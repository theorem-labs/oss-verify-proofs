(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import StrFun.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StrwF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Arr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition imemmove_entry := 0x9454c%Z.

Definition imemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at bsegs m' (bv_unsigned a1) src.

(* [comment removed for export] *)
Definition copiedR (src bs : list byte) (k : nat) : Prop := length bs = length src /\ skipn k bs = skipn k src.

Lemma copiedR_init : forall src bs, length bs = length src -> copiedR src bs (length src).
Proof. intros src bs L. split; [exact L|]. rewrite !skipn_all2 by lia. reflexivity. Qed.

Lemma copiedR_all : forall src bs, copiedR src bs 0 -> bs = src.
Proof. intros src bs [_ H]. exact H. Qed.

Lemma copiedR_step : forall src bs i x,
  copiedR src bs (S i) -> nth_error src i = Some x -> (i < length bs)%nat -> copiedR src (upd bs i x) i.
Proof.
  intros src bs i x [L K] N Hi. split; [rewrite upd_length; exact L|].
  rewrite (upd_firstn_skipn bs i x Hi).
  rewrite skipn_app, length_firstn, (Nat.min_l i (length bs)), Nat.sub_diag, skipn_all2 by (rewrite ?length_firstn; lia).
  cbn [app skipn]. rewrite K.
  destruct (nth_error_split _ _ _ N) as (pre & post & E & Hlen).
  rewrite E at 2. rewrite skipn_app, Hlen. replace (S i - i)%nat with 1%nat by lia. cbn.
  rewrite E, <- Hlen. replace (S (length pre)) with (length (pre ++ [x])) by (rewrite length_app; cbn; lia).
  rewrite skipn_all, Nat.sub_diag. cbn.
  replace (pre ++ x :: post) with ((pre ++ [x]) ++ post) by (rewrite <- app_assoc; reflexivity).
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma copied_step : forall src bs i x,
  copied src bs i -> nth_error src i = Some x -> (i < length bs)%nat -> copied src (upd bs i x) (S i).
Proof.
  intros src bs i x [L K] N Hi. split; [rewrite upd_length; exact L|].
  rewrite (upd_firstn_skipn bs i x Hi).
  rewrite firstn_app, length_firstn, (Nat.min_l i (length bs)), firstn_firstn, (Nat.min_r (S i) i) by lia.
  replace (S i - i)%nat with 1%nat by lia. cbn [firstn]. rewrite firstn_O, K.
  destruct (nth_error_split _ _ _ N) as (pre & post & E & Hlen).
  rewrite E, <- Hlen. rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
  change (pre ++ x :: post) with (pre ++ [x] ++ post). rewrite app_assoc, firstn_app, firstn_all2 by (rewrite length_app; cbn; lia).
  rewrite length_app. cbn [length]. replace (S (length pre) - (length pre + 1))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^63)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.

  Notation POST := (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at bsegs m1 S src /\ u8arr bsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
    mem_inv bsegs m1 /\ munch W m m1 /\ wmono bsegs m m1.
  (* [comment removed for export] *)
  Definition INVR (m1 : word -> option byte) (bs : list byte) (k : nat) : Prop :=
    bytes_at bsegs m1 S src /\ u8arr bsegs m1 D bs /\ copiedR src bs k /\
    mem_inv bsegs m1 /\ munch W m m1 /\ wmono bsegs m m1.

  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    | DST : u8arr _ ?m1 _ ?bs, CP : copiedR _ ?bs 0%nat |- _ =>
        let E := fresh "E" in
        pose proof (copiedR_all _ _ CP) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finish2.

  (* [comment removed for export] *)
  Lemma mr_store : forall m1 bs (i : Z) x,
    bytes_at bsegs m1 S src -> u8arr bsegs m1 D bs -> copiedR src bs (Z.to_nat (i + 1)) ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    (0 <= i < n)%Z -> nth_error src (Z.to_nat i) = Some x ->
    bytes_at bsegs (write_to_mem m1 (wa (D + i)) [x]) S src /\
    u8arr bsegs (write_to_mem m1 (wa (D + i)) [x]) D (upd bs (Z.to_nat i) x) /\
    copiedR src (upd bs (Z.to_nat i) x) (Z.to_nat i) /\
    mem_inv bsegs (write_to_mem m1 (wa (D + i)) [x]) /\ munch W m (write_to_mem m1 (wa (D + i)) [x]) /\
    wmono bsegs m (write_to_mem m1 (wa (D + i)) [x]).
  Proof.
    intros m1 bs i x SRC DST CP MI MU WM Hi N. pose proof (proj1 CP) as Lbs.
    assert (SOK : store_ok bsegs m1 (wa (D + i)) 1 = true).
    { eapply (u8arr_store_ok bsegs m1 D bs i); [exact DST | rewrite Lbs, LEN; lia | reflexivity]. }
    split; [|split; [|split; [|split; [|split]]]].
    - apply bytes_at_write_other; [exact SRC | lia | cbn; lia | rewrite LEN; cbn; lia].
    - apply (u8arr_write bsegs m1 D bs i x DST). rewrite Lbs, LEN. lia.
    - apply copiedR_step; [replace (Datatypes.S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia; exact CP | exact N | rewrite Lbs, LEN; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn; lia |]. cbn [inside length Z.of_nat Pos.of_succ_nat Pos.to_nat]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma mf_store : forall m1 bs (P : Z) x,
    bytes_at bsegs m1 S src -> u8arr bsegs m1 D bs -> copied src bs (Z.to_nat P) ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    (0 <= P < n)%Z -> nth_error src (Z.to_nat P) = Some x ->
    bytes_at bsegs (write_to_mem m1 (wa (D + P)) [x]) S src /\
    u8arr bsegs (write_to_mem m1 (wa (D + P)) [x]) D (upd bs (Z.to_nat P) x) /\
    copied src (upd bs (Z.to_nat P) x) (Z.to_nat (P + 1)) /\
    mem_inv bsegs (write_to_mem m1 (wa (D + P)) [x]) /\ munch W m (write_to_mem m1 (wa (D + P)) [x]) /\
    wmono bsegs m (write_to_mem m1 (wa (D + P)) [x]).
  Proof.
    intros m1 bs P x SRC DST CP MI MU WM HP N. pose proof (proj1 CP) as Lbs.
    assert (SOK : store_ok bsegs m1 (wa (D + P)) 1 = true).
    { eapply (u8arr_store_ok bsegs m1 D bs P); [exact DST | rewrite Lbs, LEN; lia | reflexivity]. }
    split; [|split; [|split; [|split; [|split]]]].
    - apply bytes_at_write_other; [exact SRC | lia | cbn; lia | rewrite LEN; cbn; lia].
    - apply (u8arr_write bsegs m1 D bs P x DST). rewrite Lbs, LEN. lia.
    - replace (Z.to_nat (P + 1)) with (Datatypes.S (Z.to_nat P)) by lia. apply copied_step; [exact CP | exact N | rewrite Lbs, LEN; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn; lia |]. cbn [inside length Z.of_nat Pos.of_succ_nat Pos.to_nat]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma mr_loop : forall (K : nat) m1 bs (i : Z) xa4 xa5 xa6,
    Z.to_nat (i + 1) = K -> INVR m1 bs (Z.to_nat (i + 1)) -> (0 <= i < n)%Z -> (S + n <= D)%Z ->
    evtF bsegs RNG POST (ST 0x94584 m1 a1 (Z_to_bv 64 1) (Z_to_bv 64 i) xa4 xa5 xa6).
  Proof using AB LEN SEP RS RD.
    induction K as [K IH] using lt_wf_ind; intros m1 bs i xa4 xa5 xa6 HK IV Hi HSD.
    destruct IV as (SRC & DST & CP & MI & MU & WM).
    destruct (nth_error src (Z.to_nat i)) as [x|] eqn:N; [| exfalso; apply (proj2 (nth_error_Some src (Z.to_nat i)) ltac:(rewrite LEN; lia) N)].
    pose proof (u8ro_read bsegs m1 S src i x (wa (S + i)) SRC N ltac:(lia) eq_refl) as RDx.
    zstep. zstep. clear RDx. zstep. zstep. zstep.                   (* [comment removed for export] *)
    pose proof (u8arr_store_ok bsegs m1 D bs i (wa (D + i)) DST ltac:(rewrite (proj1 CP), LEN; lia) eq_refl) as SOK.
    zstep.                                                          (* [comment removed for export] *)
    change (Z_to_bv 64 (bv_unsigned x)) with (zxb x). rewrite (le1_zxb x). change (Z_to_bv 64 (D + i)) with (wa (D + i)).
    destruct (mr_store m1 bs i x SRC DST CP MI MU WM ltac:(lia) N) as (SRC2 & DST2 & CP2 & MI2 & MU2 & WM2).
    clear SRC DST CP MI MU WM SOK.
    remember (write_to_mem m1 (wa (D + i)) [x]) as m2 eqn:Hm2. clear Hm2.
    zstep. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
    - replace (Z_to_bv 64 (i + -1)) with (Z_to_bv 64 (i - 1)) by (f_equal; lia).
      eapply (IH (Z.to_nat (i - 1 + 1)) ltac:(lia) m2 _ (i - 1)%Z); [reflexivity | | lia | lia].
      replace (Z.to_nat (i - 1 + 1)) with (Z.to_nat i) by lia.
      split; [exact SRC2|]. split; [exact DST2|]. split; [exact CP2|]. split; [exact MI2|]. split; [exact MU2| exact WM2].
    - rename SRC2 into SRC. rename DST2 into DST. rename CP2 into CP. rename MI2 into MI. rename MU2 into MU. rename WM2 into WM.
      replace (Z.to_nat i) with 0%nat in CP, DST by lia.
      zstep. fin.                                                   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma mf_loop : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 xa5 xa6,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z -> (D + n <= S)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (D + n) -> xa3 = Z_to_bv 64 (D + P) ->
    evtF bsegs RNG POST (ST 0x9455c m1 xa1 xa2 xa3 xa4 xa5 xa6).
  Proof using AB LEN SEP RS RD.
    induction K as [K IH] using lt_wf_ind; intros m1 bs P xa1 xa2 xa3 xa4 xa5 xa6 HK IV HP HDS -> -> ->.
    destruct IV as (SRC & DST & CP & MI & MU & WM).
    destruct (nth_error src (Z.to_nat P)) as [x|] eqn:N; [| exfalso; apply (proj2 (nth_error_Some src (Z.to_nat P)) ltac:(rewrite LEN; lia) N)].
    pose proof (u8ro_read bsegs m1 S src P x (wa (S + P)) SRC N ltac:(lia) eq_refl) as RDx.
    zstep. clear RDx.                                               (* [comment removed for export] *)
    pose proof (u8arr_store_ok bsegs m1 D bs P (wa (D + P)) DST ltac:(rewrite (proj1 CP), LEN; lia) eq_refl) as SOK.
    zstep.                                                          (* [comment removed for export] *)
    change (Z_to_bv 64 (bv_unsigned x)) with (zxb x). rewrite (le1_zxb x). change (Z_to_bv 64 (D + P)) with (wa (D + P)).
    destruct (mf_store m1 bs P x SRC DST CP MI MU WM ltac:(lia) N) as (SRC2 & DST2 & CP2 & MI2 & MU2 & WM2).
    clear SRC DST CP MI MU WM SOK.
    remember (write_to_mem m1 (wa (D + P)) [x]) as m2 eqn:Hm2. clear Hm2.
    zstep. zstep.                                                   (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
    - replace (Z_to_bv 64 (D + P + 1)) with (Z_to_bv 64 (D + (P + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (S + P + 1)) with (Z_to_bv 64 (S + (P + 1))) by (f_equal; lia).
      eapply (IH (Z.to_nat (n - (P + 1))) ltac:(lia) m2 _ (P + 1)%Z); [reflexivity | | lia | lia | reflexivity | reflexivity | reflexivity].
      split; [exact SRC2|]. split; [exact DST2|]. split; [exact CP2|]. split; [exact MI2|]. split; [exact MU2| exact WM2].
    - rename SRC2 into SRC. rename DST2 into DST. rename CP2 into CP. rename MI2 into MI. rename MU2 into MU. rename WM2 into WM.
      zstep. zstep. fin.                                            (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma imemmove_body : forall junk,
    rw_cells bsegs m D [CB (Z.to_nat n) junk] -> bytes_at bsegs m S src -> mem_inv bsegs m ->
    evtF bsegs RNG POST (ST 0x9454c m a1 a2 a3 a4 a5 a6).
  Proof using AB LEN SEP RS RD.
    intros junk DST0 SRC MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST0) as Ljunk.
    zstep. if_cases Kds; zify_cond Kds.                             (* [comment removed for export] *)
    - zstep. if_cases Kss; zify_cond Kss.                           (* [comment removed for export] *)
      + assert (n = 0)%Z by lia. zstep.
        pose proof (copied_0 src junk ltac:(lia)) as CP.
        pose proof (copied_all _ _ _ CP ltac:(rewrite LEN; lia)) as E. rewrite E in DST.
        apply rw_cells_of_u8arr in DST. rewrite LEN in DST. finish2.
      + zstep. if_cases Kn; zify_cond Kn.                         (* [comment removed for export] *)
        * assert (n = 0)%Z by lia. zstep.
          pose proof (copied_0 src junk ltac:(lia)) as CP.
          pose proof (copied_all _ _ _ CP ltac:(rewrite LEN; lia)) as E. rewrite E in DST.
          apply rw_cells_of_u8arr in DST. rewrite LEN in DST. finish2.
        * zstep. zstep.                                             (* [comment removed for export] *)
          replace (Z_to_bv 64 (n + -1)) with (Z_to_bv 64 (n - 1)) by (f_equal; lia).
          eapply (mr_loop (Z.to_nat (n - 1 + 1)) m junk (n - 1)%Z); [reflexivity | | lia | lia].
          split; [exact SRC|]. split; [exact DST|]. split; [| split; [exact MI|]; split; [exact MU| exact WM]].
          replace (Z.to_nat (n - 1 + 1)) with (length src) by lia. apply copiedR_init. lia.
    - zstep. if_cases Kn; zify_cond Kn.                             (* [comment removed for export] *)
      + assert (n = 0)%Z by lia. zstep.
        pose proof (copied_0 src junk ltac:(lia)) as CP.
        pose proof (copied_all _ _ _ CP ltac:(rewrite LEN; lia)) as E. rewrite E in DST.
        apply rw_cells_of_u8arr in DST. rewrite LEN in DST. finish2.
      + zstep. zstep.                                               (* [comment removed for export] *)
        eapply (mf_loop (Z.to_nat (n - 0)) m junk 0%Z); [reflexivity | | lia | lia | | reflexivity |].
        2, 3: rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned.
        split; [exact SRC|]. split; [exact DST|]. split; [| split; [exact MI|]; split; [exact MU| exact WM]].
        change (Z.to_nat 0) with 0%nat. apply copied_0. lia.
  Qed.
End Proofs.

Lemma imemmove_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at bsegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  (bv_unsigned a2 < 2^63)%Z ->
  mem_inv bsegs m ->
  rng RNG (bv_unsigned a1) (bv_unsigned a2) ->
  rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  evtF bsegs RNG (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9454c) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP N63 MI RS RD.
  eapply imemmove_body; try eassumption.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End CANSEC1.
