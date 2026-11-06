(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import STRW_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AIMEMSET : Z := 0x65840.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.


Lemma rw_cells_recast : forall segs m A cs cs', rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | b1 :: r1, b2 :: r2 => (bv_unsigned b1 =? bv_unsigned b2) && bytes_eqb r1 r2
  | _, _ => false
  end.
Lemma bytes_eqb_sound : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|b1 r1 IH]; intros [|b2 r2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. f_equal; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition imemset_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (P C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a2' a3' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 C) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(P, P + N)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' P [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].

Section IMemset.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (P C N : Z).
  Hypothesis HP : 0 <= P /\ P + N < 2^64.
  Hypothesis HN : 0 < N.
  Hypothesis HC : 0 <= C < 2^64.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P C N m).
  #[warnings="-notation-for-abbreviation"]
  Notation ST pc mm x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 C) x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma imemset_loop : forall (K : nat) (i : Z) (m1 : word -> option byte) (bs : list byte),
    Z.to_nat (N - i) = K -> 0 <= i < N ->
    u8arr bsegs m1 P bs -> filled (Z_to_bv 8 (C mod 256)) bs (fun j => 0 <= j < i) -> length bs = Z.to_nat N ->
    mem_inv bsegs m1 -> munch [(P, P + N)] m m1 -> wmono bsegs m m1 ->
    evt bsegs POST (ST 0x65858 m1 (Z_to_bv 64 (P + N)) (Z_to_bv 64 (P + i))).
  Proof using HP HN HC.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs HK Hi ARR FIL LEN MI MU WM.
    assert (Hc : bv_unsigned (Z_to_bv 64 C : word) mod 256 = C mod 256) by (rewrite unsigned_lit by lia; reflexivity).
    mst i 1%nat ltac:(rewrite le1_byte, Hc; reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - replace (P + i + 1) with (P + (i + 1)) by lia.
      eapply (IH (Z.to_nat (N - (i + 1))) ltac:(lia) (i + 1) _ _ eq_refl ltac:(revert KK; rewrite ?unsigned_lit by lia; intros KK; lia) ARR);
        try eassumption.
      eapply filled_mono; [exact FIL|]. cbv beta. intros j Hj. lia.
    - zstep. zstep.
      pose proof (filled_all _ _ _ FIL ltac:(intros j Hj; cbv beta; revert KK; rewrite ?unsigned_lit by lia; intros KK; lia)) as E.
      rewrite LEN in E. rewrite E in ARR. apply rw_cells_of_u8arr in ARR. rewrite repeat_length in ARR.
      finish.
  Qed.

End IMemset.

(* [comment removed for export] *)
Lemma imemset_call : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (P C N : Z) (junk : list byte),
  rw_cells bsegs m P [CB (Z.to_nat N) junk] -> mem_inv bsegs m ->
  0 <= P -> P + N < 2^64 -> 0 < N -> 0 <= C < 2^64 -> Z.land (Z.lor N P) 15 <> 0 ->
  evt bsegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P C N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AIMEMSET) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros DST MI H1 H2 H3 H4 H5.
  (* [comment removed for export] *)
  unfold AIMEMSET.
  pose proof (munch_refl [(P, P + N)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
  pose proof (filled_init (Z_to_bv 8 (C mod 256)) junk) as FIL.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0.
  { exfalso. revert K0 H5. rewrite ?unsigned_lit by lia. rewrite Z.lor_comm. intros K0 AL. apply AL.
    change 15 with (Z.ones 4) in *. rewrite Z.land_ones in * by lia. lia. }
  zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
  zstep. zstep.
  pose proof (imemset_loop ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P C N ltac:(lia) H3 H4
            (Z.to_nat (N - 0)) 0 m junk eq_refl ltac:(lia) ARR) as L.
  rewrite Z.add_0_r in L. eapply L; try eassumption.
  eapply filled_mono; [exact FIL|]. cbv beta. intros j Hj. lia.
Qed.


End CeilWrap.
