(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs F_memchr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition sgt_entry := 0x14bc0%Z.
Definition SEPTAB : Z := 0x10525.
Definition JTAB : Z := 0x10874.
Ltac sstep := step; fix_lit_store.

Definition sep20 : list byte := map (Z_to_bv 8) [32; 9; 40; 41; 60; 62; 64; 44; 59; 58; 92; 34; 47; 91; 93; 63; 61; 123; 125; 0]%Z.
Lemma sep_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m SEPTAB sep20.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m SEPTAB sep20 MI ltac:(vm_compute; reflexivity) ltac:(unfold SEPTAB; lia) ltac:(unfold SEPTAB; cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma memchr_ok_sep : forall A c, memchr_ok A c 20 sep20.
Proof. intros A c. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat 20) sep20)); cbn; lia. Qed.
Lemma memchr_res_small : forall A c n buf, (0 <= A)%Z -> (0 <= memchr_res A c n buf <= A + Z.of_nat (length buf))%Z.
Proof.
  intros A c n buf HA. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (L & _ & _). rewrite firstn_length in L. lia.
Qed.

Definition sgt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S T TY MB A cur len : Z) (bs : list byte) (tyw : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r cur' : Z) (tb tl : word) (tyw' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 96) (bv_unsigned sp)
    /\ rw_cells rsegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
    /\ rw_cells rsegs m' T [C8 tb; C8 tl]
    /\ rw_cells rsegs m' TY [C4 tyw']
    /\ ( (exists tlz ty, r = PARSE_OK /\ tb = wz (A + cur) /\ tl = wz tlz /\ tyw' = wz ty
             /\ 1 <= tlz /\ cur' = cur + tlz /\ cur' <= len /\ 0 <= ty <= 5
             /\ ((ty = TT_IDENTIFIER \/ ty = TT_WHITESPACE) -> cur' < len)
             /\ (ty = TT_CRLF -> exists b, nth_error bs (Z.to_nat cur) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10))
             /\ (ty = TT_CRLF -> tlz <= 2))
       \/ ((r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) /\ cur' = cur /\ tyw' = tyw) )%Z.

Definition sgt_stmt : Prop :=
  forall (S T TY MB A cur len cap : Z) (bs : list byte) (tw1 tw2 tyw : word)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] ->
  rw_cells rsegs m MB (mbuf_cells A len cap) ->
  bytes_at rsegs m A bs -> (Z.of_nat (length bs) >= len)%Z -> (0 <= cur <= len)%Z -> (len <= cap)%Z -> (A + cap + 1 < 2^63)%Z ->
  rw_cells rsegs m T [C8 tw1; C8 tw2] ->
  rw_cells rsegs m TY [C4 tyw] ->
  stk rsegs m (bv_unsigned sp - 96) (bv_unsigned sp) -> (256 <= bv_unsigned sp)%Z ->

  (A + Z.of_nat (length bs) <= bv_unsigned sp - 96)%Z -> (0 < A \/ (A = 0 /\ len = 0))%Z ->
  (bv_unsigned sp <= T)%Z -> (bv_unsigned sp <= TY)%Z -> (T + 16 <= TY \/ TY + 4 <= T)%Z ->
  (T + 16 <= MB)%Z -> (TY + 4 <= MB)%Z -> (MB + 32 <= S)%Z -> (S + 24 < 2^63)%Z ->
  mem_inv rsegs m -> a0 = wz S -> a1 = wz T -> a2 = wz TY ->
  evt rsegs (sgt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S T TY MB A cur len bs tyw m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz sgt_entry) fc None m (seg_rom rsegs)).

Definition jt104 : list byte := map (Z_to_bv 8)
  [252; 67; 0; 0; 204; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 216; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0;
   160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0;
   160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0; 160; 68; 0; 0;
   160; 68; 0; 0; 160; 68; 0; 0; 252; 67; 0; 0; 160; 68; 0; 0; 4; 69; 0; 0]%Z.

Definition jt_off (c : Z) : Z :=
  if ((c =? 9) || (c =? 32))%Z%bool then 17404 else if (c =? 10)%Z then 17612 else if (c =? 13)%Z then 17624
  else if (c =? 34)%Z then 17668 else 17568.
Lemma jt_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m JTAB jt104.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m JTAB jt104 MI ltac:(vm_compute; reflexivity) ltac:(unfold JTAB; lia) ltac:(unfold JTAB; cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1', b :: l2' => bv_eqb a b && bytes_eqb l1' l2'
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply bv_eqb_eq in H1. subst. f_equal. apply IH. exact H2.
Qed.
Lemma jt_entry : forall j : nat, (j < 26)%nat ->
  firstn 4 (skipn (4 * j) jt104) = le4 (Z_to_bv 64 (jt_off (Z.of_nat j + 9))).
Proof.
  intros j Hj. apply bytes_eqb_eq.
  do 26 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma jt_read : forall m c, mem_inv rsegs m -> (9 <= c <= 34)%Z ->
  ov_read_bytes rsegs m (wa (JTAB + 4 * (c - 9))) 4 = Some (le4 (Z_to_bv 64 (jt_off c))).
Proof.
  intros m c MI Hc. pose proof (jt_bytes m MI) as B.
  rewrite (bytes_at_read rsegs m JTAB jt104 (4 * (c - 9)) 4 B) by (cbn; lia).
  replace (Z.to_nat (4 * (c - 9))) with (4 * Z.to_nat (c - 9))%nat by lia.
  rewrite jt_entry by lia. repeat f_equal. lia.
Qed.

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (S T TY MB A cur len cap : Z) (bs : list byte) (tw1 tw2 tyw : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis SPR : (256 <= bv_unsigned sp /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis LBS : (Z.of_nat (length bs) >= len)%Z.
  Hypothesis CUR : (0 <= cur <= len)%Z.
  Hypothesis CAP : (len <= cap)%Z.
  Hypothesis AHI : (A + cap + 1 < 2^63)%Z.
  Hypothesis BLO : (A + Z.of_nat (length bs) <= bv_unsigned sp - 96)%Z.
  Hypothesis ANZ : (0 < A \/ (A = 0 /\ len = 0))%Z.
  Hypothesis LT : (bv_unsigned sp <= T)%Z.
  Hypothesis LTY : (bv_unsigned sp <= TY)%Z.
  Hypothesis TTY : (T + 16 <= TY \/ TY + 4 <= T)%Z.
  Hypothesis TMB : (T + 16 <= MB)%Z.
  Hypothesis TYMB : (TY + 4 <= MB)%Z.
  Hypothesis MBS : (MB + 32 <= S)%Z.
  Hypothesis SHI : (S + 24 < 2^63)%Z.

  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Notation POST := (sgt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S T TY MB A cur len bs tyw m0).

  Definition minv (m : mem) (tc1 tc2 : word) : Prop :=
    (exists j8, rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk rsegs m (bv_unsigned sp + -96) (bv_unsigned sp + -96)
    /\ rw_cells rsegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)]
    /\ rw_cells rsegs m MB [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)]
    /\ bytes_at rsegs m A bs
    /\ rw_cells rsegs m T [C8 tc1; C8 tc2]
    /\ rw_cells rsegs m TY [C4 tyw]
    /\ mem_inv rsegs m
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z m0 m
    /\ wmono rsegs m0 m.

  Notation LST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 x31 mm :=
    (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 TY) (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 T) x19 (Z_to_bv 64 cur) x21 (Z_to_bv 64 (A + len)) x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  #[using="Type"] Lemma ret_err : forall (r : Z) x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 tc1 tc2 m,
    minv m tc1 tc2 -> (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x14e5c) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HR.
    do 13 step.
    release_frame FR ST (bv_unsigned sp).
    unfold sgt_post. finish. 1: exact SC. 1: exact TC. 1: exact TYC. right. split; [exact HR| split; reflexivity].
  Qed.

  #[using="BLO LT LTY TTY TMB TYMB MBS SHI"] Lemma ret_ok : forall (tlz ty : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 x31 m,
    minv m (wz (A + cur)) (wz tlz) ->
    (1 <= tlz)%Z -> (cur + tlz <= len)%Z -> (0 <= ty <= 5)%Z ->
    ((ty = 0 \/ ty = 1) -> cur + tlz < len)%Z ->
    (ty = 2 -> exists b, nth_error bs (Z.to_nat cur) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10))%Z ->
    (ty = 2 -> tlz <= 2)%Z ->
    evt rsegs POST (LST 0x14e4c x1 x5 x6 x7 (Z_to_bv 64 tlz) (Z_to_bv 64 ty) x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) TL1 TL2 TYR STRICT CRB CRL.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. sstep. sstep. do 14 step.
    release_frame FR ST (bv_unsigned sp).
    unfold sgt_post. finish. 1: exact SC. 1: exact TC. 1: exact TYC.
    left. exists tlz, ty. repeat (split; [first [reflexivity| lia]|]).
    split. { intros Hty; unfold TT_IDENTIFIER, TT_WHITESPACE in Hty; specialize (STRICT Hty); lia. }
    unfold TT_CRLF. split; [exact CRB| exact CRL].
  Qed.

  #[using="bs"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma ws_end : forall (i : Z) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31 tc2 m,
    minv m (wz (A + cur)) tc2 -> (cur < i <= len)%Z ->
    evt rsegs POST (LST 0x14dec x1 x5 x6 x7 x10 (Z_to_bv 64 (A + i)) x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (A + cur)) x23 x24 x25 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros MV HI. pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. if_cases K0; zify_cond K0. { exfalso. apply K0. vm_compute. reflexivity. }
    zstep. zstep. if_cases K1; zify_cond K1.
    -   apply (ret_err 1) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| left; reflexivity].
    - zstep. sstep. zstep. zstep.
      replace (A + i - (A + cur))%Z with (i - cur)%Z in * by lia.
      apply (ret_ok (i - cur) 1); try lia.
      split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="LBS"] Lemma nth_bs : forall i, (0 <= i < len)%Z -> exists b, nth_error bs (Z.to_nat i) = Some b.
  Proof.
    intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma ws_loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x19 x24 x25 x28 x29 x30 x31 tc2 m,
    (len - i < Z.of_nat k)%Z -> (cur < i < len)%Z -> minv m (wz (A + cur)) tc2 ->
    evt rsegs POST (LST 0x14c9c x1 x5 x6 x7 (Z_to_bv 64 32) (Z_to_bv 64 (A + i)) (Z_to_bv 64 9) x13 x14 x15 x16 x17 x19
                        (Z_to_bv 64 (A + cur)) (Z_to_bv 64 (len - i)) x24 x25 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK HI MV; [lia|].
    pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    destruct (nth_bs i ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs m A bs i b (Z_to_bv 64 (A + i)) BUF Hb ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K1; zify_cond K1.
    -   zstep. zstep. zstep. if_cases K2; zify_cond K2.
      +   zstep. apply (ws_end len) with (tc2 := tc2); [exact MV| lia].
      + replace (len - i + -1)%Z with (len - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z) with (tc2 := tc2); [lia| lia| exact MV].
    - zstep. if_cases K3; zify_cond K3.
      +   zstep. zstep. zstep. if_cases K2; zify_cond K2.
        * zstep. apply (ws_end len) with (tc2 := tc2); [exact MV| lia].
        * replace (len - i + -1)%Z with (len - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
          apply (IH (i + 1)%Z) with (tc2 := tc2); [lia| lia| exact MV].
      +   zstep. apply (ws_end i) with (tc2 := tc2); [exact MV| lia].
  Qed.

  #[using="bs"] Lemma neg_neg_mod : forall n, (0 < n < 2^64)%Z -> Z_to_bv 64 (0 - (- n) mod 18446744073709551616)%Z = Z_to_bv 64 n.
  Proof.
    intros n Hn. apply Z_to_bv_eqm. change 18446744073709551616%Z with (2^64)%Z.
    rewrite <- (Z.mod_add (-n) 1 (2^64)) by lia. rewrite (Z.mod_small (-n + 1 * 2^64)) by lia.
    rewrite <- (Z.mod_add _ 1 (2^64)) by lia. f_equal. lia.
  Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma ident_end : forall (n : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x28 x29 x30 x31 tc2 m,
    minv m (wz (A + cur)) tc2 -> (1 <= n <= len - cur)%Z ->
    evt rsegs POST (LST 0x14cf0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (- n)) (Z_to_bv 64 len) x24 x25 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros MV HN. pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. if_cases K0; zify_cond K0. { exfalso. apply K0. vm_compute. reflexivity. }
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    -   apply (ret_err 1) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| left; reflexivity].
    - assert (NE : n <> (len - cur)%Z). { intros E. apply K1. subst n. f_equal. lia. }
      zstep. zstep. rewrite neg_neg_mod by lia. sstep. zstep.
      apply (ret_ok n 0); try lia.
      split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma ident_loop : forall (k : nat) (n : Z) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 tc2 m,
    (len - cur - n < Z.of_nat k)%Z -> (1 <= n <= len - cur)%Z -> minv m (wz (A + cur)) tc2 ->
    evt rsegs POST (LST 0x14cc4 x1 x5 x6 x7 x10 (Z_to_bv 64 (- n)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 SEPTAB) x21
                        (Z_to_bv 64 len) (Z_to_bv 64 (A + cur + n)) (Z_to_bv 64 94) x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK HN MV; [lia|].
    pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. if_cases K1; zify_cond K1.
    -   apply (ident_end n) with (tc2 := tc2); [exact MV| lia].
    - destruct (nth_bs (cur + n) ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
      pose proof (u8ro_read rsegs m A bs (cur + n) b (Z_to_bv 64 (A + cur + n)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      +   apply (ident_end n) with (tc2 := tc2); [exact MV| lia].
      + zstep. zstep. unfold SEPTAB at 2. zstep.
        call memchr_spec.
        all: side (rewrite ?unsigned_lit by (unfold SEPTAB; lia); first [apply sep_bytes; exact MI | apply memchr_ok_sep | exact MI]).
        clear MV RD. rename MI0 into MI.
        assert (MV : minv x25 (wz (A + cur)) tc2).
        { split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption. }
        rewrite !unsigned_lit by lia.
        pose proof (memchr_res_small 66853 (bv_unsigned b mod 256) 20 sep20 ltac:(lia)) as MR. cbn [length sep20 map] in MR.
        zstep. zstep. zstep. if_cases K3; zify_cond K3.
        *
          replace (A + cur + n + 1)%Z with (A + cur + (n + 1))%Z by lia.
          replace (- n + -1)%Z with (- (n + 1))%Z by lia.
          apply (IH (n + 1)%Z) with (tc2 := tc2); [lia| lia| exact MV].
        * apply (ident_end n) with (tc2 := tc2); [exact MV| lia].
  Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma quote_loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x17 x19 x23 x24 x25 x28 x29 x30 x31 tc2 m,
    (len - i < Z.of_nat k)%Z -> (cur < i < len)%Z -> minv m (wz (A + cur)) tc2 ->
    evt rsegs POST (LST 0x14dac x1 x5 x6 x7 (Z_to_bv 64 (A + i)) (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 127)
                        (Z_to_bv 64 13) (Z_to_bv 64 9728) x17 x19 (Z_to_bv 64 (A + cur)) x23 x24 x25 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK HI MV; [lia|].
    pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    destruct (nth_bs i ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs m A bs i b (Z_to_bv 64 (A + i)) BUF Hb ltac:(lia) eq_refl) as RD.

    assert (CONT : forall (i' : Z) y1 y5 y6 y7 y10 y19 y23 y24 y25 y28 y29 y30 y31,
      (i < i' <= len)%Z ->
      evt rsegs POST (LST 0x14da4 y1 y5 y6 y7 y10 (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 127)
                          (Z_to_bv 64 13) (Z_to_bv 64 9728) (Z_to_bv 64 (A + i')) y19 (Z_to_bv 64 (A + cur)) y23 y24 y25 y28 y29 y30 y31 m)).
    { intros until y31. intros HI'. zstep. zstep. if_cases KC; zify_cond KC.
      - zstep. zstep. apply (ret_err 1) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| left; reflexivity].
      - apply (IH i') with (tc2 := tc2); [lia| lia| exact MV]. }
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    -   zstep. if_cases K2; zify_cond K2.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
      + zstep. zstep. replace (A + i + 2)%Z with (A + (i + 2))%Z by lia. apply CONT. lia.
    - zstep. if_cases K3; zify_cond K3.
      +   zstep. sstep. zstep.
        replace (A + i + 1 - (A + cur))%Z with (i + 1 - cur)%Z in * by lia.
        apply (ret_ok (i + 1 - cur) 5); try lia.
        split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
      + zstep. if_cases K4; zify_cond K4.
        *   zstep. zstep. if_cases K5; zify_cond K5.
          -- apply (ret_err 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
          -- zstep. zstep. zstep. if_cases K6; zify_cond K6.
             ++ replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
             ++ zstep. apply (ret_err 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
        * zstep. if_cases K7; zify_cond K7.
          --   replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
          --   zstep. zstep. if_cases K8; zify_cond K8.
             ++ apply (ret_err 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
             ++ zstep. zstep. zstep. if_cases K9; zify_cond K9.
                ** replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. apply CONT. lia.
                ** zstep. apply (ret_err 3) with (tc1 := wz (A + cur)) (tc2 := tc2); [exact MV| right; reflexivity].
  Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma ident_start : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x28 x29 x30 x31 m,
    minv m tw1 tw2 -> (cur < len)%Z ->
    evt rsegs POST (LST 0x14cac x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (A + cur)) (Z_to_bv 64 len) x24 x25 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM) HC.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    sstep. zstep. zstep. zstep. zstep. zstep.
    apply (ident_loop (Datatypes.S (Z.to_nat (len - cur))) 1) with (tc2 := tw2); [lia| lia|].
    split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption.
  Qed.

  Ltac mv_tac FR := split; [eexists; exact FR|]; repeat (split; [assumption|]); assumption.

  #[using="BLO LT LTY TTY TMB TYMB MBS SHI"] Lemma default_blk : forall (c : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31 m,
    minv m tw1 tw2 -> (cur < len)%Z -> (0 <= c < 256)%Z ->
    evt rsegs POST (LST 0x14d14 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c) (Z_to_bv 64 (A + cur)) x23 x24 x25 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros MV HC Hc. pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. zstep. zstep. zstep.
    call memchr_spec.
    all: side (rewrite ?unsigned_lit by (unfold SEPTAB; lia); first [apply sep_bytes; exact MI | apply memchr_ok_sep | exact MI]).
    clear MV. rename MI0 into MI. rewrite !unsigned_lit by lia.
    pose proof (memchr_res_small 66853 (c mod 256) 20 sep20 ltac:(lia)) as MR. cbn [length sep20 map] in MR.
    zstep. if_cases K1; zify_cond K1.
    -   zstep. zstep. if_cases K2; zify_cond K2.
      +   zstep. sstep. sstep. zstep. zstep. apply (ret_ok 1 3); try lia. mv_tac FR.
      + zstep. zstep. if_cases K3; zify_cond K3.
        *   zstep. sstep. sstep. zstep. zstep. apply (ret_ok 1 3); try lia. mv_tac FR.
        *   zstep. zstep. apply (ret_err 3) with (tc1 := tw1) (tc2 := tw2); [mv_tac FR| right; reflexivity].
    -   zstep. sstep. sstep. zstep. zstep. apply (ret_ok 1 4); try lia. mv_tac FR.
  Qed.

  #[using="LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma dispatch : forall (c : Z) (b0 : byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 m,
    minv m tw1 tw2 -> (cur < len)%Z -> (0 <= c < 256)%Z -> nth_error bs (Z.to_nat cur) = Some b0 -> c = bv_unsigned b0 ->
    evt rsegs POST (LST 0x14c48 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c) (Z_to_bv 64 (A + cur)) (Z_to_bv 64 len) x24 x25 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros MV HC Hc Hb0 Hcb. pose proof MV as ([j8 FR] & ST & SC & MBC & BUF & TC & TYC & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. zstep. if_cases KR; zify_cond KR.
    -   apply default_blk; [exact MV| lia| lia].
    -
      assert (CR : (9 <= c <= 34)%Z).
      { destruct (Z.lt_ge_cases c 9); [|lia]. exfalso. revert KR.
        rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
      pose proof (jt_read m c MI CR) as RD.
      replace (wa (JTAB + 4 * (c - 9))) with (Z_to_bv 64 (Z.shiftl (c + -9) 2 + 67700))%Z in RD
        by (unfold wa, JTAB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep. zstep. zstep. zstep.
      assert (CASES : ((jt_off c = 17404 /\ (c = 9 \/ c = 32)) \/ (jt_off c = 17612 /\ c = 10) \/ (jt_off c = 17624 /\ c = 13)
                      \/ (jt_off c = 17668 /\ c = 34) \/ (jt_off c = 17568 /\ c <> 9 /\ c <> 32 /\ c <> 10 /\ c <> 13 /\ c <> 34))%Z).
      { unfold jt_off. destruct (Z.eqb_spec c 9); [subst; cbn; lia|]. destruct (Z.eqb_spec c 32); [subst; cbn; lia|]. cbn [orb].
        destruct (Z.eqb_spec c 10); [lia|]. destruct (Z.eqb_spec c 13); [lia|]. destruct (Z.eqb_spec c 34); lia. }
      destruct CASES as [[E Hc9]|[[E Hc10]|[[E Hc13]|[[E Hc34]|[E Hoth]]]]]; rewrite E; rewrite sx32_lit by lia; zstep; zstep.
      +
        zstep. sstep. zstep. if_cases K1; zify_cond K1.
        * replace (A + cur + 1)%Z with (A + (cur + 1))%Z by lia. apply (ws_end (cur + 1)) with (tc2 := tw2); [mv_tac FR| lia].
        * zstep. zstep. zstep. zstep. zstep.
          replace (Z_to_bv 64 (Z.lxor cur 18446744073709551615 + len)) with (Z_to_bv 64 (len - (cur + 1)))%Z.
          2:{ apply Z_to_bv_eqm. rewrite zb_lxor_ones by lia. change 18446744073709551615%Z with (2^64 - 1)%Z.
              rewrite <- (Z.mod_add (len - (cur + 1)) 1 (2^64)) by lia. f_equal. lia. }
          replace (A + cur + 1)%Z with (A + (cur + 1))%Z by lia.
          apply (ws_loop (Datatypes.S (Z.to_nat (len - cur))) (cur + 1)) with (tc2 := tw2); [lia| lia| mv_tac FR].
      +   zstep. sstep. zstep. sstep. zstep. zstep. apply (ret_ok 1 2); try lia. mv_tac FR. intros _; exists b0; split; [exact Hb0| lia].
      +   zstep. sstep. zstep. zstep. if_cases K1; zify_cond K1.
        * apply (ret_err 1) with (tc1 := wz (A + cur)) (tc2 := tw2); [mv_tac FR| left; reflexivity].
        * destruct (nth_bs (cur + 1) ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
          pose proof (u8ro_read rsegs _ A bs (cur + 1) b1 (Z_to_bv 64 (A + cur + 1)) BUF Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
          zstep. zstep. zstep. if_cases K2; zify_cond K2.
          -- zstep. zstep. sstep. zstep. zstep. apply (ret_ok 1 3); try lia. mv_tac FR.
          -- zstep. sstep. zstep. zstep. apply (ret_ok 2 2); try lia. mv_tac FR. intros _; exists b0; split; [exact Hb0| lia].
      +   zstep. sstep. zstep. if_cases K1; zify_cond K1.
        * zstep. zstep. apply (ret_err 1) with (tc1 := wz (A + cur)) (tc2 := tw2); [mv_tac FR| left; reflexivity].
        * do 8 zstep. replace (A + cur + 1)%Z with (A + (cur + 1))%Z by lia.
          apply (quote_loop (Datatypes.S (Z.to_nat (len - cur))) (cur + 1)) with (tc2 := tw2); [lia| lia| mv_tac FR].
      +   apply default_blk; [exact MV| lia| lia].
  Qed.

  #[using="SPR LBS CUR BLO ANZ LT LTY TTY TMB TYMB MBS SHI"] Lemma body : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    rw_cells rsegs m0 S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] ->
    rw_cells rsegs m0 MB [C8 (wz A); C8 (wz len); C8 (wz cap); C8 (wz 5)] ->
    bytes_at rsegs m0 A bs -> rw_cells rsegs m0 T [C8 tw1; C8 tw2] -> rw_cells rsegs m0 TY [C4 tyw] ->
    stk rsegs m0 (bv_unsigned sp - 96) (bv_unsigned sp) -> mem_inv rsegs m0 ->
    evt rsegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 T) (Z_to_bv 64 TY) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 sgt_entry) fc None m0 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SC MBC BUF TC TYC ST MI. unfold sgt_entry.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z m0) as MU.
    pose proof (wmono_refl rsegs m0) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    pose proof (rw_cells_bound rsegs _ _ _ MBC) as MBB. cbn [cells_size csize Nat.add] in MBB.
    carve_frame 96%nat ST.
    do 12 sstep.
    zstep. zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
    2:{   zstep. zstep.
        apply (ret_err 1) with (tc1 := tw1) (tc2 := tw2); [| left; reflexivity].
        split; [eexists; exact FR|]. repeat (split; [assumption|]). assumption. }
    assert (HC : (cur < len)%Z) by lia.
    destruct (nth_bs cur ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0.
    zstep. zstep. zstep. zstep.
    pose proof (u8ro_read rsegs _ A bs cur b0 (Z_to_bv 64 (A + cur)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
    zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - apply (dispatch (bv_unsigned b0) b0); [mv_tac FR| lia| lia| exact Hb0| reflexivity].
    - zstep. zstep. zstep. zstep. zstep.
      call memchr_spec.
      all: side (rewrite ?unsigned_lit by (unfold SEPTAB; lia); first [apply sep_bytes; exact MI | apply memchr_ok_sep | exact MI]).
      rename MI0 into MI. rewrite !unsigned_lit by lia.
      pose proof (memchr_res_small 66853 (bv_unsigned b0 mod 256) 20 sep20 ltac:(lia)) as MR. cbn [length sep20 map] in MR.
      zstep. if_cases K2; zify_cond K2.
      + apply ident_start; [mv_tac FR| lia].
      + apply (dispatch (bv_unsigned b0) b0); [mv_tac FR| lia| lia| exact Hb0| reflexivity].
  Qed.
End WALK.

Lemma scanner_get_token_spec : sgt_stmt.
Proof.
  unfold sgt_stmt. intros until m.
  intros SC MBC BUF LBS CUR CAP AHI TC TYC ST SPLO BLO ANZ LT LTY TTY TMB TYMB MBS SHI MI -> -> ->.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC.
  eapply body; eauto. pose proof (word_lt64 sp). lia.
Qed.
