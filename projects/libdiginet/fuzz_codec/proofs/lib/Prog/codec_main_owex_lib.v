From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_agree codec_main_inv.
Import ListNotations.
Open Scope Z_scope.

(** Facts for the segment OWE11 (SYSEX) of the walk of LLVMFuzzerTestOneInput in the plain image: the
    seven_bit loop over k.bytes[0..n) at 0x14944-0x14960. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- list and byte facts ---- *)

Lemma sx_firstn_S_nth : forall (A : Type) (l : list A) j d, (j < length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  intros A l. induction l as [|x l IH]; intros j d H; cbn in H; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH j d) by lia. reflexivity.
Qed.

Lemma sx_seven_bit_snoc : forall l x, seven_bit (l ++ [x]) = seven_bit l && negb (Z.testbit x 7).
Proof. intros l x. unfold seven_bit. rewrite forallb_app. cbn [forallb]. rewrite andb_true_r. reflexivity. Qed.

Lemma sx_in_nth_firstn : forall (l : list Z) j n d, (j < n)%nat -> (j < length l)%nat -> In (nth j l d) (firstn n l).
Proof.
  induction l as [|x l IH]; intros j n d Hn Hl; cbn in Hl; [lia|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; cbn [firstn nth]; [left; reflexivity | right; apply IH; lia].
Qed.

Lemma sx_seven_bit_bad : forall l j n, (j < n)%nat -> (j < length l)%nat -> Z.testbit (nth j l 0) 7 = true ->
  seven_bit (firstn n l) = false.
Proof.
  intros l j n Hj Hl Ht. destruct (seven_bit (firstn n l)) eqn:E; [|reflexivity].
  unfold seven_bit in E. rewrite forallb_forall in E. specialize (E _ (sx_in_nth_firstn l j n 0 Hj Hl)).
  rewrite Ht in E. discriminate E.
Qed.

Lemma sx_zb_nth : forall l j, nth j (zb l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. intros l j. exact (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j). Qed.

Lemma sx_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

(** bltz of an lb: bit 7 of the byte. *)
Lemma sxb_lts0 : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = Z.testbit (bv_unsigned b) 7.
Proof.
  intros b. rewrite bv_lts_zero_r. unfold sxb. pose proof (sx_byte_range b) as Hb.
  rewrite tb7_byte by lia. rewrite unsigned_lit_wrap.
  unfold bv_signed, bv_swrap, bv_wrap.
  replace (bv_half_modulus 8) with 128 by reflexivity. replace (bv_modulus 8) with 256 by reflexivity.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808.
  remember (bv_unsigned b) as u eqn:Eu. clear Eu.
  destruct (Z.ltb_spec 127 u) as [H|H].
  - rewrite <- (Z.mod_unique (u + 128) 256 1 (u - 128)) by lia.
    rewrite <- (Z.mod_unique (u - 128 - 128) 18446744073709551616 (-1) (u - 256 + 18446744073709551616)) by lia.
    apply Z.leb_le. lia.
  - rewrite (Z.mod_small (u + 128) 256) by lia.
    rewrite (Z.mod_small (u + 128 - 128) 18446744073709551616) by lia.
    apply Z.leb_gt. lia.
Qed.

(** ---- the loop 0x14950-0x14960: lb a3, 0(a1); bltz a3 -> 0x14800; a2 -= 1; a1 += 1; bnez a2 ---- *)

Lemma sysex_loop : forall (Q : machine_state -> Prop) F fc m ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (B : Z) (N : nat) (l : list byte),
  bytes_at rsegs m B l -> (N <= length l)%nat -> 0 <= B -> B + Z.of_nat (length l) < 2 ^ 64 ->
  (seven_bit (firstn N (zb l)) = false -> forall a1' a2' a3',
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x14800) fc None m (seg_rom rsegs))) ->
  (seven_bit (firstn N (zb l)) = true -> forall a1' a2' a3',
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x14964) fc None m (seg_rom rsegs))) ->
  forall (d j : nat) (a1v a2v a3v : word), d = (N - j)%nat -> (j < N)%nat ->
    bv_unsigned a1v = B + Z.of_nat j -> bv_unsigned a2v = Z.of_nat (N - j) ->
    seven_bit (firstn j (zb l)) = true ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1v a2v a3v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         t3 t4 t5 t6) F (Z_to_bv 64 0x14950) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 B N l
         BY HN HB HBL KR KS d.
  induction d as [|d IH]; intros j a1v a2v a3v Hd Hj HA1 HA2 H7; [lia|].
  pose proof (bytes_at_byte m B l (Z.of_nat j) BY ltac:(lia)) as HR.
  rewrite Nat2Z.id in HR.
  rewrite (wa_of_var a1v (B + Z.of_nat j) ltac:(lia)) in HR.
  assert (Lzb : length (zb l) = length l) by (unfold zb; apply length_map).
  zstep. zstep.
  if_cases G.
  - rewrite sxb_lts0 in G. apply KR.
    apply (sx_seven_bit_bad _ j); [lia | lia | rewrite sx_zb_nth; exact G].
  - rewrite sxb_lts0 in G. zstep. zstep. zstep.
    assert (H7' : seven_bit (firstn (S j) (zb l)) = true).
    { rewrite (sx_firstn_S_nth _ _ j 0) by lia. rewrite sx_seven_bit_snoc, H7, sx_zb_nth, G. reflexivity. }
    if_cases G2.
    + zify_cond G2. repeat (rewrite Z.mod_small in G2 by lia).
      eapply (IH (S j)); [lia | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact H7'].
    + zify_cond G2. repeat (rewrite Z.mod_small in G2 by lia).
      assert (EJ : S j = N) by lia. rewrite EJ in H7'. apply KS. exact H7'.
Qed.

(** 0x14944 addi a1, sp, 0x38; mv a2, s5; beqz s5 -> 0x14964; then the loop: seven_bit (bytes[0..n)). *)
Lemma sysex_check : forall (Q : machine_state -> Prop) F fc m ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (n : Z) (l : list byte),
  bytes_at rsegs m (bv_unsigned sp + 56) l -> 0 <= n <= Z.of_nat (length l) ->
  bv_unsigned sp + 56 + Z.of_nat (length l) < 2 ^ 64 ->
  (seven_bit (firstn (Z.to_nat n) (zb l)) = false -> forall a1' a2' a3',
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9
                          s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14800) fc None m (seg_rom rsegs))) ->
  (seven_bit (firstn (Z.to_nat n) (zb l)) = true -> forall a1' a2' a3',
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9
                          s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14964) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x14944) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 n l
         BY Hn HBL KR KS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  zstep. zstep. zstep.
  if_cases E0.
  - zify_cond E0. apply KS. rewrite E0. reflexivity.
  - zify_cond E0.
    eapply (sysex_loop Q F fc m ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 (bv_unsigned sp + 56) (Z.to_nat n) l BY ltac:(lia) ltac:(lia) HBL KR KS
              (Z.to_nat n - 0) 0);
      [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity ].
Qed.
