(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Walk Arr SysStep StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sn_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac br K := brf K; try (exfalso; lia).

Definition SN_WRITE : Z := 0x20638.
Definition hide (P : Prop) := P.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. symmetry. apply firstn_map. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. symmetry. apply skipn_map. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells ssegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Definition firstn_two_copies__stmt : Prop := forall (o s : list Z) (room : nat),
  firstn (Nat.min room (length o)) o ++ firstn (Nat.min (room - Nat.min room (length o)) (length s)) s
  = firstn room (o ++ s).
Section Sz7.
Variables o s room : ltac2:(SecDiet.SzSec.tyM 'firstn_two_copies__stmt "vvv" @o).
#[using="Type"] Lemma firstn_two_copies__body : ltac2:(SecDiet.SzSec.bodyP 'firstn_two_copies__stmt "vvv").
Proof.
 rewrite firstn_app.
  destruct (Nat.le_ge_cases room (length o)) as [L|G].
  - replace (Nat.min room (length o)) with room by lia. replace (room - room)%nat with 0%nat by lia. cbn [Nat.min]. rewrite firstn_O.
    replace (room - length o)%nat with 0%nat by lia. rewrite firstn_O. reflexivity.
  - replace (Nat.min room (length o)) with (length o) by lia. rewrite (firstn_all2 o) by lia. rewrite (firstn_all2 o) by lia. f_equal.
    destruct (Nat.le_ge_cases (room - length o) (length s)) as [L2|G2].
    + replace (Nat.min (room - length o) (length s)) with (room - length o)%nat by lia. reflexivity.
    + replace (Nat.min (room - length o) (length s)) with (length s) by lia. rewrite firstn_all, firstn_all2 by lia. reflexivity.
Qed.
End Sz7.
Lemma firstn_two_copies : ltac:(let t := eval cbv delta [firstn_two_copies__stmt] in firstn_two_copies__stmt in exact t).
Proof. intros o s room. ltac2:(SecDiet.SzSec.closeP 'firstn_two_copies__body "vvv"). Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at ssegs m' Src src.
Definition memcpy_callv__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at ssegs m Src src -> length src = Z.to_nat N -> rw_cells ssegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv ssegs m ->
  evt ssegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz8.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_callv__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_callv__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_callv__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.
End Sz8.
Lemma memcpy_callv : ltac:(let t := eval cbv delta [memcpy_callv__stmt] in memcpy_callv__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_callv__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition dest_carve__stmt : Prop := forall m D dn (w : list Z) (junk : list byte) (k : nat),
  rw_cells ssegs m D [CB dn (zb w ++ junk)] -> (length w + k <= dn)%nat ->
  rw_cells ssegs m D [CB (length w) (zb w)]
  /\ rw_cells ssegs m (D + Z.of_nat (length w)) [CB k (firstn k junk)]
  /\ rw_cells ssegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)].
Section Sz9.
Variables m D dn w junk k : ltac2:(SecDiet.SzSec.tyM 'dest_carve__stmt "vvvvvv" @m).
#[using="Type"] Lemma dest_carve__body : ltac2:(SecDiet.SzSec.bodyP 'dest_carve__stmt "vvvvvv").
Proof.
  intros H LE.
  pose proof (rw_CB_length _ _ _ _ H) as LJ. rewrite length_app, zb_length in LJ.
  assert (E1 : firstn (length w) (zb w ++ junk) = zb w).
  { rewrite <- (zb_length w), firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. }
  assert (E2 : skipn (length w) (zb w ++ junk) = junk).
  { rewrite <- (zb_length w), skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (EM : mk_CB_cells [length w; k; dn - length w - k]%nat (zb w ++ junk)
               = [CB (length w) (zb w); CB k (firstn k junk); CB (dn - length w - k)%nat (skipn k junk)]).
  { cbn [mk_CB_cells]. rewrite E1, E2. rewrite (firstn_all2 (skipn k junk)) by (rewrite length_skipn; lia). reflexivity. }
  apply (rw_cells_split_CB ssegs _ _ [] dn _ [] [length w; k; dn - length w - k]%nat) in H; [ | cbn; lia ].
  rewrite EM, app_nil_r in H. cbn [app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H. rewrite Nat.add_0_r in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.
End Sz9.
Lemma dest_carve : ltac:(let t := eval cbv delta [dest_carve__stmt] in dest_carve__stmt in exact t).
Proof. intros m D dn w junk k. ltac2:(SecDiet.SzSec.closeP 'dest_carve__body "vvvvvv"). Qed.

Definition dest_join__stmt : Prop := forall m D dn (w x : list Z) (junk : list byte) (k : nat),
  rw_cells ssegs m D [CB (length w) (zb w)] ->
  rw_cells ssegs m (D + Z.of_nat (length w)) [CB k (zb x)] ->
  rw_cells ssegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)] ->
  (length w + k <= dn)%nat -> length x = k ->
  rw_cells ssegs m D [CB dn (zb (w ++ x) ++ skipn k junk)].
Section Sz10.
Variables m D dn w x junk k : ltac2:(SecDiet.SzSec.tyM 'dest_join__stmt "vvvvvvv" @m).
#[using="Type"] Lemma dest_join__body : ltac2:(SecDiet.SzSec.bodyP 'dest_join__stmt "vvvvvvv").
Proof.
  intros H1 H2 H3 LE LX.
  assert (J : rw_cells ssegs m D ([] ++ [CB (length w) (zb w); CB k (zb x); CB (dn - length w - k) (skipn k junk)] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app ssegs _ _ [_] _)). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (proj2 (rw_cells_app ssegs _ _ [_] _)). split; [exact H2|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H3. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite !app_nil_r in J.
  replace (length w + (k + (dn - length w - k + 0)))%nat with dn in J by lia.
  rewrite zb_app, <- app_assoc. exact J.
Qed.
End Sz10.
Lemma dest_join : ltac:(let t := eval cbv delta [dest_join__stmt] in dest_join__stmt in exact t).
Proof. intros m D dn w x junk k. ltac2:(SecDiet.SzSec.closeP 'dest_join__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D cap B S bufp lo : Z) (o s wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (junk' : list byte),
    let wr' := wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength s)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells ssegs m' D [CB dn (zb wr' ++ Z_to_bv 8 0 :: junk')]
    /\ rw_cells ssegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells ssegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at ssegs m' B (zb o) /\ bytes_at ssegs m' S (zb s)
    /\ zlength wr' <= cap.

Lemma zlength_app_firstn : forall (w x : list Z) k, (0 <= k <= zlength x)%Z ->
  zlength (w ++ firstn (Z.to_nat k) x) = (zlength w + k)%Z.
Proof. intros w x k Hk. unfold zlength in *. rewrite length_app, length_firstn. lia. Qed.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.

Section SnWrite.
  Variables (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp CK D cap B S bufp lo : Z) (o s : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HO : (zlength o < 2^62)%Z.
  Hypothesis HSL : (zlength s < 2^62)%Z.
  Hypothesis BUFP : (0 <= bufp < 2^64)%Z.
  Hypothesis RNG : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < B /\ B + zlength o <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength s <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z.
  Hypothesis DS : (S + zlength s <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z.
  Hypothesis CKF : (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z.
  Hypothesis CKB : (B + zlength o <= CK \/ CK + 16 <= B)%Z.
  Hypothesis CKS : (S + zlength s <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z.
  Hypothesis FS_ : (S + zlength s <= Fp + 40 \/ Fp + 160 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (CK + 16 <= lo \/ q <= CK)%Z.
  Hypothesis SPF : (Fp + 160 <= lo \/ q <= Fp)%Z.
  Hypothesis SPB : (B + zlength o <= lo \/ q <= B)%Z.
  Hypothesis SPS : (S + zlength s <= lo \/ q <= S)%Z.

  Definition frame_cells (junk : list byte) (s0 s1 s2 s3 s4 s5 : word) : list cell :=
    [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Ltac join_dest k jk :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with DWm : rw_cells _ mm D [CB (length ?w) (zb ?w)], DKm : rw_cells _ mm (D + Z.of_nat (length ?w))%Z [CB (Z.to_nat k) (zb ?x)],
                       DRm : rw_cells _ mm (D + Z.of_nat (length ?w) + Z.of_nat (Z.to_nat k))%Z _ |- _ =>
        pose proof (dest_join mm D dn w x jk (Z.to_nat k) DWm DKm DRm ltac:(lia) ltac:(rewrite length_firstn; lia)) as DST;
        clear DWm DKm DRm end end.

  (* [comment removed for export] *)
  Ltac bytes_back H0 LZ :=
    lazymatch goal with |- bytes_at _ ?mm ?A ?bs =>
      first [ match goal with H : bytes_at _ mm A bs |- _ => exact H end
            | unfold hide in H0;
              lazymatch type of H0 with bytes_at _ ?m0 _ _ =>
                match goal with MUx : munch _ m0 mm |- _ =>
                  eapply bytes_at_transport; [exact H0 | exact MUx | cbn [disjoint_from]; rewrite LZ; first [intuition lia | match goal with |- ?g => idtac "DISJ-FAIL" g; fail end] ] end end
            | match goal with |- ?g => idtac "BYTES-GOAL" g end;
              unfold hide in H0; (let t := type of H0 in idtac "H0:" t);
              repeat match goal with X : munch ?W ?ma ?mb |- _ => idtac "MUNCH" W ma mb; clear X end;
              repeat match goal with X : bytes_at _ ?ma ?A ?bs |- _ => idtac "BYTESAT" ma A bs; clear X end;
              match goal with |- ?g => idtac g end;
              repeat match goal with X : ?T |- _ => lazymatch type of T with Prop => idtac X ":" T; clear X | _ => clear X end end; fail ] end.

  (* [comment removed for export] *)
  Definition sn_A__stmt : Prop := forall (t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wl : Z),
    (0 <= wl <= cap)%Z ->
    rw_cells ssegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells ssegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells ssegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells ssegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    stk ssegs m lo q -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (t0' t1' t2' t3' t4' t5' t6' : word) (junk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (zlength o)) (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 (Z.min (cap - wl) (zlength o))) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x20684) fc None m1 (seg_rom ssegs)
        /\ rw_cells ssegs m1 (q + -64) (frame_cells junk s0 s1 s2 s3 s4 s5)
        /\ munch [(q - 64, q)]%Z m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (q + -64))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom ssegs)).
  Section Sz12.
  Variables t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl : ltac2:(SecDiet.SzSec.tyM 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_A__body : ltac2:(SecDiet.SzSec.bodyP 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using DN HO LO RNG SPCK SPF. pin_using (fun (DN HO LO RNG SPCK SPF : unit) => tt).
 intros WL WPOS WBASE CKP CKC ST MI.
    clear DB DS DCK DF CKF CKB CKS FB FS_ SPD SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold zlength in *.
    unfold SN_WRITE. carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      rewrite Z.min_l by lia.
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - zs. (* [comment removed for export] *) rewrite Z.min_r by lia.
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.
  End Sz12.
  Lemma sn_A : ltac:(let t := eval cbv delta [sn_A__stmt] in sn_A__stmt in exact t).
  Proof using DN HO LO RNG SPCK SPF. intros t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl. ltac2:(SecDiet.SzSec.closeP 'sn_A__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sn_B__stmt : Prop := forall (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte) (k1 : Z),
    let wl := zlength wr in
    (0 <= wl)%Z -> (0 <= k1 <= zlength o)%Z -> (wl + k1 <= cap)%Z ->
    rw_cells ssegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells ssegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at ssegs m B (zb o) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k1)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl - k1)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x206ac) fc None m1 (seg_rom ssegs)
        /\ munch [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ rw_cells ssegs m1 CK [C8 (Z_to_bv 64 (D + wl + k1)); C8 (Z_to_bv 64 (cap - wl - k1))]
        /\ rw_cells ssegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k1) o) ++ skipn (Z.to_nat k1) junk)]
        /\ bytes_at ssegs m1 B (zb o))
      (MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               a0 (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20684) fc None m (seg_rom ssegs)).
  Section Sz13.
  Variables t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m wr junk k1 : ltac2:(SecDiet.SzSec.tyM 'sn_B__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_B__body : ltac2:(SecDiet.SzSec.bodyP 'sn_B__stmt "vvvvvvvvvvvvvvvvv").
  Proof using CAP0 CKB DB DCK DN RNG sp. pin_using (fun (CAP0 CKB DB DCK DN RNG sp : unit) => tt).
 cbv zeta. intros WL K1R ROOM CKC DST BO MI.
    clear DS DF CKF CKS FB FS_ LO SPD SPCK SPF SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. unfold zlength in *.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      assert (K10 : k1 = 0%Z) by lia. subst k1.
      rewrite !Z.add_0_r, !Z.sub_0_r. change (Z.to_nat 0) with 0%nat. rewrite firstn_O, skipn_O, app_nil_r.
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [exact CKC|]. split; [exact DST| exact BO].
    - zs. (* [comment removed for export] *)
      destruct (dest_carve _ _ _ _ _ (Z.to_nat k1) DST ltac:(lia)) as (DW & DK & DR). clear DST.
      pose proof BO as BO0. change (hide (bytes_at ssegs m B (zb o))) in BO0.
      pose proof BO as BOk. rewrite <- (firstn_skipn (Z.to_nat k1) (zb o)) in BOk. apply bytes_at_app in BOk. destruct BOk as [BOk _].
      zs. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [ eapply memcpy_callv with (Dst := (D + Z.of_nat (length wr))%Z) (Src := B) (N := k1) (src := firstn (Z.to_nat k1) (zb o)) (junk := firstn (Z.to_nat k1) junk);
          [ exact BOk | rewrite length_firstn, LZo; (keep_hyps o s dn wr junk k1 K1R; lia) | exact DK | (keep_hyps D cap B o s dn wr junk k1 DN DB K1R ROOM; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 RNG K1R; lia) | (keep_hyps Fp CK D B S o s dn wr junk RNG; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 DN RNG K1R ROOM; lia) | exact MI ]
        | post_call ssegs mm ] end.
      (* [comment removed for export] *)
      rewrite <- zb_firstn in *.
      join_dest k1 junk.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
      split; [exact DST|].
      bytes_back BO0 LZo.
  Qed.
  End Sz13.
  Lemma sn_B : ltac:(let t := eval cbv delta [sn_B__stmt] in sn_B__stmt in exact t).
  Proof using CAP0 CKB DB DCK DN RNG sp. intros t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m wr junk k1. ltac2:(SecDiet.SzSec.closeP 'sn_B__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sn_C__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v : word) (m : mem) (wr : list Z) (junk : list byte),
    let wl := zlength wr in let k2 := Z.min (cap - wl) (zlength s) in
    (0 <= wl <= cap)%Z ->
    rw_cells ssegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells ssegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at ssegs m S (zb s) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s3v' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k2)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) s3v' s4v (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x206dc) fc None m1 (seg_rom ssegs)
        /\ munch [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ rw_cells ssegs m1 CK [C8 (Z_to_bv 64 (D + wl + k2)); C8 (Z_to_bv 64 (cap - wl - k2))]
        /\ rw_cells ssegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k2) s) ++ skipn (Z.to_nat k2) junk)]
        /\ bytes_at ssegs m1 S (zb s))
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x206ac) fc None m (seg_rom ssegs)).
  Section Sz14.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v m wr junk : ltac2:(SecDiet.SzSec.tyM 'sn_C__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma sn_C__body : ltac2:(SecDiet.SzSec.bodyP 'sn_C__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using CAP0 CKS DCK DN DS HSL RNG sp. pin_using (fun (CAP0 CKS DCK DN DS HSL RNG sp : unit) => tt).
 cbv zeta. intros WL CKC DST BS MI.
    clear DB DF CKF CKB FB FS_ LO SPD SPCK SPF SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length s) as LZs. unfold zlength in *.
    (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    2: zs. (* [comment removed for export] *)
    all: zs; (* [comment removed for export] *) brf K2.
    1,3: (replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with 0%Z by lia);
         rewrite !Z.add_0_r, !Z.sub_0_r; change (Z.to_nat 0) with 0%nat; rewrite firstn_O, skipn_O, app_nil_r;
         apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end);
         (split; [cbv delta [mkR]; reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]);
         (split; [exact CKC|]); split; [exact DST| exact BS].
    all: let s3r := getreg 19%Z in lazymatch s3r with Z_to_bv 64 ?k =>
      replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with k by lia;
      set (k2 := k);
      assert (EK2 : k2 = k) by reflexivity;
      assert (K2R : (0 < k2 <= Z.of_nat (length s) /\ Z.of_nat (length wr) + k2 <= cap)%Z) by lia end.
    all: clear K1 K2.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: destruct (dest_carve _ _ _ _ _ (Z.to_nat k2) DST ltac:(lia)) as (DW & DK & DR); clear DST.
    all: pose proof BS as BS0; change (hide (bytes_at ssegs m S (zb s))) in BS0.
    all: pose proof BS as BSk; rewrite <- (firstn_skipn (Z.to_nat k2) (zb s)) in BSk; apply bytes_at_app in BSk; destruct BSk as [BSk _].
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [ eapply memcpy_callv with (Dst := (D + Z.of_nat (length wr))%Z) (Src := S) (N := k2) (src := firstn (Z.to_nat k2) (zb s)) (junk := firstn (Z.to_nat k2) junk);
          [ exact BSk | rewrite length_firstn, LZs; (keep_hyps cap o s dn wr junk K2R; lia) | exact DK | (keep_hyps D cap S o s dn wr junk DN DS K2R; lia) | (keep_hyps cap o s dn wr junk HSL K2R; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk RNG; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk DN RNG K2R WL; lia) | exact MI ]
        | post_call ssegs mm ] end.
    all: rewrite <- zb_firstn in *.
    all: join_dest k2 junk.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *)
         zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|].
    all: split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
    all: split; [exact DST|].
    all: bytes_back BS0 LZs.
  Qed.
  End Sz14.
  Lemma sn_C : ltac:(let t := eval cbv delta [sn_C__stmt] in sn_C__stmt in exact t).
  Proof using CAP0 CKS DCK DN DS HSL RNG sp. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v m wr junk. ltac2:(SecDiet.SzSec.closeP 'sn_C__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition WD : list (Z * Z) := [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z.

  Definition sn_D__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v : word) (s0 s1 s2 s3 s4 s5 : word) (m : mem)
      (wr : list Z) (junk fj : list byte) (wposv wbasev : word),
    let wl := zlength wr in
    (0 <= wl <= cap)%Z ->
    rw_cells ssegs m D [CB dn (zb wr ++ junk)] ->
    rw_cells ssegs m (Fp + 40) [C8 wposv] -> rw_cells ssegs m (Fp + 56) [C8 wbasev] ->
    rw_cells ssegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells ssegs m (q + -64) (frame_cells fj s0 s1 s2 s3 s4 s5) ->
    stk ssegs m lo (q + -64) ->
    mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (zlength s)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom ssegs)
        /\ munch WD m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo q
        /\ rw_cells ssegs m1 D [CB dn (zb wr ++ Z_to_bv 8 0 :: skipn 1 junk)]
        /\ rw_cells ssegs m1 (Fp + 40) [C8 (Z_to_bv 64 bufp)]
        /\ rw_cells ssegs m1 (Fp + 56) [C8 (Z_to_bv 64 bufp)])
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) s3v s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x206dc) fc None m (seg_rom ssegs)).
  Section Sz15.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s0 s1 s2 s3 s4 s5 m wr junk fj wposv wbasev : ltac2:(SecDiet.SzSec.tyM 'sn_D__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma sn_D__body : ltac2:(SecDiet.SzSec.bodyP 'sn_D__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CAP0 DF DN FB FS_ LO RNG SPB SPD SPF SPS. pin_using (fun (CAP0 DF DN FB FS_ LO RNG SPB SPD SPF SPS : unit) => tt).
 cbv zeta. intros WL DST WPOS WBASE BUFC FR ST MI.
    clear DB DS CKB CKS DCK CKF SPCK.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold WD. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    unfold zlength in *. unfold frame_cells in FR.
    (* [comment removed for export] *)
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (u8arr_store_ok ssegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 64 (D + Z.of_nat (length wr))) DA
                  ltac:(rewrite length_app, zb_length; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length wr)) : word) with (wa (D + Z.of_nat (length wr))) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write ssegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 8 0) DA ltac:(rewrite length_app, zb_length; lia)) as DA2. clear DA DST. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. clear DA2. rewrite upd_length, length_app, zb_length in DST.
    replace (length wr + length junk)%nat with dn in DST by lia.
    assert (EU : upd (zb wr ++ junk) (Z.to_nat (Z.of_nat (length wr))) (Z_to_bv 8 0) = zb wr ++ Z_to_bv 8 0 :: skipn 1 junk).
    { rewrite Nat2Z.id, upd_firstn_skipn by (rewrite length_app, zb_length; lia).
      rewrite firstn_app, skipn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite (firstn_all2 (zb wr)) by (rewrite zb_length; lia).
      rewrite (skipn_all2 (zb wr)) by (rewrite zb_length; lia).
      replace (Datatypes.S (length wr) - length wr)%nat with 1%nat by lia. reflexivity. }
    rewrite EU in DST. clear EU.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 9 zs. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { first [exact DST | lazymatch type of DST with ?t => idtac "DST:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail]. }
    split; assumption.
  Qed.
  End Sz15.
  Lemma sn_D : ltac:(let t := eval cbv delta [sn_D__stmt] in sn_D__stmt in exact t).
  Proof using CAP0 DF DN FB FS_ LO RNG SPB SPD SPF SPS. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s0 s1 s2 s3 s4 s5 m wr junk fj wposv wbasev. ltac2:(SecDiet.SzSec.closeP 'sn_D__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sn_write_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
    rw_cells ssegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells ssegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells ssegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells ssegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells ssegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    bytes_at ssegs m B (zb o) -> bytes_at ssegs m S (zb s) ->
    rw_cells ssegs m D [CB dn (zb wr ++ junk)] ->
    stk ssegs m lo q -> mem_inv ssegs m ->
    evt ssegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D cap B S bufp lo o s wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom ssegs)).
  Section Sz16.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk : ltac2:(SecDiet.SzSec.tyM 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO RNG SPB SPCK SPD SPF SPS. pin_using (fun (BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO RNG SPB SPCK SPD SPF SPS : unit) => tt).
 intros WL -> -> -> WPOS WBASE BUFC CKP CKC BO BS DST ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. pose proof (zb_length s) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o)%Z) by (unfold zlength; lia). assert (NNs : (0 <= zlength s)%Z) by (unfold zlength; lia).
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_;
    stash SPD; stash SPCK; stash SPF; stash SPB; stash SPS.
    set (W := [(q - 64, q); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z).
    assert (SUB1 : sub_fp [(q - 64, q)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; tauto).
    assert (SUB2 : sub_fp [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; tauto).
    (* [comment removed for export] *)
    eapply evt_cut. { eapply (sn_A t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m (zlength wr)); first [exact WL | eassumption]. }
    cbv beta. intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & fj & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (T1 : forall A cs, rw_cells ssegs m A cs -> (A + Z.of_nat (cells_size cs) <= lo \/ q <= A)%Z -> rw_cells ssegs m1 A cs).
    { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU1 | exact WM1 | cbn [disjoint_from]; lia]. }
    assert (TB1 : forall A bs, bytes_at ssegs m A bs -> (A + Z.of_nat (length bs) <= lo \/ q <= A)%Z -> bytes_at ssegs m1 A bs).
    { intros A bs H HA. eapply bytes_at_transport; [exact H | exact MU1 | cbn [disjoint_from]; lia]. }
    pose proof (T1 _ _ WPOS ltac:(cbn; unfold hide in SPF; lia)) as WPOS1. pose proof (T1 _ _ WBASE ltac:(cbn; unfold hide in SPF; lia)) as WBASE1.
    pose proof (T1 _ _ BUFC ltac:(cbn; unfold hide in SPF; lia)) as BUFC1. pose proof (T1 _ _ CKP ltac:(cbn; unfold hide in SPF; lia)) as CKP1.
    pose proof (T1 _ _ CKC ltac:(cbn; unfold hide in SPCK; lia)) as CKC1. pose proof (T1 _ _ DST ltac:(cbn; unfold hide in SPD; lia)) as DST1.
    pose proof (TB1 _ _ BO ltac:(rewrite LZo; unfold hide in SPB; unfold zlength in SPB; lia)) as BO1.
    pose proof (TB1 _ _ BS ltac:(rewrite LZs; unfold hide in SPS; unfold zlength in SPS; lia)) as BS1.
    clear T1 TB1 WPOS WBASE BUFC CKP CKC DST BO BS MI.
    (* [comment removed for export] *)
    set (k1 := Z.min (cap - zlength wr) (zlength o)).
    assert (K1R : (0 <= k1 <= zlength o /\ zlength wr + k1 <= cap)%Z) by (subst k1; lia).
    eapply evt_cut. { eapply (sn_B u0 u1 u2 _ a3 a4 a5 a6 a7 u3 u4 u5 u6 m1 wr junk k1); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms2 (x1 & v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & CKC2 & DST2 & BO2).
    assert (T2 : forall A cs, rw_cells ssegs m1 A cs -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells ssegs m2 A cs).
    { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    pose proof (T2 _ _ WPOS1 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS2.
    pose proof (T2 _ _ WBASE1 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE2.
    pose proof (T2 _ _ BUFC1 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC2.
    pose proof (T2 _ _ FR1 ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR2.
    assert (BS2 : bytes_at ssegs m2 S (zb s)).
    { eapply bytes_at_transport; [exact BS1 | exact MU2 | cbn [disjoint_from]; rewrite LZs; unfold hide in CKS, DS; unfold zlength in CKS, DS; lia]. }
    assert (ST2 : stk ssegs m2 lo (q + -64)).
    { eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; unfold hide in SPCK, SPD; lia]. }
    clear T2 WPOS1 WBASE1 BUFC1 FR1 BS1 ST1 CKC1 DST1 CKP1 MI1.
    (* [comment removed for export] *)
    set (wr1 := wr ++ firstn (Z.to_nat k1) o) in *.
    assert (L1 : zlength wr1 = (zlength wr + k1)%Z) by (subst wr1; apply zlength_app_firstn; lia).
    replace (D + zlength wr + k1)%Z with (D + zlength wr1)%Z in * by lia.
    replace (cap - zlength wr - k1)%Z with (cap - zlength wr1)%Z in * by lia.
    set (k2 := Z.min (cap - zlength wr1) (zlength s)).
    eapply evt_cut. { eapply (sn_C x1 v0 v1 v2 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 _ m2 wr1 (skipn (Z.to_nat k1) junk)); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms3 (x1' & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & s3v & m3 & -> & MU3 & WM3 & MI3 & CKC3 & DST3 & BS3).
    fold k2 in CKC3. fold k2 in DST3. fold k2.
    assert (K2R : (0 <= k2 <= zlength s /\ zlength wr1 + k2 <= cap)%Z) by (subst k2; lia).
    assert (T3 : forall A cs, rw_cells ssegs m2 A cs -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells ssegs m3 A cs).
    { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MU3 | exact WM3 | cbn [disjoint_from]; lia]. }
    pose proof (T3 _ _ WPOS2 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS3.
    pose proof (T3 _ _ WBASE2 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE3.
    pose proof (T3 _ _ BUFC2 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC3.
    pose proof (T3 _ _ FR2 ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR3.
    assert (BO3 : bytes_at ssegs m3 B (zb o)).
    { eapply bytes_at_transport; [exact BO2 | exact MU3 | cbn [disjoint_from]; rewrite LZo; unfold hide in CKB, DB; unfold zlength in CKB, DB; lia]. }
    assert (ST3 : stk ssegs m3 lo (q + -64)).
    { eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 | cbn [disjoint_from]; unfold hide in SPCK, SPD; lia]. }
    (* [comment removed for export] *)
    assert (MU13 : munch W m m3).
    { eapply munch_trans; [apply (munch_weaken _ _ _ _ SUB1); exact MU1|].
      eapply munch_trans; apply (munch_weaken _ _ _ _ SUB2); [exact MU2 | exact MU3]. }
    assert (WM13 : wmono ssegs m m3) by (eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]).
    clear T3 WPOS2 WBASE2 BUFC2 FR2 BO2 ST2 CKC2 DST2 MU1 MU2 MU3 WM1 WM2 WM3 MI2.
    (* [comment removed for export] *)
    set (wr2 := wr1 ++ firstn (Z.to_nat k2) s) in *.
    assert (L2 : zlength wr2 = (zlength wr1 + k2)%Z) by (subst wr2; apply zlength_app_firstn; lia).
    replace (D + zlength wr1 + k2)%Z with (D + zlength wr2)%Z in * by lia.
    replace (cap - zlength wr1 - k2)%Z with (cap - zlength wr2)%Z in * by lia.
    eapply evt_cut. { eapply (sn_D x1' w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 s3v _ s0 s1 s2 s3 s4 s5 m3 wr2); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms4 (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & DST4 & WPOS4 & WBASE4).
    unfold WD in MU4.
    assert (SUB4 : sub_fp [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; (keep_hyps sp Fp CK D cap B S bufp o s dn wr x H; tauto)).
    assert (MU14 : munch W m m4) by (eapply munch_trans; [exact MU13 | apply (munch_weaken _ _ _ _ SUB4); exact MU4]).
    assert (WM14 : wmono ssegs m m4) by (eapply wmono_trans; [exact WM13 | exact WM4]).
    assert (CKC4 : rw_cells ssegs m4 CK [C8 (Z_to_bv 64 (D + zlength wr2)); C8 (Z_to_bv 64 (cap - zlength wr2))]).
    { eapply rw_cells_transport; [exact CKC3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; unfold hide in SPCK, DCK, CKF; lia]. }
    assert (BO4 : bytes_at ssegs m4 B (zb o)).
    { eapply bytes_at_transport; [exact BO3 | exact MU4 | cbn [disjoint_from]; rewrite LZo; unfold hide in SPB, DB, FB; unfold zlength in SPB, DB, FB; lia]. }
    assert (BS4 : bytes_at ssegs m4 S (zb s)).
    { eapply bytes_at_transport; [exact BS3 | exact MU4 | cbn [disjoint_from]; rewrite LZs; unfold hide in SPS, DS, FS_; unfold zlength in SPS, DS, FS_; lia]. }
    subst W.
    (* [comment removed for export] *)
    assert (EW : wr2 = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s)).
    { subst wr2 wr1. rewrite <- app_assoc. f_equal. subst k1 k2. rewrite L1. unfold zlength.
      rewrite <- (firstn_two_copies o s (Z.to_nat (cap - Z.of_nat (length wr)))). f_equal; [f_equal; (keep_hyps sp cap o s dn wr junk; lia)|]. f_equal. (keep_hyps sp cap o s dn wr junk; lia). }
    apply evt_done. unfold sn_write_post. cbv zeta. rewrite <- EW.
    exists y0, y1, y2, d1, d2, d3, d4, d5, d6, d7, y3, y4, y5, y6, m4, (skipn 1 (skipn (Z.to_nat k2) (skipn (Z.to_nat k1) junk))).
    split; [reflexivity|]. split; [exact MU14|]. split; [exact WM14|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact CKC4|]. split; [exact DST4|]. split; [exact WPOS4|]. split; [exact WBASE4|].
    split; [exact BO4|]. split; [exact BS4|]. lia.
  Qed.
  End Sz16.
  Theorem sn_write_spec : ltac:(let t := eval cbv delta [sn_write_spec__stmt] in sn_write_spec__stmt in exact t).
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO RNG SPB SPCK SPD SPF SPS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk. ltac2:(SecDiet.SzSec.closeP 'sn_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnWrite.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac br K := brf K; try (exfalso; lia).

Definition SN_WRITE : Z := 0x20df8.
Definition hide (P : Prop) := P.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. symmetry. apply firstn_map. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. symmetry. apply skipn_map. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells usegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Definition firstn_two_copies__stmt : Prop := forall (o s : list Z) (room : nat),
  firstn (Nat.min room (length o)) o ++ firstn (Nat.min (room - Nat.min room (length o)) (length s)) s
  = firstn room (o ++ s).
Section Sz7.
Variables o s room : ltac2:(SecDiet.SzSec.tyM 'firstn_two_copies__stmt "vvv" @o).
#[using="Type"] Lemma firstn_two_copies__body : ltac2:(SecDiet.SzSec.bodyP 'firstn_two_copies__stmt "vvv").
Proof.
 rewrite firstn_app.
  destruct (Nat.le_ge_cases room (length o)) as [L|G].
  - replace (Nat.min room (length o)) with room by lia. replace (room - room)%nat with 0%nat by lia. cbn [Nat.min]. rewrite firstn_O.
    replace (room - length o)%nat with 0%nat by lia. rewrite firstn_O. reflexivity.
  - replace (Nat.min room (length o)) with (length o) by lia. rewrite (firstn_all2 o) by lia. rewrite (firstn_all2 o) by lia. f_equal.
    destruct (Nat.le_ge_cases (room - length o) (length s)) as [L2|G2].
    + replace (Nat.min (room - length o) (length s)) with (room - length o)%nat by lia. reflexivity.
    + replace (Nat.min (room - length o) (length s)) with (length s) by lia. rewrite firstn_all, firstn_all2 by lia. reflexivity.
Qed.
End Sz7.
Lemma firstn_two_copies : ltac:(let t := eval cbv delta [firstn_two_copies__stmt] in firstn_two_copies__stmt in exact t).
Proof. intros o s room. ltac2:(SecDiet.SzSec.closeP 'firstn_two_copies__body "vvv"). Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at usegs m' Src src.
Definition memcpy_callv__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv usegs m ->
  evt usegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz8.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_callv__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_callv__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_callv__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.
End Sz8.
Lemma memcpy_callv : ltac:(let t := eval cbv delta [memcpy_callv__stmt] in memcpy_callv__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_callv__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition dest_carve__stmt : Prop := forall m D dn (w : list Z) (junk : list byte) (k : nat),
  rw_cells usegs m D [CB dn (zb w ++ junk)] -> (length w + k <= dn)%nat ->
  rw_cells usegs m D [CB (length w) (zb w)]
  /\ rw_cells usegs m (D + Z.of_nat (length w)) [CB k (firstn k junk)]
  /\ rw_cells usegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)].
Section Sz9.
Variables m D dn w junk k : ltac2:(SecDiet.SzSec.tyM 'dest_carve__stmt "vvvvvv" @m).
#[using="Type"] Lemma dest_carve__body : ltac2:(SecDiet.SzSec.bodyP 'dest_carve__stmt "vvvvvv").
Proof.
  intros H LE.
  pose proof (rw_CB_length _ _ _ _ H) as LJ. rewrite length_app, zb_length in LJ.
  assert (E1 : firstn (length w) (zb w ++ junk) = zb w).
  { rewrite <- (zb_length w), firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. }
  assert (E2 : skipn (length w) (zb w ++ junk) = junk).
  { rewrite <- (zb_length w), skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (EM : mk_CB_cells [length w; k; dn - length w - k]%nat (zb w ++ junk)
               = [CB (length w) (zb w); CB k (firstn k junk); CB (dn - length w - k)%nat (skipn k junk)]).
  { cbn [mk_CB_cells]. rewrite E1, E2. rewrite (firstn_all2 (skipn k junk)) by (rewrite length_skipn; lia). reflexivity. }
  apply (rw_cells_split_CB usegs _ _ [] dn _ [] [length w; k; dn - length w - k]%nat) in H; [ | cbn; lia ].
  rewrite EM, app_nil_r in H. cbn [app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H. rewrite Nat.add_0_r in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.
End Sz9.
Lemma dest_carve : ltac:(let t := eval cbv delta [dest_carve__stmt] in dest_carve__stmt in exact t).
Proof. intros m D dn w junk k. ltac2:(SecDiet.SzSec.closeP 'dest_carve__body "vvvvvv"). Qed.

Definition dest_join__stmt : Prop := forall m D dn (w x : list Z) (junk : list byte) (k : nat),
  rw_cells usegs m D [CB (length w) (zb w)] ->
  rw_cells usegs m (D + Z.of_nat (length w)) [CB k (zb x)] ->
  rw_cells usegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)] ->
  (length w + k <= dn)%nat -> length x = k ->
  rw_cells usegs m D [CB dn (zb (w ++ x) ++ skipn k junk)].
Section Sz10.
Variables m D dn w x junk k : ltac2:(SecDiet.SzSec.tyM 'dest_join__stmt "vvvvvvv" @m).
#[using="Type"] Lemma dest_join__body : ltac2:(SecDiet.SzSec.bodyP 'dest_join__stmt "vvvvvvv").
Proof.
  intros H1 H2 H3 LE LX.
  assert (J : rw_cells usegs m D ([] ++ [CB (length w) (zb w); CB k (zb x); CB (dn - length w - k) (skipn k junk)] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app usegs _ _ [_] _)). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (proj2 (rw_cells_app usegs _ _ [_] _)). split; [exact H2|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H3. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite !app_nil_r in J.
  replace (length w + (k + (dn - length w - k + 0)))%nat with dn in J by lia.
  rewrite zb_app, <- app_assoc. exact J.
Qed.
End Sz10.
Lemma dest_join : ltac:(let t := eval cbv delta [dest_join__stmt] in dest_join__stmt in exact t).
Proof. intros m D dn w x junk k. ltac2:(SecDiet.SzSec.closeP 'dest_join__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D cap B S bufp lo : Z) (o s wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (junk' : list byte),
    let wr' := wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength s)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells usegs m' D [CB dn (zb wr' ++ Z_to_bv 8 0 :: junk')]
    /\ rw_cells usegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells usegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at usegs m' B (zb o) /\ bytes_at usegs m' S (zb s)
    /\ zlength wr' <= cap.

Lemma zlength_app_firstn : forall (w x : list Z) k, (0 <= k <= zlength x)%Z ->
  zlength (w ++ firstn (Z.to_nat k) x) = (zlength w + k)%Z.
Proof. intros w x k Hk. unfold zlength in *. rewrite length_app, length_firstn. lia. Qed.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.

Section SnWrite.
  Variables (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp CK D cap B S bufp lo : Z) (o s : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HO : (zlength o < 2^62)%Z.
  Hypothesis HSL : (zlength s < 2^62)%Z.
  Hypothesis BUFP : (0 <= bufp < 2^64)%Z.
  Hypothesis RNG : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < B /\ B + zlength o <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength s <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z.
  Hypothesis DS : (S + zlength s <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z.
  Hypothesis CKF : (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z.
  Hypothesis CKB : (B + zlength o <= CK \/ CK + 16 <= B)%Z.
  Hypothesis CKS : (S + zlength s <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z.
  Hypothesis FS_ : (S + zlength s <= Fp + 40 \/ Fp + 160 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (CK + 16 <= lo \/ q <= CK)%Z.
  Hypothesis SPF : (Fp + 160 <= lo \/ q <= Fp)%Z.
  Hypothesis SPB : (B + zlength o <= lo \/ q <= B)%Z.
  Hypothesis SPS : (S + zlength s <= lo \/ q <= S)%Z.

  Definition frame_cells (junk : list byte) (s0 s1 s2 s3 s4 s5 : word) : list cell :=
    [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Ltac join_dest k jk :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with DWm : rw_cells _ mm D [CB (length ?w) (zb ?w)], DKm : rw_cells _ mm (D + Z.of_nat (length ?w))%Z [CB (Z.to_nat k) (zb ?x)],
                       DRm : rw_cells _ mm (D + Z.of_nat (length ?w) + Z.of_nat (Z.to_nat k))%Z _ |- _ =>
        pose proof (dest_join mm D dn w x jk (Z.to_nat k) DWm DKm DRm ltac:(lia) ltac:(rewrite length_firstn; lia)) as DST;
        clear DWm DKm DRm end end.

  (* [comment removed for export] *)
  Ltac bytes_back H0 LZ :=
    lazymatch goal with |- bytes_at _ ?mm ?A ?bs =>
      first [ match goal with H : bytes_at _ mm A bs |- _ => exact H end
            | unfold hide in H0;
              lazymatch type of H0 with bytes_at _ ?m0 _ _ =>
                match goal with MUx : munch _ m0 mm |- _ =>
                  eapply bytes_at_transport; [exact H0 | exact MUx | cbn [disjoint_from]; rewrite LZ; first [intuition lia | match goal with |- ?g => idtac "DISJ-FAIL" g; fail end] ] end end
            | match goal with |- ?g => idtac "BYTES-GOAL" g end;
              unfold hide in H0; (let t := type of H0 in idtac "H0:" t);
              repeat match goal with X : munch ?W ?ma ?mb |- _ => idtac "MUNCH" W ma mb; clear X end;
              repeat match goal with X : bytes_at _ ?ma ?A ?bs |- _ => idtac "BYTESAT" ma A bs; clear X end;
              match goal with |- ?g => idtac g end;
              repeat match goal with X : ?T |- _ => lazymatch type of T with Prop => idtac X ":" T; clear X | _ => clear X end end; fail ] end.

  (* [comment removed for export] *)
  Definition sn_A__stmt : Prop := forall (t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wl : Z),
    (0 <= wl <= cap)%Z ->
    rw_cells usegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells usegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells usegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells usegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    stk usegs m lo q -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' t3' t4' t5' t6' : word) (junk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (zlength o)) (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 (Z.min (cap - wl) (zlength o))) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x20e44) fc None m1 (seg_rom usegs)
        /\ rw_cells usegs m1 (q + -64) (frame_cells junk s0 s1 s2 s3 s4 s5)
        /\ munch [(q - 64, q)]%Z m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (q + -64))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom usegs)).
  Section Sz12.
  Variables t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl : ltac2:(SecDiet.SzSec.tyM 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_A__body : ltac2:(SecDiet.SzSec.bodyP 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using DN HO LO RNG SPCK SPF. pin_using (fun (DN HO LO RNG SPCK SPF : unit) => tt).
 intros WL WPOS WBASE CKP CKC ST MI.
    clear DB DS DCK DF CKF CKB CKS FB FS_ SPD SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold zlength in *.
    unfold SN_WRITE. carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      rewrite Z.min_l by lia.
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - zs. (* [comment removed for export] *) rewrite Z.min_r by lia.
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.
  End Sz12.
  Lemma sn_A : ltac:(let t := eval cbv delta [sn_A__stmt] in sn_A__stmt in exact t).
  Proof using DN HO LO RNG SPCK SPF. intros t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl. ltac2:(SecDiet.SzSec.closeP 'sn_A__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sn_B__stmt : Prop := forall (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte) (k1 : Z),
    let wl := zlength wr in
    (0 <= wl)%Z -> (0 <= k1 <= zlength o)%Z -> (wl + k1 <= cap)%Z ->
    rw_cells usegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells usegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at usegs m B (zb o) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k1)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl - k1)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x20e6c) fc None m1 (seg_rom usegs)
        /\ munch [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ rw_cells usegs m1 CK [C8 (Z_to_bv 64 (D + wl + k1)); C8 (Z_to_bv 64 (cap - wl - k1))]
        /\ rw_cells usegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k1) o) ++ skipn (Z.to_nat k1) junk)]
        /\ bytes_at usegs m1 B (zb o))
      (MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               a0 (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20e44) fc None m (seg_rom usegs)).
  Section Sz13.
  Variables t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m wr junk k1 : ltac2:(SecDiet.SzSec.tyM 'sn_B__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_B__body : ltac2:(SecDiet.SzSec.bodyP 'sn_B__stmt "vvvvvvvvvvvvvvvvv").
  Proof using CAP0 CKB DB DCK DN RNG sp. pin_using (fun (CAP0 CKB DB DCK DN RNG sp : unit) => tt).
 cbv zeta. intros WL K1R ROOM CKC DST BO MI.
    clear DS DF CKF CKS FB FS_ LO SPD SPCK SPF SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. unfold zlength in *.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      assert (K10 : k1 = 0%Z) by lia. subst k1.
      rewrite !Z.add_0_r, !Z.sub_0_r. change (Z.to_nat 0) with 0%nat. rewrite firstn_O, skipn_O, app_nil_r.
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [exact CKC|]. split; [exact DST| exact BO].
    - zs. (* [comment removed for export] *)
      destruct (dest_carve _ _ _ _ _ (Z.to_nat k1) DST ltac:(lia)) as (DW & DK & DR). clear DST.
      pose proof BO as BO0. change (hide (bytes_at usegs m B (zb o))) in BO0.
      pose proof BO as BOk. rewrite <- (firstn_skipn (Z.to_nat k1) (zb o)) in BOk. apply bytes_at_app in BOk. destruct BOk as [BOk _].
      zs. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [ eapply memcpy_callv with (Dst := (D + Z.of_nat (length wr))%Z) (Src := B) (N := k1) (src := firstn (Z.to_nat k1) (zb o)) (junk := firstn (Z.to_nat k1) junk);
          [ exact BOk | rewrite length_firstn, LZo; (keep_hyps o s dn wr junk k1 K1R; lia) | exact DK | (keep_hyps D cap B o s dn wr junk k1 DN DB K1R ROOM; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 RNG K1R; lia) | (keep_hyps Fp CK D B S o s dn wr junk RNG; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 DN RNG K1R ROOM; lia) | exact MI ]
        | post_call usegs mm ] end.
      (* [comment removed for export] *)
      rewrite <- zb_firstn in *.
      join_dest k1 junk.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
      split; [exact DST|].
      bytes_back BO0 LZo.
  Qed.
  End Sz13.
  Lemma sn_B : ltac:(let t := eval cbv delta [sn_B__stmt] in sn_B__stmt in exact t).
  Proof using CAP0 CKB DB DCK DN RNG sp. intros t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m wr junk k1. ltac2:(SecDiet.SzSec.closeP 'sn_B__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sn_C__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v : word) (m : mem) (wr : list Z) (junk : list byte),
    let wl := zlength wr in let k2 := Z.min (cap - wl) (zlength s) in
    (0 <= wl <= cap)%Z ->
    rw_cells usegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells usegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at usegs m S (zb s) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s3v' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k2)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) s3v' s4v (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x20e9c) fc None m1 (seg_rom usegs)
        /\ munch [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ rw_cells usegs m1 CK [C8 (Z_to_bv 64 (D + wl + k2)); C8 (Z_to_bv 64 (cap - wl - k2))]
        /\ rw_cells usegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k2) s) ++ skipn (Z.to_nat k2) junk)]
        /\ bytes_at usegs m1 S (zb s))
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20e6c) fc None m (seg_rom usegs)).
  Section Sz14.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v m wr junk : ltac2:(SecDiet.SzSec.tyM 'sn_C__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma sn_C__body : ltac2:(SecDiet.SzSec.bodyP 'sn_C__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using CAP0 CKS DCK DN DS HSL RNG sp. pin_using (fun (CAP0 CKS DCK DN DS HSL RNG sp : unit) => tt).
 cbv zeta. intros WL CKC DST BS MI.
    clear DB DF CKF CKB FB FS_ LO SPD SPCK SPF SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length s) as LZs. unfold zlength in *.
    (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    2: zs. (* [comment removed for export] *)
    all: zs; (* [comment removed for export] *) brf K2.
    1,3: (replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with 0%Z by lia);
         rewrite !Z.add_0_r, !Z.sub_0_r; change (Z.to_nat 0) with 0%nat; rewrite firstn_O, skipn_O, app_nil_r;
         apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end);
         (split; [cbv delta [mkR]; reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]);
         (split; [exact CKC|]); split; [exact DST| exact BS].
    all: let s3r := getreg 19%Z in lazymatch s3r with Z_to_bv 64 ?k =>
      replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with k by lia;
      set (k2 := k);
      assert (EK2 : k2 = k) by reflexivity;
      assert (K2R : (0 < k2 <= Z.of_nat (length s) /\ Z.of_nat (length wr) + k2 <= cap)%Z) by lia end.
    all: clear K1 K2.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: destruct (dest_carve _ _ _ _ _ (Z.to_nat k2) DST ltac:(lia)) as (DW & DK & DR); clear DST.
    all: pose proof BS as BS0; change (hide (bytes_at usegs m S (zb s))) in BS0.
    all: pose proof BS as BSk; rewrite <- (firstn_skipn (Z.to_nat k2) (zb s)) in BSk; apply bytes_at_app in BSk; destruct BSk as [BSk _].
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [ eapply memcpy_callv with (Dst := (D + Z.of_nat (length wr))%Z) (Src := S) (N := k2) (src := firstn (Z.to_nat k2) (zb s)) (junk := firstn (Z.to_nat k2) junk);
          [ exact BSk | rewrite length_firstn, LZs; (keep_hyps cap o s dn wr junk K2R; lia) | exact DK | (keep_hyps D cap S o s dn wr junk DN DS K2R; lia) | (keep_hyps cap o s dn wr junk HSL K2R; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk RNG; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk DN RNG K2R WL; lia) | exact MI ]
        | post_call usegs mm ] end.
    all: rewrite <- zb_firstn in *.
    all: join_dest k2 junk.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *)
         zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|].
    all: split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
    all: split; [exact DST|].
    all: bytes_back BS0 LZs.
  Qed.
  End Sz14.
  Lemma sn_C : ltac:(let t := eval cbv delta [sn_C__stmt] in sn_C__stmt in exact t).
  Proof using CAP0 CKS DCK DN DS HSL RNG sp. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v m wr junk. ltac2:(SecDiet.SzSec.closeP 'sn_C__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition WD : list (Z * Z) := [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z.

  Definition sn_D__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v : word) (s0 s1 s2 s3 s4 s5 : word) (m : mem)
      (wr : list Z) (junk fj : list byte) (wposv wbasev : word),
    let wl := zlength wr in
    (0 <= wl <= cap)%Z ->
    rw_cells usegs m D [CB dn (zb wr ++ junk)] ->
    rw_cells usegs m (Fp + 40) [C8 wposv] -> rw_cells usegs m (Fp + 56) [C8 wbasev] ->
    rw_cells usegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells usegs m (q + -64) (frame_cells fj s0 s1 s2 s3 s4 s5) ->
    stk usegs m lo (q + -64) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (zlength s)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom usegs)
        /\ munch WD m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo q
        /\ rw_cells usegs m1 D [CB dn (zb wr ++ Z_to_bv 8 0 :: skipn 1 junk)]
        /\ rw_cells usegs m1 (Fp + 40) [C8 (Z_to_bv 64 bufp)]
        /\ rw_cells usegs m1 (Fp + 56) [C8 (Z_to_bv 64 bufp)])
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) s3v s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20e9c) fc None m (seg_rom usegs)).
  Section Sz15.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s0 s1 s2 s3 s4 s5 m wr junk fj wposv wbasev : ltac2:(SecDiet.SzSec.tyM 'sn_D__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma sn_D__body : ltac2:(SecDiet.SzSec.bodyP 'sn_D__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CAP0 DF DN FB FS_ LO RNG SPB SPD SPF SPS. pin_using (fun (CAP0 DF DN FB FS_ LO RNG SPB SPD SPF SPS : unit) => tt).
 cbv zeta. intros WL DST WPOS WBASE BUFC FR ST MI.
    clear DB DS CKB CKS DCK CKF SPCK.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold WD. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    unfold zlength in *. unfold frame_cells in FR.
    (* [comment removed for export] *)
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (u8arr_store_ok usegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 64 (D + Z.of_nat (length wr))) DA
                  ltac:(rewrite length_app, zb_length; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length wr)) : word) with (wa (D + Z.of_nat (length wr))) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write usegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 8 0) DA ltac:(rewrite length_app, zb_length; lia)) as DA2. clear DA DST. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. clear DA2. rewrite upd_length, length_app, zb_length in DST.
    replace (length wr + length junk)%nat with dn in DST by lia.
    assert (EU : upd (zb wr ++ junk) (Z.to_nat (Z.of_nat (length wr))) (Z_to_bv 8 0) = zb wr ++ Z_to_bv 8 0 :: skipn 1 junk).
    { rewrite Nat2Z.id, upd_firstn_skipn by (rewrite length_app, zb_length; lia).
      rewrite firstn_app, skipn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite (firstn_all2 (zb wr)) by (rewrite zb_length; lia).
      rewrite (skipn_all2 (zb wr)) by (rewrite zb_length; lia).
      replace (Datatypes.S (length wr) - length wr)%nat with 1%nat by lia. reflexivity. }
    rewrite EU in DST. clear EU.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 9 zs. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { first [exact DST | lazymatch type of DST with ?t => idtac "DST:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail]. }
    split; assumption.
  Qed.
  End Sz15.
  Lemma sn_D : ltac:(let t := eval cbv delta [sn_D__stmt] in sn_D__stmt in exact t).
  Proof using CAP0 DF DN FB FS_ LO RNG SPB SPD SPF SPS. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s0 s1 s2 s3 s4 s5 m wr junk fj wposv wbasev. ltac2:(SecDiet.SzSec.closeP 'sn_D__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sn_write_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
    rw_cells usegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells usegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells usegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells usegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells usegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    bytes_at usegs m B (zb o) -> bytes_at usegs m S (zb s) ->
    rw_cells usegs m D [CB dn (zb wr ++ junk)] ->
    stk usegs m lo q -> mem_inv usegs m ->
    evt usegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D cap B S bufp lo o s wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom usegs)).
  Section Sz16.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk : ltac2:(SecDiet.SzSec.tyM 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO RNG SPB SPCK SPD SPF SPS. pin_using (fun (BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO RNG SPB SPCK SPD SPF SPS : unit) => tt).
 intros WL -> -> -> WPOS WBASE BUFC CKP CKC BO BS DST ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. pose proof (zb_length s) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o)%Z) by (unfold zlength; lia). assert (NNs : (0 <= zlength s)%Z) by (unfold zlength; lia).
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_;
    stash SPD; stash SPCK; stash SPF; stash SPB; stash SPS.
    set (W := [(q - 64, q); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z).
    assert (SUB1 : sub_fp [(q - 64, q)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; tauto).
    assert (SUB2 : sub_fp [(CK, CK + 16); (D, D + Z.of_nat dn)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; tauto).
    (* [comment removed for export] *)
    eapply evt_cut. { eapply (sn_A t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m (zlength wr)); first [exact WL | eassumption]. }
    cbv beta. intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & fj & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (T1 : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= lo \/ q <= A)%Z -> rw_cells usegs m1 A cs).
    { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU1 | exact WM1 | cbn [disjoint_from]; lia]. }
    assert (TB1 : forall A bs, bytes_at usegs m A bs -> (A + Z.of_nat (length bs) <= lo \/ q <= A)%Z -> bytes_at usegs m1 A bs).
    { intros A bs H HA. eapply bytes_at_transport; [exact H | exact MU1 | cbn [disjoint_from]; lia]. }
    pose proof (T1 _ _ WPOS ltac:(cbn; unfold hide in SPF; lia)) as WPOS1. pose proof (T1 _ _ WBASE ltac:(cbn; unfold hide in SPF; lia)) as WBASE1.
    pose proof (T1 _ _ BUFC ltac:(cbn; unfold hide in SPF; lia)) as BUFC1. pose proof (T1 _ _ CKP ltac:(cbn; unfold hide in SPF; lia)) as CKP1.
    pose proof (T1 _ _ CKC ltac:(cbn; unfold hide in SPCK; lia)) as CKC1. pose proof (T1 _ _ DST ltac:(cbn; unfold hide in SPD; lia)) as DST1.
    pose proof (TB1 _ _ BO ltac:(rewrite LZo; unfold hide in SPB; unfold zlength in SPB; lia)) as BO1.
    pose proof (TB1 _ _ BS ltac:(rewrite LZs; unfold hide in SPS; unfold zlength in SPS; lia)) as BS1.
    clear T1 TB1 WPOS WBASE BUFC CKP CKC DST BO BS MI.
    (* [comment removed for export] *)
    set (k1 := Z.min (cap - zlength wr) (zlength o)).
    assert (K1R : (0 <= k1 <= zlength o /\ zlength wr + k1 <= cap)%Z) by (subst k1; lia).
    eapply evt_cut. { eapply (sn_B u0 u1 u2 _ a3 a4 a5 a6 a7 u3 u4 u5 u6 m1 wr junk k1); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms2 (x1 & v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & CKC2 & DST2 & BO2).
    assert (T2 : forall A cs, rw_cells usegs m1 A cs -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells usegs m2 A cs).
    { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    pose proof (T2 _ _ WPOS1 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS2.
    pose proof (T2 _ _ WBASE1 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE2.
    pose proof (T2 _ _ BUFC1 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC2.
    pose proof (T2 _ _ FR1 ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR2.
    assert (BS2 : bytes_at usegs m2 S (zb s)).
    { eapply bytes_at_transport; [exact BS1 | exact MU2 | cbn [disjoint_from]; rewrite LZs; unfold hide in CKS, DS; unfold zlength in CKS, DS; lia]. }
    assert (ST2 : stk usegs m2 lo (q + -64)).
    { eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; unfold hide in SPCK, SPD; lia]. }
    clear T2 WPOS1 WBASE1 BUFC1 FR1 BS1 ST1 CKC1 DST1 CKP1 MI1.
    (* [comment removed for export] *)
    set (wr1 := wr ++ firstn (Z.to_nat k1) o) in *.
    assert (L1 : zlength wr1 = (zlength wr + k1)%Z) by (subst wr1; apply zlength_app_firstn; lia).
    replace (D + zlength wr + k1)%Z with (D + zlength wr1)%Z in * by lia.
    replace (cap - zlength wr - k1)%Z with (cap - zlength wr1)%Z in * by lia.
    set (k2 := Z.min (cap - zlength wr1) (zlength s)).
    eapply evt_cut. { eapply (sn_C x1 v0 v1 v2 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 _ m2 wr1 (skipn (Z.to_nat k1) junk)); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms3 (x1' & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & s3v & m3 & -> & MU3 & WM3 & MI3 & CKC3 & DST3 & BS3).
    fold k2 in CKC3. fold k2 in DST3. fold k2.
    assert (K2R : (0 <= k2 <= zlength s /\ zlength wr1 + k2 <= cap)%Z) by (subst k2; lia).
    assert (T3 : forall A cs, rw_cells usegs m2 A cs -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells usegs m3 A cs).
    { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MU3 | exact WM3 | cbn [disjoint_from]; lia]. }
    pose proof (T3 _ _ WPOS2 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS3.
    pose proof (T3 _ _ WBASE2 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE3.
    pose proof (T3 _ _ BUFC2 ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC3.
    pose proof (T3 _ _ FR2 ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR3.
    assert (BO3 : bytes_at usegs m3 B (zb o)).
    { eapply bytes_at_transport; [exact BO2 | exact MU3 | cbn [disjoint_from]; rewrite LZo; unfold hide in CKB, DB; unfold zlength in CKB, DB; lia]. }
    assert (ST3 : stk usegs m3 lo (q + -64)).
    { eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 | cbn [disjoint_from]; unfold hide in SPCK, SPD; lia]. }
    (* [comment removed for export] *)
    assert (MU13 : munch W m m3).
    { eapply munch_trans; [apply (munch_weaken _ _ _ _ SUB1); exact MU1|].
      eapply munch_trans; apply (munch_weaken _ _ _ _ SUB2); [exact MU2 | exact MU3]. }
    assert (WM13 : wmono usegs m m3) by (eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]).
    clear T3 WPOS2 WBASE2 BUFC2 FR2 BO2 ST2 CKC2 DST2 MU1 MU2 MU3 WM1 WM2 WM3 MI2.
    (* [comment removed for export] *)
    set (wr2 := wr1 ++ firstn (Z.to_nat k2) s) in *.
    assert (L2 : zlength wr2 = (zlength wr1 + k2)%Z) by (subst wr2; apply zlength_app_firstn; lia).
    replace (D + zlength wr1 + k2)%Z with (D + zlength wr2)%Z in * by lia.
    replace (cap - zlength wr1 - k2)%Z with (cap - zlength wr2)%Z in * by lia.
    eapply evt_cut. { eapply (sn_D x1' w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 s3v _ s0 s1 s2 s3 s4 s5 m3 wr2); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms4 (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & DST4 & WPOS4 & WBASE4).
    unfold WD in MU4.
    assert (SUB4 : sub_fp [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; (keep_hyps sp Fp CK D cap B S bufp o s dn wr x H; tauto)).
    assert (MU14 : munch W m m4) by (eapply munch_trans; [exact MU13 | apply (munch_weaken _ _ _ _ SUB4); exact MU4]).
    assert (WM14 : wmono usegs m m4) by (eapply wmono_trans; [exact WM13 | exact WM4]).
    assert (CKC4 : rw_cells usegs m4 CK [C8 (Z_to_bv 64 (D + zlength wr2)); C8 (Z_to_bv 64 (cap - zlength wr2))]).
    { eapply rw_cells_transport; [exact CKC3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; unfold hide in SPCK, DCK, CKF; lia]. }
    assert (BO4 : bytes_at usegs m4 B (zb o)).
    { eapply bytes_at_transport; [exact BO3 | exact MU4 | cbn [disjoint_from]; rewrite LZo; unfold hide in SPB, DB, FB; unfold zlength in SPB, DB, FB; lia]. }
    assert (BS4 : bytes_at usegs m4 S (zb s)).
    { eapply bytes_at_transport; [exact BS3 | exact MU4 | cbn [disjoint_from]; rewrite LZs; unfold hide in SPS, DS, FS_; unfold zlength in SPS, DS, FS_; lia]. }
    subst W.
    (* [comment removed for export] *)
    assert (EW : wr2 = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s)).
    { subst wr2 wr1. rewrite <- app_assoc. f_equal. subst k1 k2. rewrite L1. unfold zlength.
      rewrite <- (firstn_two_copies o s (Z.to_nat (cap - Z.of_nat (length wr)))). f_equal; [f_equal; (keep_hyps sp cap o s dn wr junk; lia)|]. f_equal. (keep_hyps sp cap o s dn wr junk; lia). }
    apply evt_done. unfold sn_write_post. cbv zeta. rewrite <- EW.
    exists y0, y1, y2, d1, d2, d3, d4, d5, d6, d7, y3, y4, y5, y6, m4, (skipn 1 (skipn (Z.to_nat k2) (skipn (Z.to_nat k1) junk))).
    split; [reflexivity|]. split; [exact MU14|]. split; [exact WM14|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact CKC4|]. split; [exact DST4|]. split; [exact WPOS4|]. split; [exact WBASE4|].
    split; [exact BO4|]. split; [exact BS4|]. lia.
  Qed.
  End Sz16.
  Theorem sn_write_spec : ltac:(let t := eval cbv delta [sn_write_spec__stmt] in sn_write_spec__stmt in exact t).
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO RNG SPB SPCK SPD SPF SPS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk. ltac2:(SecDiet.SzSec.closeP 'sn_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnWrite.
End TwB.
End F_sn_write.

(* [comment removed for export] *)
Module F_fwritex_sn.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).

Definition FWRITEX : Z := 0x1b724.

(* [comment removed for export] *)
Definition snfile_cells (wend wpos wbase bufp bufsize : Z) (md : word) (CK : Z) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 bufp); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 CK);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Lemma snfile_cells_size : forall wend wpos wbase bufp bufsize md CK, cells_size (snfile_cells wend wpos wbase bufp bufsize md CK) = 232%nat.
Proof. reflexivity. Qed.

Lemma rwc_eqA : forall m A A' cs, rw_cells ssegs m A cs -> A = A' -> rw_cells ssegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

(* [comment removed for export] *)
Definition snfile_split__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK,
  rw_cells ssegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  rw_cells ssegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK))
  /\ rw_cells ssegs m (Fp + 40) [C8 (Z_to_bv 64 wpos)]
  /\ rw_cells ssegs m (Fp + 48) [C8 (Z_to_bv 64 0)]
  /\ rw_cells ssegs m (Fp + 56) [C8 (Z_to_bv 64 wbase)]
  /\ rw_cells ssegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
  /\ rw_cells ssegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)]
  /\ rw_cells ssegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK)))
  /\ rw_cells ssegs m (Fp + 152) [C8 (Z_to_bv 64 CK)]
  /\ rw_cells ssegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)].
Section Sz3.
Variables m Fp wend wpos wbase bufp bufsize md CK : ltac2:(SecDiet.SzSec.tyM 'snfile_split__stmt "vvvvvvvvv" @m).
#[using="Type"] Lemma snfile_split__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_split__stmt "vvvvvvvvv").
Proof.
  intros H.
 unfold snfile_cells in *. cbn [firstn skipn].
  apply (proj1 (rw_cells_app ssegs _ _ [_;_;_;_;_;_] _)) in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H40 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H48 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H56 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_;_;_] _)) in H. destruct H as [H64 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H88 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H96 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in H. destruct H as [H152 H160]. cbn [cells_size csize Nat.add app] in H160.
  split; [exact H0|]. split; [eapply rwc_eqA; [exact H40| cbn; lia]|]. split; [eapply rwc_eqA; [exact H48| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H56| cbn; lia]|]. split; [eapply rwc_eqA; [exact H64| cbn; lia]|]. split; [eapply rwc_eqA; [exact H88| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H96| cbn; lia]|]. split; [eapply rwc_eqA; [exact H152| cbn; lia]|]. eapply rwc_eqA; [exact H160| cbn; lia].
Qed.
End Sz3.
Lemma snfile_split : ltac:(let t := eval cbv delta [snfile_split__stmt] in snfile_split__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK. ltac2:(SecDiet.SzSec.closeP 'snfile_split__body "vvvvvvvvv"). Qed.

Definition snfile_join__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK wpos' wbase',
  rw_cells ssegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK)) ->
  rw_cells ssegs m (Fp + 40) [C8 (Z_to_bv 64 wpos')] ->
  rw_cells ssegs m (Fp + 48) [C8 (Z_to_bv 64 0)] ->
  rw_cells ssegs m (Fp + 56) [C8 (Z_to_bv 64 wbase')] ->
  rw_cells ssegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)] ->
  rw_cells ssegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells ssegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK))) ->
  rw_cells ssegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells ssegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)] ->
  rw_cells ssegs m Fp (snfile_cells wend wpos' wbase' bufp bufsize md CK).
Section Sz4.
Variables m Fp wend wpos wbase bufp bufsize md CK wpos' wbase' : ltac2:(SecDiet.SzSec.tyM 'snfile_join__stmt "vvvvvvvvvvv" @m).
#[using="Type"] Lemma snfile_join__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_join__stmt "vvvvvvvvvvv").
Proof.
  intros H0 H40 H48 H56 H64 H88 H96 H152 H160.
 unfold snfile_cells in *. cbn [firstn skipn] in *.
  change (rw_cells ssegs m Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wend)]
     ++ [C8 (Z_to_bv 64 wpos')] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 wbase')] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 bufp)] ++ [C8 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 CK)] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)])).
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact H0|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H40|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H48|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H56|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H64|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H88|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H96|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact H152|lia]|]; cbn [cells_size csize Nat.add].
  eapply rwc_eqA; [exact H160|lia].
Qed.
End Sz4.
Lemma snfile_join : ltac:(let t := eval cbv delta [snfile_join__stmt] in snfile_join__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK wpos' wbase'. ltac2:(SecDiet.SzSec.closeP 'snfile_join__body "vvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition fwritex_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp Bi CK D cap S lo : Z) (md : word) (o bs wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (wr' o' : list Z) (jb' jd' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength bs)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' Fp (snfile_cells (Bi + 80) (Bi + zlength o') Bi Bi 80 md CK)
    /\ rw_cells ssegs m' Bi [CB 80 (zb o' ++ jb')]
    /\ rw_cells ssegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells ssegs m' D [CB dn (zb wr' ++ jd')]
    /\ bytes_at ssegs m' S (zb bs)
    /\ ((wr' = wr /\ o' = o ++ bs) \/ (wr' = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs) /\ o' = []))
    /\ (zlength wr' <= cap)%Z.

Section FwritexSn.
  Variables (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp Bi CK D cap S lo : Z) (md : word) (o bs : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HSL : (zlength bs < 2^31)%Z.
  Hypothesis RNG : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < Bi /\ Bi + 80 <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength bs <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (Bi + 80 <= D \/ D + Z.of_nat dn <= Bi)%Z.
  Hypothesis DS : (S + zlength bs <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 232 <= D \/ D + Z.of_nat dn <= Fp)%Z.
  Hypothesis CKF : (CK + 16 <= Fp \/ Fp + 232 <= CK)%Z.
  Hypothesis CKB : (Bi + 80 <= CK \/ CK + 16 <= Bi)%Z.
  Hypothesis CKS : (S + zlength bs <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (Bi + 80 <= Fp \/ Fp + 232 <= Bi)%Z.
  Hypothesis FS_ : (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z.
  Hypothesis BS_ : (S + zlength bs <= Bi \/ Bi + 80 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (q <= CK)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPB : (q <= Bi)%Z.
  Hypothesis SPS : (S + zlength bs <= lo \/ q <= S)%Z.

  Definition fwritex_sn_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (jb jd : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength bs) -> a2 = Z_to_bv 64 Fp ->
    rw_cells ssegs m Fp (snfile_cells (Bi + 80) (Bi + zlength o) Bi Bi 80 md CK) ->
    rw_cells ssegs m Bi [CB 80 (zb o ++ jb)] ->
    rw_cells ssegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    rw_cells ssegs m D [CB dn (zb wr ++ jd)] ->
    bytes_at ssegs m S (zb bs) ->
    stk ssegs m lo q -> mem_inv ssegs m ->
    evt ssegs (fwritex_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp Bi CK D cap S lo md o bs wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX) fc None m (seg_rom ssegs)).
  Section Sz5.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd : ltac2:(SecDiet.SzSec.tyM 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fwritex_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO RNG SPB SPCK SPD SPF SPS. pin_using (fun (BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO RNG SPB SPCK SPD SPF SPS : unit) => tt).
    intros WL -> -> -> FC IB CKC DST SRC ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o <= 80)%Z) by (unfold zlength in *; lia). assert (NNs : (0 <= zlength bs)%Z) by (unfold zlength; lia).
    pose proof SRC as SRC0. change (hide (bytes_at ssegs m S (zb bs))) in SRC0.
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_; stash BS_.
    pose proof (munch_refl [(q - 64, q); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    unfold FWRITEX. subst q. unfold snfile_cells in FC. unfold zlength in *.
    carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (Bi + 80 - (Bi + Z.of_nat (length o)))%Z with (80 - Z.of_nat (length o))%Z by lia.
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) first [if_lit | brf K2; [|exfalso; revert K2; cbn; rewrite ?unsigned_lit by lia; cbn; lia]].
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold hide in DB, CKB, FB, BS_. stash SPD; stash SPS.
      destruct (dest_carve _ _ _ _ _ (length bs) IB ltac:(lia)) as (DW & DK & DR). clear IB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [ eapply memcpy_callv with (Dst := (Bi + Z.of_nat (length o))%Z) (Src := S) (N := Z.of_nat (length bs)) (src := zb bs) (junk := firstn (length bs) jb);
          [ | rewrite LZs; lia | rewrite Nat2Z.id; exact DK | lia | lia | lia | lia | ]
        | post_call ssegs mm ] end.
      { unfold hide in SRC0, FS_, CKS, DS, SPS.
        lazymatch goal with |- bytes_at _ ?mm S _ => match goal with MUx : munch _ m mm |- _ =>
          eapply bytes_at_transport; [exact SRC0 | exact MUx | cbn [disjoint_from]; rewrite LZs; lia] end end. }
      { assumption. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with DKm : rw_cells _ mm (Bi + Z.of_nat (length o))%Z [CB _ (zb bs)], DRm : rw_cells _ mm (Bi + Z.of_nat (length o) + _)%Z _ , DWm : rw_cells _ mm Bi _ |- _ =>
          rewrite Nat2Z.id in DKm;
          pose proof (dest_join mm Bi 80 o bs jb (length bs) DWm DKm DRm ltac:(lia) ltac:(lia)) as IB;
          clear DWm DKm DRm end end.
      (* [comment removed for export] *)
      stash DB; stash CKB; stash BS_. unfold hide in FB, CKF, DF, FS_.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      do 9 zs. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold fwritex_sn_post.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_l; reflexivity|].
      split. { eapply munch_weaken; [|eassumption]. unfold sub_fp; cbn [outside]. clear -LJB NNo NNs K1. intros; lia. }
      split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split. { unfold snfile_cells, zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc.
               match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "FC:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail] end. }
      split; [exact IB|].
      split. { match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split. { match goal with H : rw_cells _ _ D _ |- _ => exact H end. }
      split. { match goal with H : bytes_at _ _ S (zb bs) |- _ => exact H end. }
      split; [left; split; reflexivity|]. unfold zlength. clear -WL. lia.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *)
      do 7 zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [lia | reflexivity]).
      release_frame FR ST (bv_unsigned sp).
      destruct (snfile_split _ _ _ _ _ _ _ _ _ ltac:(unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end))
        as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160).
      match goal with H : rw_cells _ ?mm Fp (_ :: _ :: _ :: _) |- _ => clear H end.
      unfold hide in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with IBc : rw_cells _ mm Bi [CB 80 _] |- _ =>
          pose proof (rw_cells_bytes_at _ _ _ _ IBc) as BO; cbn [cells_bytes cbytes app] in BO; rewrite app_nil_r in BO;
          apply bytes_at_app in BO; destruct BO as [BO _] end end.
      eapply evt_mono.
      { eapply (sn_write_spec ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Fp CK D cap Bi S Bi lo o bs dn) with (wr := wr) (junk := jd);
          fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption | unfold zlength in *; lia | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
      cbv beta. intros ms' P. unfold sn_write_post in P. cbv zeta in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & junk' & -> & MUc & WMc & MIc & STc & CKc & DSTc & F40c & F56c & BOc & BSc & LE).
      unfold fwritex_sn_post.
      lazymatch type of MUc with munch ?Wc ?m1 _ =>
        assert (T : forall A cs, rw_cells ssegs m1 A cs ->
                  (bv_unsigned sp <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z ->
                  (A + Z.of_nat (cells_size cs) <= Fp + 40 \/ Fp + 48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fp + 56 \/ Fp + 64 <= A)%Z ->
                  rw_cells ssegs m' A cs)
          by (intros A cs HH H1 H2 H3 H4 H5; eapply rw_cells_transport; [exact HH | exact MUc | exact WMc | cbn [disjoint_from]; lia]) end.
      pose proof (T _ _ G0 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G0'.
      pose proof (T _ _ G48 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G48'.
      pose proof (T _ _ G64 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G64'.
      pose proof (T _ _ G88 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G88'.
      pose proof (T _ _ G96 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G96'.
      pose proof (T _ _ G152 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G152'.
      pose proof (T _ _ G160 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G160'.
      match goal with H : rw_cells _ _ Bi [CB 80 _] |- _ =>
        pose proof (T _ _ H ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as IB' end.
      pose proof (snfile_join _ _ _ _ _ _ _ _ _ _ _ G0' F40c G48' F56c G64' G88' G96' G152' G160') as FC'.
      do 15 eexists. exists (wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs)), (@nil Z), (zb o ++ jb), (Z_to_bv 8 0 :: junk').
      split; [reflexivity|].
      split. { lazymatch type of MUc with munch _ ?m1 _ =>
                 eapply munch_trans; [eapply munch_weaken; [|match goal with H : munch _ m m1 |- _ => exact H end] | eapply munch_weaken; [|exact MUc]] end.
               all: unfold sub_fp; cbn [outside]; clear -LJB NNo NNs; intros; lia. }
      split. { eapply wmono_trans; [|exact WMc]. assumption. }
      split; [exact MIc|]. split; [exact STc|].
      split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r. exact FC'. }
      split. { cbn [zb map app]. exact IB'. }
      split; [exact CKc|]. split; [exact DSTc|]. split; [exact BSc|].
      split; [right; split; reflexivity|]. exact LE.
  Qed.
  End Sz5.
  Theorem fwritex_sn_spec : ltac:(let t := eval cbv delta [fwritex_sn_spec__stmt] in fwritex_sn_spec__stmt in exact t).
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO RNG SPB SPCK SPD SPF SPS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd. ltac2:(SecDiet.SzSec.closeP 'fwritex_sn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FwritexSn.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).

Definition FWRITEX : Z := 0x1bee4.

(* [comment removed for export] *)
Definition snfile_cells (wend wpos wbase bufp bufsize : Z) (md : word) (CK : Z) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 bufp); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 CK);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Lemma snfile_cells_size : forall wend wpos wbase bufp bufsize md CK, cells_size (snfile_cells wend wpos wbase bufp bufsize md CK) = 232%nat.
Proof. reflexivity. Qed.

Lemma rwc_eqA : forall m A A' cs, rw_cells usegs m A cs -> A = A' -> rw_cells usegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

(* [comment removed for export] *)
Definition snfile_split__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK,
  rw_cells usegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  rw_cells usegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK))
  /\ rw_cells usegs m (Fp + 40) [C8 (Z_to_bv 64 wpos)]
  /\ rw_cells usegs m (Fp + 48) [C8 (Z_to_bv 64 0)]
  /\ rw_cells usegs m (Fp + 56) [C8 (Z_to_bv 64 wbase)]
  /\ rw_cells usegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
  /\ rw_cells usegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)]
  /\ rw_cells usegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK)))
  /\ rw_cells usegs m (Fp + 152) [C8 (Z_to_bv 64 CK)]
  /\ rw_cells usegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)].
Section Sz3.
Variables m Fp wend wpos wbase bufp bufsize md CK : ltac2:(SecDiet.SzSec.tyM 'snfile_split__stmt "vvvvvvvvv" @m).
#[using="Type"] Lemma snfile_split__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_split__stmt "vvvvvvvvv").
Proof.
  intros H.
 unfold snfile_cells in *. cbn [firstn skipn].
  apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_;_;_] _)) in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H40 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H48 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H56 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_;_;_] _)) in H. destruct H as [H64 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H88 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H96 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in H. destruct H as [H152 H160]. cbn [cells_size csize Nat.add app] in H160.
  split; [exact H0|]. split; [eapply rwc_eqA; [exact H40| cbn; lia]|]. split; [eapply rwc_eqA; [exact H48| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H56| cbn; lia]|]. split; [eapply rwc_eqA; [exact H64| cbn; lia]|]. split; [eapply rwc_eqA; [exact H88| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H96| cbn; lia]|]. split; [eapply rwc_eqA; [exact H152| cbn; lia]|]. eapply rwc_eqA; [exact H160| cbn; lia].
Qed.
End Sz3.
Lemma snfile_split : ltac:(let t := eval cbv delta [snfile_split__stmt] in snfile_split__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK. ltac2:(SecDiet.SzSec.closeP 'snfile_split__body "vvvvvvvvv"). Qed.

Definition snfile_join__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK wpos' wbase',
  rw_cells usegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK)) ->
  rw_cells usegs m (Fp + 40) [C8 (Z_to_bv 64 wpos')] ->
  rw_cells usegs m (Fp + 48) [C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m (Fp + 56) [C8 (Z_to_bv 64 wbase')] ->
  rw_cells usegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells usegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK))) ->
  rw_cells usegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells usegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)] ->
  rw_cells usegs m Fp (snfile_cells wend wpos' wbase' bufp bufsize md CK).
Section Sz4.
Variables m Fp wend wpos wbase bufp bufsize md CK wpos' wbase' : ltac2:(SecDiet.SzSec.tyM 'snfile_join__stmt "vvvvvvvvvvv" @m).
#[using="Type"] Lemma snfile_join__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_join__stmt "vvvvvvvvvvv").
Proof.
 intros H0 H40 H48 H56 H64 H88 H96 H152 H160. unfold snfile_cells in *. cbn [firstn skipn] in *.
  change (rw_cells usegs m Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wend)]
     ++ [C8 (Z_to_bv 64 wpos')] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 wbase')] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 bufp)] ++ [C8 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 CK)] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)])).
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact H0|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H40|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H48|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H56|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H64|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H88|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H96|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact H152|lia]|]; cbn [cells_size csize Nat.add].
  eapply rwc_eqA; [exact H160|lia].
Qed.
End Sz4.
Lemma snfile_join : ltac:(let t := eval cbv delta [snfile_join__stmt] in snfile_join__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK wpos' wbase'. ltac2:(SecDiet.SzSec.closeP 'snfile_join__body "vvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition fwritex_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp Bi CK D cap S lo : Z) (md : word) (o bs wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (wr' o' : list Z) (jb' jd' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength bs)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' Fp (snfile_cells (Bi + 80) (Bi + zlength o') Bi Bi 80 md CK)
    /\ rw_cells usegs m' Bi [CB 80 (zb o' ++ jb')]
    /\ rw_cells usegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells usegs m' D [CB dn (zb wr' ++ jd')]
    /\ bytes_at usegs m' S (zb bs)
    /\ ((wr' = wr /\ o' = o ++ bs) \/ (wr' = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs) /\ o' = []))
    /\ (zlength wr' <= cap)%Z.

Section FwritexSn.
  Variables (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp Bi CK D cap S lo : Z) (md : word) (o bs : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HSL : (zlength bs < 2^31)%Z.
  Hypothesis RNG : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < Bi /\ Bi + 80 <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength bs <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (Bi + 80 <= D \/ D + Z.of_nat dn <= Bi)%Z.
  Hypothesis DS : (S + zlength bs <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 232 <= D \/ D + Z.of_nat dn <= Fp)%Z.
  Hypothesis CKF : (CK + 16 <= Fp \/ Fp + 232 <= CK)%Z.
  Hypothesis CKB : (Bi + 80 <= CK \/ CK + 16 <= Bi)%Z.
  Hypothesis CKS : (S + zlength bs <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (Bi + 80 <= Fp \/ Fp + 232 <= Bi)%Z.
  Hypothesis FS_ : (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z.
  Hypothesis BS_ : (S + zlength bs <= Bi \/ Bi + 80 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (q <= CK)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPB : (q <= Bi)%Z.
  Hypothesis SPS : (S + zlength bs <= lo \/ q <= S)%Z.

  Definition fwritex_sn_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (jb jd : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength bs) -> a2 = Z_to_bv 64 Fp ->
    rw_cells usegs m Fp (snfile_cells (Bi + 80) (Bi + zlength o) Bi Bi 80 md CK) ->
    rw_cells usegs m Bi [CB 80 (zb o ++ jb)] ->
    rw_cells usegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    rw_cells usegs m D [CB dn (zb wr ++ jd)] ->
    bytes_at usegs m S (zb bs) ->
    stk usegs m lo q -> mem_inv usegs m ->
    evt usegs (fwritex_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp Bi CK D cap S lo md o bs wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX) fc None m (seg_rom usegs)).
  Section Sz5.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd : ltac2:(SecDiet.SzSec.tyM 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fwritex_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO RNG SPB SPCK SPD SPF SPS. pin_using (fun (BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO RNG SPB SPCK SPD SPF SPS : unit) => tt).
 intros WL -> -> -> FC IB CKC DST SRC ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o <= 80)%Z) by (unfold zlength in *; lia). assert (NNs : (0 <= zlength bs)%Z) by (unfold zlength; lia).
    pose proof SRC as SRC0. change (hide (bytes_at usegs m S (zb bs))) in SRC0.
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_; stash BS_.
    pose proof (munch_refl [(q - 64, q); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    unfold FWRITEX. subst q. unfold snfile_cells in FC. unfold zlength in *.
    carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (Bi + 80 - (Bi + Z.of_nat (length o)))%Z with (80 - Z.of_nat (length o))%Z by lia.
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) first [if_lit | brf K2; [|exfalso; revert K2; cbn; rewrite ?unsigned_lit by lia; cbn; lia]].
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold hide in DB, CKB, FB, BS_. stash SPD; stash SPS.
      destruct (dest_carve _ _ _ _ _ (length bs) IB ltac:(lia)) as (DW & DK & DR). clear IB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [ eapply memcpy_callv with (Dst := (Bi + Z.of_nat (length o))%Z) (Src := S) (N := Z.of_nat (length bs)) (src := zb bs) (junk := firstn (length bs) jb);
          [ | rewrite LZs; lia | rewrite Nat2Z.id; exact DK | lia | lia | lia | lia | ]
        | post_call usegs mm ] end.
      { unfold hide in SRC0, FS_, CKS, DS, SPS.
        lazymatch goal with |- bytes_at _ ?mm S _ => match goal with MUx : munch _ m mm |- _ =>
          eapply bytes_at_transport; [exact SRC0 | exact MUx | cbn [disjoint_from]; rewrite LZs; lia] end end. }
      { assumption. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with DKm : rw_cells _ mm (Bi + Z.of_nat (length o))%Z [CB _ (zb bs)], DRm : rw_cells _ mm (Bi + Z.of_nat (length o) + _)%Z _ , DWm : rw_cells _ mm Bi _ |- _ =>
          rewrite Nat2Z.id in DKm;
          pose proof (dest_join mm Bi 80 o bs jb (length bs) DWm DKm DRm ltac:(lia) ltac:(lia)) as IB;
          clear DWm DKm DRm end end.
      (* [comment removed for export] *)
      stash DB; stash CKB; stash BS_. unfold hide in FB, CKF, DF, FS_.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      do 9 zs. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold fwritex_sn_post.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_l; reflexivity|].
      split. { eapply munch_weaken; [|eassumption]. unfold sub_fp; cbn [outside]. clear -LJB NNo NNs K1. intros; lia. }
      split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split. { unfold snfile_cells, zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc.
               match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "FC:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail] end. }
      split; [exact IB|].
      split. { match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split. { match goal with H : rw_cells _ _ D _ |- _ => exact H end. }
      split. { match goal with H : bytes_at _ _ S (zb bs) |- _ => exact H end. }
      split; [left; split; reflexivity|]. unfold zlength. clear -WL. lia.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *)
      do 7 zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [lia | reflexivity]).
      release_frame FR ST (bv_unsigned sp).
      destruct (snfile_split _ _ _ _ _ _ _ _ _ ltac:(unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end))
        as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160).
      match goal with H : rw_cells _ ?mm Fp (_ :: _ :: _ :: _) |- _ => clear H end.
      unfold hide in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with IBc : rw_cells _ mm Bi [CB 80 _] |- _ =>
          pose proof (rw_cells_bytes_at _ _ _ _ IBc) as BO; cbn [cells_bytes cbytes app] in BO; rewrite app_nil_r in BO;
          apply bytes_at_app in BO; destruct BO as [BO _] end end.
      eapply evt_mono.
      { eapply (sn_write_spec ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Fp CK D cap Bi S Bi lo o bs dn) with (wr := wr) (junk := jd);
          fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption | unfold zlength in *; lia | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
      cbv beta. intros ms' P. unfold sn_write_post in P. cbv zeta in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & junk' & -> & MUc & WMc & MIc & STc & CKc & DSTc & F40c & F56c & BOc & BSc & LE).
      unfold fwritex_sn_post.
      lazymatch type of MUc with munch ?Wc ?m1 _ =>
        assert (T : forall A cs, rw_cells usegs m1 A cs ->
                  (bv_unsigned sp <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z ->
                  (A + Z.of_nat (cells_size cs) <= Fp + 40 \/ Fp + 48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fp + 56 \/ Fp + 64 <= A)%Z ->
                  rw_cells usegs m' A cs)
          by (intros A cs HH H1 H2 H3 H4 H5; eapply rw_cells_transport; [exact HH | exact MUc | exact WMc | cbn [disjoint_from]; lia]) end.
      pose proof (T _ _ G0 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G0'.
      pose proof (T _ _ G48 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G48'.
      pose proof (T _ _ G64 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G64'.
      pose proof (T _ _ G88 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G88'.
      pose proof (T _ _ G96 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G96'.
      pose proof (T _ _ G152 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G152'.
      pose proof (T _ _ G160 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G160'.
      match goal with H : rw_cells _ _ Bi [CB 80 _] |- _ =>
        pose proof (T _ _ H ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as IB' end.
      pose proof (snfile_join _ _ _ _ _ _ _ _ _ _ _ G0' F40c G48' F56c G64' G88' G96' G152' G160') as FC'.
      do 15 eexists. exists (wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs)), (@nil Z), (zb o ++ jb), (Z_to_bv 8 0 :: junk').
      split; [reflexivity|].
      split. { lazymatch type of MUc with munch _ ?m1 _ =>
                 eapply munch_trans; [eapply munch_weaken; [|match goal with H : munch _ m m1 |- _ => exact H end] | eapply munch_weaken; [|exact MUc]] end.
               all: unfold sub_fp; cbn [outside]; clear -LJB NNo NNs; intros; lia. }
      split. { eapply wmono_trans; [|exact WMc]. assumption. }
      split; [exact MIc|]. split; [exact STc|].
      split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r. exact FC'. }
      split. { cbn [zb map app]. exact IB'. }
      split; [exact CKc|]. split; [exact DSTc|]. split; [exact BSc|].
      split; [right; split; reflexivity|]. exact LE.
  Qed.
  End Sz5.
  Theorem fwritex_sn_spec : ltac:(let t := eval cbv delta [fwritex_sn_spec__stmt] in fwritex_sn_spec__stmt in exact t).
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO RNG SPB SPCK SPD SPF SPS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd. ltac2:(SecDiet.SzSec.closeP 'fwritex_sn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FwritexSn.
End TwB.
End F_fwritex_sn.

(* [comment removed for export] *)
Module Printf_snsink.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr SysStep ITree Nodes Decode ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition SN_FS : Z := 600.      (* [comment removed for export] *)
Definition SN_FOFF : Z := 352.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma firstn_cap_app : forall cap (P X : list Z),
  0 <= cap ->
  firstn (Z.to_nat cap) P ++ firstn (Z.to_nat (cap - zlength (firstn (Z.to_nat cap) P))) X = firstn (Z.to_nat cap) (P ++ X).
Proof.
  intros cap P X Hc. unfold zlength. rewrite firstn_app, length_firstn. f_equal. f_equal. lia.
Qed.

Section SnSink.
  Variables (Bi : Z) (md : word) (frest : list cell) (D cap : Z) (dn : nat).
  Let Ff := Bi + SN_FOFF.
  Let CK := Bi + SN_FOFF + 232.

  Definition SINK_sn (m : mem) (T : list Z) : Prop :=
    exists (P o : list Z) (jb jd : list byte) (wp cs cn : Z),
      let wr := firstn (Z.to_nat cap) P in
      T = P ++ o /\ (zlength o <= 80)
      /\ wp = Bi + zlength o /\ cs = D + zlength wr /\ cn = cap - zlength wr
      /\ rw_cells ssegs m Ff (snfile_cells (Bi + 80) wp Bi Bi 80 md CK)
      /\ rw_cells ssegs m Bi [CB 80 (zb o ++ jb)]
      /\ rw_cells ssegs m (Bi + 80) frest /\ cells_size frest = 272%nat
      /\ rw_cells ssegs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)]
      /\ rw_cells ssegs m D [CB dn (zb wr ++ jd)]
      /\ Z.of_nat dn = cap + 1 /\ 0 <= cap
      /\ 0x55000 <= Bi /\ Bi + SN_FS <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63
      /\ (D + Z.of_nat dn <= 0x10000 \/ 0x55000 <= D)
      /\ (Bi + SN_FS <= D \/ D + Z.of_nat dn <= Bi).

  Definition TOPOK_sn (sp : Z) : Prop := sp <= Bi.

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using CK Ff. pin_using (fun (CK Ff : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Definition sn_sink_frame__stmt : Prop := sink_frame_stmt Bi SN_FS D (Z.of_nat dn) SINK_sn.
  Section Sz3.
  Variables W m m' T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_frame__stmt "vvvv" @W).
  Lemma sn_sink_frame__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_frame__stmt "vvvv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS) MU WM D1 D2.
 cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    unfold SN_FS, SN_FOFF in *.
    exists P, o, jb, jd, wp, cs, cn. cbv zeta. split; [exact ET|]. split; [exact LO80|].
    split; [exact Ewp|]. split; [exact Ecs|]. split; [exact Ecn|].
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. rewrite snfile_cells_size.
             eapply Forall_disjoint_from; [exact D1 | subst Ff; lia | subst Ff; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact IB | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. rewrite FRL.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FRL|].
    split. { eapply rw_cells_transport; [exact CKC | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | subst CK; lia | subst CK; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact DST | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  Lemma sn_sink_frame : ltac:(let t := eval cbv delta [sn_sink_frame__stmt] in sn_sink_frame__stmt in exact t).
  Proof using Type. unfold sink_frame_stmt. intros W m m' T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_frame__body "vvvv"). Qed.

  Definition sn_sink_flags__stmt : Prop := sink_flags_stmt Ff SINK_sn.
  Section Sz4.
  Variables m T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_flags__stmt "vv" @m).
  Lemma sn_sink_flags__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_flags__stmt "vv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS).
 cbv zeta in HS.
    destruct HS as (_ & _ & _ & _ & _ & FC & _).
    exists (Z_to_bv 8 0). split; [|reflexivity].
    unfold snfile_cells in FC. apply (proj1 (rw_cells_app ssegs m Ff [C4 (Z_to_bv 64 0)] _)) in FC. destruct FC as [FC _].
    destruct FC as [[WF BY] WR]. split; [split|].
    - cbn. split; [reflexivity| exact I].
    - cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
      change (le4 (Z_to_bv 64 0)) with ([Z_to_bv 8 0] ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in BY.
      apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
    - cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A & B_ & C). split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
  Qed.
  End Sz4.
  Lemma sn_sink_flags : ltac:(let t := eval cbv delta [sn_sink_flags__stmt] in sn_sink_flags__stmt in exact t).
  Proof using Type. unfold sink_flags_stmt. intros m T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_flags__body "vv"). Qed.

  Lemma sn_topok : topok_stmt TOPOK_sn.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  (* [comment removed for export] *)
  Definition sn_out__stmt : Prop := out_stmt Bi SN_FS Ff D (Z.of_nat dn) SINK_sn TOPOK_sn OUT_app.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary : ltac2:(SecDiet.SzSec.tyM 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sn_out__body : ltac2:(SecDiet.SzSec.bodyP 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros HS SRC BYT LB Ha1 Ha2 ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5.
   (* [comment removed for export] *)
    destruct HS as (P & o & jb & jd & wp & cs & cn & HS). cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    subst wp cs cn.
    unfold TOPOK_sn, OUT_DEPTH, GLOBALS_TOP, SN_FS, SN_FOFF in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    assert (NNo : 0 <= zlength o) by (unfold zlength; lia).
    assert (WL : 0 <= zlength (firstn (Z.to_nat cap) P) <= cap) by (unfold zlength; rewrite length_firstn; lia).
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    unfold implM, OUT_app. apply impl_ret_intro. cbn [epost fst snd].
    eapply evt_mono.
    { eapply (fwritex_sn_spec ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Ff Bi CK D cap S lo md o bs dn)
        with (wr := firstn (Z.to_nat cap) P) (jb := jb) (jd := jd); subst Ff CK; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact HDN | eassumption | lia | match goal with |- ?g => idtac "SNOUT-PREM:" g end; fail ]). }
    cbv beta. intros ms' PST. unfold fwritex_sn_post in PST.
    destruct PST as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & wr' & o' & jb' & jd'
                     & -> & MU & WM & MI' & ST' & FC' & IB' & CKC' & DST' & SRC' & CASES & LE').
    unfold out_post, SR. unfold SN_FS.
    exists x5, x6, x7, (Z_to_bv 64 (zlength bs)), b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. subst Ff CK. clear -LO HDN HCAP. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      pose proof (rw_CB_length _ _ _ _ IB') as LJB'. rewrite length_app, zb_length in LJB'.
      destruct CASES as [[-> ->] | [-> ->]].
      - exists P, (o ++ bs), jb', jd', (Bi + zlength (o ++ bs)), (D + zlength (firstn (Z.to_nat cap) P)), (cap - zlength (firstn (Z.to_nat cap) P)). cbv zeta. subst st.
        split; [rewrite app_assoc; reflexivity|]. split; [unfold zlength in *; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption.
      - exists (P ++ (o ++ bs)), (@nil Z), jb', jd'. eexists. eexists. eexists. cbv zeta. subst st.
        rewrite <- (firstn_cap_app cap P (o ++ bs)) by exact HCAP.
        split; [rewrite app_nil_r, app_assoc; reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption. }
    split.
    { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
      - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia].
      - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia]. }
    exact SRC'.
  Qed.
  End Sz6.
  Lemma sn_out : ltac:(let t := eval cbv delta [sn_out__stmt] in sn_out__stmt in exact t).
  Proof using Type. unfold out_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary. ltac2:(SecDiet.SzSec.closeP 'sn_out__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnSink.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition SN_FS : Z := 600.      (* [comment removed for export] *)
Definition SN_FOFF : Z := 352.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma firstn_cap_app : forall cap (P X : list Z),
  0 <= cap ->
  firstn (Z.to_nat cap) P ++ firstn (Z.to_nat (cap - zlength (firstn (Z.to_nat cap) P))) X = firstn (Z.to_nat cap) (P ++ X).
Proof.
  intros cap P X Hc. unfold zlength. rewrite firstn_app, length_firstn. f_equal. f_equal. lia.
Qed.

Section SnSink.
  Variables (Bi : Z) (md : word) (frest : list cell) (D cap : Z) (dn : nat).
  Let Ff := Bi + SN_FOFF.
  Let CK := Bi + SN_FOFF + 232.

  Definition SINK_sn (m : mem) (T : list Z) : Prop :=
    exists (P o : list Z) (jb jd : list byte) (wp cs cn : Z),
      let wr := firstn (Z.to_nat cap) P in
      T = P ++ o /\ (zlength o <= 80)
      /\ wp = Bi + zlength o /\ cs = D + zlength wr /\ cn = cap - zlength wr
      /\ rw_cells usegs m Ff (snfile_cells (Bi + 80) wp Bi Bi 80 md CK)
      /\ rw_cells usegs m Bi [CB 80 (zb o ++ jb)]
      /\ rw_cells usegs m (Bi + 80) frest /\ cells_size frest = 272%nat
      /\ rw_cells usegs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)]
      /\ rw_cells usegs m D [CB dn (zb wr ++ jd)]
      /\ Z.of_nat dn = cap + 1 /\ 0 <= cap
      /\ 0x56000 <= Bi /\ Bi + SN_FS <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63
      /\ (D + Z.of_nat dn <= 0x10000 \/ 0x56000 <= D)
      /\ (Bi + SN_FS <= D \/ D + Z.of_nat dn <= Bi).

  Definition TOPOK_sn (sp : Z) : Prop := sp <= Bi.

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using CK Ff. pin_using (fun (CK Ff : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Definition sn_sink_frame__stmt : Prop := sink_frame_stmt Bi SN_FS D (Z.of_nat dn) SINK_sn.
  Section Sz3.
  Variables W m m' T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_frame__stmt "vvvv" @W).
  Lemma sn_sink_frame__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_frame__stmt "vvvv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS) MU WM D1 D2.
 cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    unfold SN_FS, SN_FOFF in *.
    exists P, o, jb, jd, wp, cs, cn. cbv zeta. split; [exact ET|]. split; [exact LO80|].
    split; [exact Ewp|]. split; [exact Ecs|]. split; [exact Ecn|].
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. rewrite snfile_cells_size.
             eapply Forall_disjoint_from; [exact D1 | subst Ff; lia | subst Ff; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact IB | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. rewrite FRL.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FRL|].
    split. { eapply rw_cells_transport; [exact CKC | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | subst CK; lia | subst CK; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact DST | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  Lemma sn_sink_frame : ltac:(let t := eval cbv delta [sn_sink_frame__stmt] in sn_sink_frame__stmt in exact t).
  Proof using Type. unfold sink_frame_stmt. intros W m m' T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_frame__body "vvvv"). Qed.

  Definition sn_sink_flags__stmt : Prop := sink_flags_stmt Ff SINK_sn.
  Section Sz4.
  Variables m T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_flags__stmt "vv" @m).
  Lemma sn_sink_flags__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_flags__stmt "vv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS).
 cbv zeta in HS.
    destruct HS as (_ & _ & _ & _ & _ & FC & _).
    exists (Z_to_bv 8 0). split; [|reflexivity].
    unfold snfile_cells in FC. apply (proj1 (rw_cells_app usegs m Ff [C4 (Z_to_bv 64 0)] _)) in FC. destruct FC as [FC _].
    destruct FC as [[WF BY] WR]. split; [split|].
    - cbn. split; [reflexivity| exact I].
    - cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
      change (le4 (Z_to_bv 64 0)) with ([Z_to_bv 8 0] ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in BY.
      apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
    - cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A & B_ & C). split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
  Qed.
  End Sz4.
  Lemma sn_sink_flags : ltac:(let t := eval cbv delta [sn_sink_flags__stmt] in sn_sink_flags__stmt in exact t).
  Proof using Type. unfold sink_flags_stmt. intros m T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_flags__body "vv"). Qed.

  Lemma sn_topok : topok_stmt TOPOK_sn.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  (* [comment removed for export] *)
  Definition sn_out__stmt : Prop := out_stmt Bi SN_FS Ff D (Z.of_nat dn) SINK_sn TOPOK_sn OUT_app.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary : ltac2:(SecDiet.SzSec.tyM 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sn_out__body : ltac2:(SecDiet.SzSec.bodyP 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros HS SRC BYT LB Ha1 Ha2 ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5.   (* [comment removed for export] *)
    destruct HS as (P & o & jb & jd & wp & cs & cn & HS). cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    subst wp cs cn.
    unfold TOPOK_sn, OUT_DEPTH, GLOBALS_TOP, SN_FS, SN_FOFF in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    assert (NNo : 0 <= zlength o) by (unfold zlength; lia).
    assert (WL : 0 <= zlength (firstn (Z.to_nat cap) P) <= cap) by (unfold zlength; rewrite length_firstn; lia).
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    unfold implM, OUT_app. apply impl_ret_intro. cbn [epost fst snd].
    eapply evt_mono.
    { eapply (fwritex_sn_spec ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Ff Bi CK D cap S lo md o bs dn)
        with (wr := firstn (Z.to_nat cap) P) (jb := jb) (jd := jd); subst Ff CK; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact HDN | eassumption | lia | match goal with |- ?g => idtac "SNOUT-PREM:" g end; fail ]). }
    cbv beta. intros ms' PST. unfold fwritex_sn_post in PST.
    destruct PST as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & wr' & o' & jb' & jd'
                     & -> & MU & WM & MI' & ST' & FC' & IB' & CKC' & DST' & SRC' & CASES & LE').
    unfold out_post, SR. unfold SN_FS.
    exists x5, x6, x7, (Z_to_bv 64 (zlength bs)), b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. subst Ff CK. clear -LO HDN HCAP. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      pose proof (rw_CB_length _ _ _ _ IB') as LJB'. rewrite length_app, zb_length in LJB'.
      destruct CASES as [[-> ->] | [-> ->]].
      - exists P, (o ++ bs), jb', jd', (Bi + zlength (o ++ bs)), (D + zlength (firstn (Z.to_nat cap) P)), (cap - zlength (firstn (Z.to_nat cap) P)). cbv zeta. subst st.
        split; [rewrite app_assoc; reflexivity|]. split; [unfold zlength in *; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption.
      - exists (P ++ (o ++ bs)), (@nil Z), jb', jd'. eexists. eexists. eexists. cbv zeta. subst st.
        rewrite <- (firstn_cap_app cap P (o ++ bs)) by exact HCAP.
        split; [rewrite app_nil_r, app_assoc; reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption. }
    split.
    { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
      - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia].
      - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia]. }
    exact SRC'.
  Qed.
  End Sz6.
  Lemma sn_out : ltac:(let t := eval cbv delta [sn_out__stmt] in sn_out__stmt in exact t).
  Proof using Type. unfold out_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary. ltac2:(SecDiet.SzSec.closeP 'sn_out__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnSink.
End TwB.
End Printf_snsink.
