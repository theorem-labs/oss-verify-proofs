(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require PerfA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_stdio_read.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import PerfA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac disjoint_goal ::= disjoint_goal_rel.  Local Ltac tlia ::= tlia_rel.  Local Ltac slia ::= slia_rel.   (* [comment removed for export] *)
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= lia_rel_pin.   (* [comment removed for export] *)
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_READ : Z := 0x99d8c.
Definition STDIO_READ_DEPTH : Z := 80.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bv_eqb_eq' : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Definition dec_readv_Some2__stmt : Prop := forall d0 l0 d1 l1 rsp a,
  0 < l0 -> 0 < l1 -> 0 <= d0 -> 0 <= d1 ->
  dec_readv [(d0, l0); (d1, l1)] rsp = Some a ->
  match a with
  | RdErr e => rsp = efferr e /\ 1 <= e <= 4095
  | RdData bs =>
      let n := Z.of_nat (length bs) in
      n <= l0 + l1 /\
      rsp = mkEffect (Z_to_bv 64 n)
              (if n =? 0 then []
               else if n <=? l0 then [(Z_to_bv 64 d0, bs)]
               else [(Z_to_bv 64 d0, firstn (Z.to_nat l0) bs); (Z_to_bv 64 d1, skipn (Z.to_nat l0) bs)]) []
  end.
Section Sz2.
Variables d0 l0 d1 l1 : ltac2:(SecDiet.SzSec.tyM 'dec_readv_Some2__stmt "vvvv" @d0).
#[using="Type"] Lemma dec_readv_Some2__body : ltac2:(SecDiet.SzSec.bodyP 'dec_readv_Some2__stmt "vvvv").
Proof.
  intros [r ws zs us [|? ?] [|? ?]] a L0 L1 D0 D1 H; try discriminate H.
  unfold dec_readv in H. cbn [core] in H.
  destruct zs; [|discriminate H]. destruct us; [|discriminate H].
  destruct (errno_of r) as [e|] eqn:E.
  - destruct ws; [|discriminate H]. injection H as <-. apply errno_of_Some in E as [-> He]. split; [reflexivity| exact He].
  - unfold iovs_total_Z in H. cbn [fold_right snd fst] in H. rewrite Z.add_0_r in H.
    destruct (Z.leb_spec0 (bv_unsigned r) (l0 + l1)) as [LE|]; [|discriminate H].
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. cbn in R.
    set (n := bv_unsigned r) in *.
    cbn [match_scatter] in H.
    destruct (Z.leb_spec0 (Z.min n l0) 0) as [Z0|P0].
    + assert (n = 0) by lia.
      destruct (Z.leb_spec0 (Z.min n l1) 0) as [_|P1]; [|exfalso; lia].
      destruct ws; [|discriminate H].
      replace (n =? 0) with true in H by (symmetry; apply Z.eqb_eq; lia). injection H as <-.
      cbn [length Z.of_nat Z.eqb]. split; [lia|]. f_equal. apply bv_eq. subst n. rewrite H0. reflexivity.
    + destruct ws as [|[x bs0] ws']; [discriminate H|].
      destruct (bv_eqb x (Z_to_bv 64 d0)) eqn:EX; [|discriminate H]. apply bv_eqb_eq' in EX. subst x.
      destruct (Z.eqb_spec (Z.of_nat (length bs0)) (Z.min n l0)) as [EL|]; [|discriminate H]. cbn [andb] in H.
      destruct (Z.leb_spec0 (Z.min (n - Z.min n l0) l1) 0) as [Z1|P1].
      * destruct ws'; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. assert (EN : Z.of_nat (length bs0) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with true by (symmetry; apply Z.leb_le; lia).
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
      * destruct ws' as [|[y bs1] ws'']; [discriminate H|].
        destruct (bv_eqb y (Z_to_bv 64 d1)) eqn:EY; [|discriminate H]. apply bv_eqb_eq' in EY. subst y.
        destruct (Z.eqb_spec (Z.of_nat (length bs1)) (Z.min (n - Z.min n l0) l1)) as [EL1|]; [|discriminate H]. cbn [andb] in H.
        destruct ws''; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0 - Z.min (n - Z.min n l0) l1) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. rewrite length_app.
        assert (EN : Z.of_nat (length bs0 + length bs1) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.to_nat l0) with (length bs0) by lia.
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all, skipn_app, Nat.sub_diag, skipn_O, skipn_all, app_nil_l.
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
Qed.
End Sz2.
Lemma dec_readv_Some2 : ltac:(let t := eval cbv delta [dec_readv_Some2__stmt] in dec_readv_Some2__stmt in exact t).
Proof. intros d0 l0 d1 l1. ltac2:(SecDiet.SzSec.closeP 'dec_readv_Some2__body "vvvv"). Qed.

Lemma to_of_bytes : forall l, to_bytes (of_bytes l) = l.
Proof. intros l. unfold to_bytes, of_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma FR_map : forall l : list byte, Forall (fun z => 0 <= z < 256) (map bv_unsigned l).
Proof. induction l as [|b l IH]; constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact IH]. Qed.
Lemma FR_cons : forall (b : byte) l, Forall (fun z => 0 <= z < 256) l -> Forall (fun z => 0 <= z < 256) (bv_unsigned b :: l).
Proof. intros b l H. constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact H]. Qed.
Lemma FR_app : forall a b : list Z, Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) b -> Forall (fun z => 0 <= z < 256) (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.
Lemma FR_firstn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (firstn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [H _]. exact H. Qed.
Lemma FR_skipn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (skipn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [_ H]. exact H. Qed.
Ltac frange :=
  repeat first [ assumption | apply Forall_nil | apply FR_map | apply FR_cons | apply FR_app | apply FR_firstn | apply FR_skipn
               | match goal with H : f_rbuf ?f = [] |- Forall _ (f_rbuf ?f) => rewrite H end
               | progress cbn [fst snd f_rbuf set_rbuf set_eof set_w of_bytes] ].
Lemma length_of_bytes : forall l, length (of_bytes l) = length l.
Proof. intros. unfold of_bytes. apply length_map. Qed.

(* [comment removed for export] *)
Lemma apply_mem_write2 : forall m a1 b1 a2 b2,
  apply_writes (apply_zeros (apply_unmaps m []) []) [(a1, b1); (a2, b2)] = write_to_mem (write_to_mem m a1 b1) a2 b2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac sys_mem_write_inner :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?a2 ?bs2) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write_inner: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Definition iov_bytes0__stmt : Prop := forall m A (w0 w1 w2 w3 : word) rest,
  rw_cells asegs m A (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at asegs m A (iovec_bytes [(w0, w1); (w2, w3)]).
Section Sz11.
Variables m A w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes0__stmt "vvvvvvv" @m).
#[using="Type"] Lemma iov_bytes0__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes0__stmt "vvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r.
  apply bytes_at_app. rewrite length_app, !length_le8. split.
  - apply bytes_at_app. rewrite length_le8. split; [exact FB0 | exact FB1].
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz11.
Lemma iov_bytes0 : ltac:(let t := eval cbv delta [iov_bytes0__stmt] in iov_bytes0__stmt in exact t).
Proof. intros m A w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes0__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition land_mod32__stmt : Prop := forall a k, 0 <= k < 2^32 -> 0 <= a -> Z.land (a mod 2^32) k = Z.land a k.
Section Sz12.
Variables a k : ltac2:(SecDiet.SzSec.tyM 'land_mod32__stmt "vv" @a).
#[using="Type"] Lemma land_mod32__body : ltac2:(SecDiet.SzSec.bodyP 'land_mod32__stmt "vv").
Proof.
  intros Hk Ha.
 apply Z.bits_inj'; intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 32) as [L|G].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit k i) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
    eapply Z.lt_le_trans; [apply (proj2 Hk)|]. apply Z.pow_le_mono_r; lia.
Qed.
End Sz12.
Lemma land_mod32 : ltac:(let t := eval cbv delta [land_mod32__stmt] in land_mod32__stmt in exact t).
Proof. intros a k. ltac2:(SecDiet.SzSec.closeP 'land_mod32__body "vv"). Qed.
Lemma sx32_mod32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. nia.
Qed.
Lemma lor16_mod32 : forall a, 0 <= a -> Z.lor a 16 mod 2^32 = Z.lor (a mod 2^32) 16.
Proof.
  intros a Ha. rewrite <- !Z.land_ones by lia. rewrite Z.land_lor_distr_l. f_equal.
Qed.
Definition flags_ok_eof__stmt : Prop := forall f (flags : word), flags_ok f flags -> flags_ok (set_eof f) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)).
Section Sz15.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_eof__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_eof__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_eof__stmt "vv").
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6).
 unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. cbn [f_nord f_nowr f_eof f_chan set_eof].
  pose proof (bv_unsigned_in_range 64 flags) as R. unfold bv_modulus in R.
  rewrite unsigned_lit by (pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)); lia).
  rewrite !Z.land_lor_distr_l. rewrite H1, H2, H4, H5, H6.
  change (Z.land 16 4) with 0. change (Z.land 16 8) with 0. change (Z.land 16 16) with 16. change (Z.land 16 32) with 0. change (Z.land 16 64) with 0. change (Z.land 16 1) with 0.
  rewrite !Z.lor_0_r. repeat split; try reflexivity.
  rewrite H3. destruct (f_eof f); reflexivity.
Qed.
End Sz15.
Lemma flags_ok_eof : ltac:(let t := eval cbv delta [flags_ok_eof__stmt] in flags_ok_eof__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_eof__body "vv"). Qed.

Lemma rw_cells_CB0 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [reflexivity | exact W].
  - cbn [cells_bytes cbytes app]. exact B.
  - cbn [cells_size csize]. exact R.
Qed.
Lemma flags_cell_eof : forall m A (flags : word) rest,
  rw_cells asegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) :: rest) ->
  rw_cells asegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) :: rest).
Proof.
  intros m A flags rest H. apply (rw_cells_C4_eq m A [] (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) rest); [|exact H].
  pose proof (bv_unsigned_in_range 64 flags) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2. unfold bv_modulus in R1, R2.
  cbn in R1, R2. pose proof (Z_lor_range (bv_unsigned (sx32 flags)) 16 ltac:(lia) ltac:(lia)). pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)).
  rewrite !unsigned_lit by lia.
  rewrite !lor16_mod32 by lia. rewrite sx32_mod32. reflexivity.
Qed.

Section StdioRead.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition rd_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f
    /\ (f_eof f = true -> f_eof f' = true).

  Definition rd_W (sp : word) (Fp B bs D len : Z) : list (Z * Z) :=
    [(bv_unsigned sp - STDIO_READ_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + len)].

  Definition stdio_read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (closefn readfn seekfn B prev next : Z) (mode : word) (tail : list byte)
      (D len : Z) (djunk : list byte) (lo : Z) (canary : word) (m : mem) : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ rd_inv f (snd r) /\ Z.of_nat (length (fst r)) <= len /\
      (Z.of_nat (length (fst r)) < len -> f_rbuf (snd r) = []) /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' : word) (rp' : Z) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (rd_W sp Fp B (f_bufsize f) D len) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells asegs m' B [CB (Z.to_nat (f_bufsize f)) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + f_bufsize f
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells asegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat len - length (fst r)) (skipn (length (fst r)) djunk)]
      /\ ssp_cells m' canary.

  Definition stdio_read_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (D len : Z) (djunk : list byte) (lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rp rp closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      flags_ok f flags -> 0 <= rp < 2^63 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] ->
      rw_cells asegs m D [CB (Z.to_nat len) djunk] ->
      f_wactive f = false -> f_wbuf f = [] -> f_rbuf f = [] -> f_chan f = false -> 3 <= f_fd f < 2^31 ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 len ->
      1 <= len -> 0 < f_bufsize f <= 2^20 -> len <= 2^30 ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_READ_DEPTH -> 0x603000 <= lo -> bv_unsigned sp <= 2^47 ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      (D + len <= got_ssp \/ got_ssp + 8 <= D) -> (D + len <= ssp_guard \/ ssp_guard + 8 <= D) ->
      0 < B -> B + f_bufsize f <= 2^47 -> 0 <= D -> D + len <= 2^47 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) -> (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      (D + len <= lo \/ bv_unsigned sp <= D) -> (D + len <= Fp \/ Fp + 232 <= D) -> (D + len <= B \/ B + f_bufsize f <= D) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG D len -> rng_aimg RNG ->
      implAM RNG (stdio_read f B D len) st
        (stdio_read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp closefn readfn seekfn B prev next mode tail D len djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_READ) fc None m (seg_rom asegs)).
  Section Sz18.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma stdio_read_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL RPR BUF DST WACT WB0 RB0 NCH FD -> -> -> L1 BS LMAX ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D0 D47 SB1 SB2 SD1 SD2 SD3 RSTK RFP RBUF RD RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold STDIO_READ, STDIO_READ_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (rd_W sp Fp B (f_bufsize f) D len) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold rd_W, STDIO_READ_DEPTH in MU.
    unfold fcells, file_cells in FC.
    unfold stdio_read.
    replace (f_bufsize f =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn zeta.
    apply implAM_from_evt.
    carve_frame 80%nat ST.
    do 13 zs. do 3 zs. rewrite (sx32_small (f_fd f)) by lia.
    do 6 zs.
    assert (HB1 : (0 <? f_bufsize f) = true) by (apply Z.ltb_lt; lia). rewrite HB1 in *. cbn [Z.b2z] in *.
    destruct (Z.eq_dec len 1) as [L1eq | Lgt].
    - (* [comment removed for export] *)
      subst len. change (1 - 1 =? 0) with true. cbv iota. change (1 - 1) with 0 in *.
      zs. if_true. zs.
      apply evtF_done. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      step_ecall. split.
      { at_nodeA_red; (split; [split_spine | ]); try reflexivity; try lia; try (eapply rng_sub'; [exact RBUF | lia]).
        (* [comment removed for export] *)
        apply (rw_cells_wr_at asegs _ _ _ _ BUF). cbn [cells_size csize]. lia. }
      intros rsp ans Hdec.
      apply (dec_read_Some B (f_bufsize f)) in Hdec; [| lia].
      destruct ans as [e | raw].
      { apply implAM_unr. }
      destruct Hdec as [-> NLE].
      unfold zlength. rewrite length_of_bytes.
      destruct raw as [|b0 rest2].
      + (* [comment removed for export] *)
        cbn [length Z.of_nat Z.eqb delivered_writes].
        apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x99e48)) with (Z_to_bv 64 0x99e48 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. lia. }
        zs. if_true. zs. zs. zs. zs. zs.
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + (* [comment removed for export] *)
        cbn [delivered_writes].
        set (raw' := b0 :: rest2) in *. assert (ER : raw' = b0 :: rest2) by reflexivity. assert (LRW : length raw' = S (length rest2)) by reflexivity.
        clearbody raw'. cbn [length] in NLE.
        replace (Z.of_nat (length raw') =? 0) with false by (rewrite LRW; reflexivity).
        replace (Z.of_nat (length raw') <=? 0) with false by (rewrite LRW; reflexivity).
        apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x99e48)) with (Z_to_bv 64 0x99e48 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 2:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
        zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
        zs. zs. zs. zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
        assert (HR : ov_read_bytes asegs mC (wa (B + 0)) 1 = Some [b0]).
        { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB. rewrite ER in BB.
          rewrite (bytes_at_read asegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
        zs. zs.
        assert (HS : store_ok asegs mC (wa (D + 0)) 1 = true).
        { apply (wr_at_store_ok asegs mC D 1 0 1); [| lia | lia].
          apply (rw_cells_wr_at asegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
        zs.
        change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a _) _) =>
          replace a with (wa D) by (unfold wa; f_equal; lia) end.
        pose proof (rw_cells_CB_prefix_write asegs mC D _ _ [b0] DST ltac:(cbn; lia)) as DST2. cbn [length] in DST2.
        try clear DST; (store_done).
        zs. do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        subst raw'. cbn [length] in LRW, NLE.
        pose proof (rw_cells_merge asegs mZ B [] [CB (length (b0 :: rest2)) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - length (b0 :: rest2)) (skipn (length (b0 :: rest2)) bufbytes)] []) as BM.
        cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
        replace (length (b0 :: rest2) + (Z.to_nat (f_bufsize f) - length (b0 :: rest2) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by (cbn [length] in NLE |- *; lia).
        unfold stdio_read_post. cbn [fst snd]. replace (Z.to_nat 0) with 0%nat by reflexivity. cbn [of_bytes map f_rbuf set_rbuf]. rewrite !skipn_O, !firstn_O.
        repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
        repeat match goal with |- context [firstn 1 (?a :: ?l)] => change (firstn 1 (a :: l)) with [a] end.
        cbn [app length].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length (b0 :: rest2)) bufbytes), mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        unfold zlength. rewrite ?length_map.
        split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (Z.of_nat (length (b0 :: rest2)) - 0)) by (cbn [length]; lia). exact FC. }
        split; [exact FL|].
        split; [exact BM|].
        split. { intros _. rewrite ?length_map. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons.
                 repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
                 rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. fold (of_bytes rest2). rewrite to_of_bytes. apply firstn_all2. lia. }
        split; [lia|]. split; [lia|].
        split. { cbn [length Nat.sub]. change (to_bytes [bv_unsigned b0]) with (to_bytes (of_bytes [b0])). rewrite to_of_bytes. exact DST2. }
        split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      replace (len - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs.
      apply evtF_done. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      step_ecall. split.
      { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -80) _ |- _ =>
            pose proof (iov_bytes0 _ _ _ _ _ _ _ FRM) as IOV end end.
        at_nodeA_red; (split; [split_spine | ]).
        - reflexivity.
        - lia.
        - reflexivity.
        - reflexivity.
        - cbn; lia.
        - rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
        - lia.
        - cbn [dsts_total]. unfold MAX_RW_COUNT. lia.
        - constructor; [|constructor; [|constructor]]; cbn [fst snd].
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at asegs _ _ _ _ DST). cbn [cells_size csize]. lia.
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at asegs _ _ _ _ BUF). cbn [cells_size csize]. lia.
        - reflexivity.
        - rewrite unsigned_lit by lia. cbn [iovs_of map fst snd]. exact IOV.
        - (* [comment removed for export] *)
          split; [rewrite ?unsigned_lit by lia; eapply rng_sub'; [exact RSTK | cbn [length]; lia]
                 | repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; first [exact RD | exact RBUF | eapply rng_sub'; [exact RD | lia] | eapply rng_sub'; [exact RBUF | lia]]]. }
      intros rsp ans Hdec.
      apply (dec_readv_Some2 D (len - 1) B (f_bufsize f)) in Hdec; [| lia | lia | lia | lia].
      destruct ans as [e | raw].
      { (* [comment removed for export] *) apply implAM_unr. }
      cbv zeta in Hdec. destruct Hdec as [NLE ->].
      set (n := Z.of_nat (length raw)) in *.
      unfold zlength. rewrite length_of_bytes. fold n.
      destruct (Z.eqb_spec n 0) as [N0 | N0].
      + (* [comment removed for export] *)
        replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; exact N0).
        apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x99dfc)) with (Z_to_bv 64 0x99dfc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite N0. zs. if_true. zs. if_true. zs. zs. zs. zs. zs.
        (* [comment removed for export] *)
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        assert (raw = []) as -> by (destruct raw; [reflexivity | exfalso; subst n; cbn in N0; lia]).
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r, Nat.sub_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0).
        destruct (Z.leb_spec0 n (len - 1)) as [LE1 | GT1].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with true by (symmetry; apply Z.leb_le; exact LE1).
          apply implAM_from_evt. sys_nret.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x99dfc)) with (Z_to_bv 64 0x99dfc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 2:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs.
          do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evtF_done. apply implAM_ret. apply evtF_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          unfold stdio_read_post. cbn [fst snd].
          split; [reflexivity|]. split; [unfold rd_inv; repeat split; auto|]. split; [rewrite length_of_bytes; lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, rp, bufbytes, mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
          split; [unfold fcells, file_cells; exact FC|]. split; [exact FL|].
          split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
          split; [rewrite to_of_bytes, length_of_bytes; exact DST|]. split; [exact GOT | exact GUARD].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with false by (symmetry; apply Z.leb_gt; lia).
          apply implAM_from_evt.
          rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
          lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
              let p' := eval vm_compute in (p + 4)%Z in
              replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
          end.
          rewrite apply_mem_write2.
          assert (LF : length (firstn (Z.to_nat (len - 1)) raw) = Z.to_nat (len - 1)) by (rewrite length_firstn; lia).
          assert (LS : length (skipn (Z.to_nat (len - 1)) raw) = (length raw - Z.to_nat (len - 1))%nat) by (rewrite length_skipn; lia).
          sys_mem_write_inner.
          sys_mem_write.
          rewrite LF in DST. rewrite LS in BUF.
          assert (exists b0 rest2, skipn (Z.to_nat (len - 1)) raw = b0 :: rest2) as (b0 & rest2 & EB2).
          { destruct (skipn (Z.to_nat (len - 1)) raw) as [|b0 r2] eqn:E; [exfalso; cbn in LS; lia | exists b0, r2; reflexivity]. }
          rewrite EB2 in BUF. cbn [length] in BUF.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x99dfc)) with (Z_to_bv 64 0x99dfc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs. zs. zs. zs. zs.
          zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
          zs. zs.
          lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
          assert (HR : ov_read_bytes asegs mC (wa (B + 0)) 1 = Some [b0]).
          { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB.
            rewrite (bytes_at_read asegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
          zs. zs.
          assert (HS : store_ok asegs mC (wa (D + (len - 1))) 1 = true).
          { apply (wr_at_store_ok asegs mC D len (len - 1) 1); [| lia | lia].
            apply (rw_cells_wr_at asegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
          zs.
          change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
          (* [comment removed for export] *)
          set (k := Z.to_nat (len - 1)) in *.
          pose proof DST as DST0.
          apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
          cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
          assert (DST2 : rw_cells asegs (write_to_mem mC (wa (D + (len - 1))) [b0]) D
                           [CB (k + 1) (firstn k raw ++ [b0]); CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]).
          { replace (D + (len - 1)) with (D + Z.of_nat k) by lia.
            assert (A1 : rw_cells asegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)]).
            { apply rw_cells_frame; [exact DSTa | lia | cbn; lia | cbn [cells_size csize length]; lia]. }
            pose proof (rw_cells_CB_prefix_write asegs mC (D + Z.of_nat k) _ _ [b0] DSTb ltac:(cbn; lia)) as A2. cbn [length] in A2.
            pose proof (proj2 (rw_cells_app asegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)] [CB 1 [b0]; CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))])) as J.
            cbn [cells_size csize Nat.add app] in J. rewrite ?Nat.add_0_r in J. specialize (J (conj A1 A2)).
            apply (rw_cells_merge asegs _ D [] [CB k (firstn k raw); CB 1 [b0]] [CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]) in J.
            cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J. exact J. }
          clear DSTa DSTb.
          try clear DST; (store_done).
          zs. do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evtF_done. apply implAM_ret. apply evtF_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          (* [comment removed for export] *)
          pose proof (rw_cells_merge asegs mZ B [] [CB (length raw - k) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - (length raw - k)) (skipn (length raw - k) bufbytes)] []) as BM.
          cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
          replace (length raw - k + (Z.to_nat (f_bufsize f) - (length raw - k) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by lia.
          assert (RB : skipn 1 (skipn k (of_bytes raw)) = of_bytes rest2).
          { unfold of_bytes. rewrite !skipn_map, EB2. reflexivity. }
          assert (HD : firstn k (of_bytes raw) ++ firstn 1 (skipn k (of_bytes raw)) = of_bytes (firstn k raw ++ [b0])).
          { unfold of_bytes. rewrite firstn_map, skipn_map, EB2, map_app. reflexivity. }
          assert (LR2 : Z.of_nat (length rest2) = n - len).
          { apply (f_equal (@length byte)) in EB2. rewrite length_skipn in EB2. cbn [length] in EB2. lia. }
          unfold stdio_read_post. cbn [fst snd]. rewrite RB, HD. cbn [f_rbuf set_rbuf].
          split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; lia|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length raw - k) bufbytes), mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes, length_app; cbn [length]; repeat f_equal; lia|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          unfold zlength. rewrite !length_of_bytes.
          split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (n - (len - 1))) by lia. exact FC. }
          split; [exact FL|].
          split; [exact BM|].
          split. { intros _. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons. cbn [skipn].
                   rewrite ?skipn_O, ?length_of_bytes, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, to_of_bytes. apply firstn_all2. lia. }
          split; [lia|]. split; [lia|].
          split. { rewrite to_of_bytes, length_app, length_firstn. cbn [length].
                   replace (Nat.min k (length raw) + 1)%nat with (k + 1)%nat by lia.
                   rewrite skipn_skipn in DST2. replace (1 + k)%nat with (k + 1)%nat in DST2 by lia.
                   replace (Z.to_nat len - (k + 1))%nat with (Z.to_nat len - k - 1)%nat by lia. exact DST2. }
          split; [exact GOT | exact GUARD].
  Qed.
  End Sz18.
  Theorem stdio_read_spec : ltac:(let t := eval cbv delta [stdio_read_spec__stmt] in stdio_read_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_read_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End StdioRead.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.PerfA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac disjoint_goal ::= disjoint_goal_rel.  Local Ltac tlia ::= tlia_rel.  Local Ltac slia ::= slia_rel.   (* [comment removed for export] *)
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= lia_rel_pin.   (* [comment removed for export] *)
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_READ : Z := 0x9a170.
Definition STDIO_READ_DEPTH : Z := 80.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bv_eqb_eq' : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Definition dec_readv_Some2__stmt : Prop := forall d0 l0 d1 l1 rsp a,
  0 < l0 -> 0 < l1 -> 0 <= d0 -> 0 <= d1 ->
  dec_readv [(d0, l0); (d1, l1)] rsp = Some a ->
  match a with
  | RdErr e => rsp = efferr e /\ 1 <= e <= 4095
  | RdData bs =>
      let n := Z.of_nat (length bs) in
      n <= l0 + l1 /\
      rsp = mkEffect (Z_to_bv 64 n)
              (if n =? 0 then []
               else if n <=? l0 then [(Z_to_bv 64 d0, bs)]
               else [(Z_to_bv 64 d0, firstn (Z.to_nat l0) bs); (Z_to_bv 64 d1, skipn (Z.to_nat l0) bs)]) []
  end.
Section Sz2.
Variables d0 l0 d1 l1 : ltac2:(SecDiet.SzSec.tyM 'dec_readv_Some2__stmt "vvvv" @d0).
#[using="Type"] Lemma dec_readv_Some2__body : ltac2:(SecDiet.SzSec.bodyP 'dec_readv_Some2__stmt "vvvv").
Proof.
  intros [r ws zs us [|? ?] [|? ?]] a L0 L1 D0 D1 H; try discriminate H.
  unfold dec_readv in H. cbn [core] in H.
  destruct zs; [|discriminate H]. destruct us; [|discriminate H].
  destruct (errno_of r) as [e|] eqn:E.
  - destruct ws; [|discriminate H]. injection H as <-. apply errno_of_Some in E as [-> He]. split; [reflexivity| exact He].
  - unfold iovs_total_Z in H. cbn [fold_right snd fst] in H. rewrite Z.add_0_r in H.
    destruct (Z.leb_spec0 (bv_unsigned r) (l0 + l1)) as [LE|]; [|discriminate H].
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. cbn in R.
    set (n := bv_unsigned r) in *.
    cbn [match_scatter] in H.
    destruct (Z.leb_spec0 (Z.min n l0) 0) as [Z0|P0].
    + assert (n = 0) by lia.
      destruct (Z.leb_spec0 (Z.min n l1) 0) as [_|P1]; [|exfalso; lia].
      destruct ws; [|discriminate H].
      replace (n =? 0) with true in H by (symmetry; apply Z.eqb_eq; lia). injection H as <-.
      cbn [length Z.of_nat Z.eqb]. split; [lia|]. f_equal. apply bv_eq. subst n. rewrite H0. reflexivity.
    + destruct ws as [|[x bs0] ws']; [discriminate H|].
      destruct (bv_eqb x (Z_to_bv 64 d0)) eqn:EX; [|discriminate H]. apply bv_eqb_eq' in EX. subst x.
      destruct (Z.eqb_spec (Z.of_nat (length bs0)) (Z.min n l0)) as [EL|]; [|discriminate H]. cbn [andb] in H.
      destruct (Z.leb_spec0 (Z.min (n - Z.min n l0) l1) 0) as [Z1|P1].
      * destruct ws'; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. assert (EN : Z.of_nat (length bs0) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with true by (symmetry; apply Z.leb_le; lia).
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
      * destruct ws' as [|[y bs1] ws'']; [discriminate H|].
        destruct (bv_eqb y (Z_to_bv 64 d1)) eqn:EY; [|discriminate H]. apply bv_eqb_eq' in EY. subst y.
        destruct (Z.eqb_spec (Z.of_nat (length bs1)) (Z.min (n - Z.min n l0) l1)) as [EL1|]; [|discriminate H]. cbn [andb] in H.
        destruct ws''; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0 - Z.min (n - Z.min n l0) l1) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. rewrite length_app.
        assert (EN : Z.of_nat (length bs0 + length bs1) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.to_nat l0) with (length bs0) by lia.
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all, skipn_app, Nat.sub_diag, skipn_O, skipn_all, app_nil_l.
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
Qed.
End Sz2.
Lemma dec_readv_Some2 : ltac:(let t := eval cbv delta [dec_readv_Some2__stmt] in dec_readv_Some2__stmt in exact t).
Proof. intros d0 l0 d1 l1. ltac2:(SecDiet.SzSec.closeP 'dec_readv_Some2__body "vvvv"). Qed.

Lemma to_of_bytes : forall l, to_bytes (of_bytes l) = l.
Proof. intros l. unfold to_bytes, of_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma FR_map : forall l : list byte, Forall (fun z => 0 <= z < 256) (map bv_unsigned l).
Proof. induction l as [|b l IH]; constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact IH]. Qed.
Lemma FR_cons : forall (b : byte) l, Forall (fun z => 0 <= z < 256) l -> Forall (fun z => 0 <= z < 256) (bv_unsigned b :: l).
Proof. intros b l H. constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact H]. Qed.
Lemma FR_app : forall a b : list Z, Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) b -> Forall (fun z => 0 <= z < 256) (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.
Lemma FR_firstn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (firstn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [H _]. exact H. Qed.
Lemma FR_skipn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (skipn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [_ H]. exact H. Qed.
Ltac frange :=
  repeat first [ assumption | apply Forall_nil | apply FR_map | apply FR_cons | apply FR_app | apply FR_firstn | apply FR_skipn
               | match goal with H : f_rbuf ?f = [] |- Forall _ (f_rbuf ?f) => rewrite H end
               | progress cbn [fst snd f_rbuf set_rbuf set_eof set_w of_bytes] ].
Lemma length_of_bytes : forall l, length (of_bytes l) = length l.
Proof. intros. unfold of_bytes. apply length_map. Qed.

(* [comment removed for export] *)
Lemma apply_mem_write2 : forall m a1 b1 a2 b2,
  apply_writes (apply_zeros (apply_unmaps m []) []) [(a1, b1); (a2, b2)] = write_to_mem (write_to_mem m a1 b1) a2 b2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac sys_mem_write_inner :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?a2 ?bs2) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write_inner: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Definition iov_bytes0__stmt : Prop := forall m A (w0 w1 w2 w3 : word) rest,
  rw_cells asegs m A (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at asegs m A (iovec_bytes [(w0, w1); (w2, w3)]).
Section Sz11.
Variables m A w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes0__stmt "vvvvvvv" @m).
#[using="Type"] Lemma iov_bytes0__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes0__stmt "vvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r.
  apply bytes_at_app. rewrite length_app, !length_le8. split.
  - apply bytes_at_app. rewrite length_le8. split; [exact FB0 | exact FB1].
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz11.
Lemma iov_bytes0 : ltac:(let t := eval cbv delta [iov_bytes0__stmt] in iov_bytes0__stmt in exact t).
Proof. intros m A w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes0__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition land_mod32__stmt : Prop := forall a k, 0 <= k < 2^32 -> 0 <= a -> Z.land (a mod 2^32) k = Z.land a k.
Section Sz12.
Variables a k : ltac2:(SecDiet.SzSec.tyM 'land_mod32__stmt "vv" @a).
#[using="Type"] Lemma land_mod32__body : ltac2:(SecDiet.SzSec.bodyP 'land_mod32__stmt "vv").
Proof.
  intros Hk Ha.
 apply Z.bits_inj'; intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 32) as [L|G].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit k i) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
    eapply Z.lt_le_trans; [apply (proj2 Hk)|]. apply Z.pow_le_mono_r; lia.
Qed.
End Sz12.
Lemma land_mod32 : ltac:(let t := eval cbv delta [land_mod32__stmt] in land_mod32__stmt in exact t).
Proof. intros a k. ltac2:(SecDiet.SzSec.closeP 'land_mod32__body "vv"). Qed.
Lemma sx32_mod32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. nia.
Qed.
Lemma lor16_mod32 : forall a, 0 <= a -> Z.lor a 16 mod 2^32 = Z.lor (a mod 2^32) 16.
Proof.
  intros a Ha. rewrite <- !Z.land_ones by lia. rewrite Z.land_lor_distr_l. f_equal.
Qed.
Definition flags_ok_eof__stmt : Prop := forall f (flags : word), flags_ok f flags -> flags_ok (set_eof f) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)).
Section Sz15.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_eof__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_eof__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_eof__stmt "vv").
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6).
 unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. cbn [f_nord f_nowr f_eof f_chan set_eof].
  pose proof (bv_unsigned_in_range 64 flags) as R. unfold bv_modulus in R.
  rewrite unsigned_lit by (pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)); lia).
  rewrite !Z.land_lor_distr_l. rewrite H1, H2, H4, H5, H6.
  change (Z.land 16 4) with 0. change (Z.land 16 8) with 0. change (Z.land 16 16) with 16. change (Z.land 16 32) with 0. change (Z.land 16 64) with 0. change (Z.land 16 1) with 0.
  rewrite !Z.lor_0_r. repeat split; try reflexivity.
  rewrite H3. destruct (f_eof f); reflexivity.
Qed.
End Sz15.
Lemma flags_ok_eof : ltac:(let t := eval cbv delta [flags_ok_eof__stmt] in flags_ok_eof__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_eof__body "vv"). Qed.

Lemma rw_cells_CB0 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [reflexivity | exact W].
  - cbn [cells_bytes cbytes app]. exact B.
  - cbn [cells_size csize]. exact R.
Qed.
Lemma flags_cell_eof : forall m A (flags : word) rest,
  rw_cells asegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) :: rest) ->
  rw_cells asegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) :: rest).
Proof.
  intros m A flags rest H. apply (rw_cells_C4_eq m A [] (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) rest); [|exact H].
  pose proof (bv_unsigned_in_range 64 flags) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2. unfold bv_modulus in R1, R2.
  cbn in R1, R2. pose proof (Z_lor_range (bv_unsigned (sx32 flags)) 16 ltac:(lia) ltac:(lia)). pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)).
  rewrite !unsigned_lit by lia.
  rewrite !lor16_mod32 by lia. rewrite sx32_mod32. reflexivity.
Qed.

Section StdioRead.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition rd_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f
    /\ (f_eof f = true -> f_eof f' = true).

  Definition rd_W (sp : word) (Fp B bs D len : Z) : list (Z * Z) :=
    [(bv_unsigned sp - STDIO_READ_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + len)].

  Definition stdio_read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (closefn readfn seekfn B prev next : Z) (mode : word) (tail : list byte)
      (D len : Z) (djunk : list byte) (lo : Z) (canary : word) (m : mem) : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ rd_inv f (snd r) /\ Z.of_nat (length (fst r)) <= len /\
      (Z.of_nat (length (fst r)) < len -> f_rbuf (snd r) = []) /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' : word) (rp' : Z) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (rd_W sp Fp B (f_bufsize f) D len) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells asegs m' B [CB (Z.to_nat (f_bufsize f)) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + f_bufsize f
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells asegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat len - length (fst r)) (skipn (length (fst r)) djunk)]
      /\ ssp_cells m' canary.

  Definition stdio_read_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (D len : Z) (djunk : list byte) (lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rp rp closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      flags_ok f flags -> 0 <= rp < 2^63 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] ->
      rw_cells asegs m D [CB (Z.to_nat len) djunk] ->
      f_wactive f = false -> f_wbuf f = [] -> f_rbuf f = [] -> f_chan f = false -> 3 <= f_fd f < 2^31 ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 len ->
      1 <= len -> 0 < f_bufsize f <= 2^20 -> len <= 2^30 ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_READ_DEPTH -> 0x604000 <= lo -> bv_unsigned sp <= 2^47 ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      (D + len <= got_ssp \/ got_ssp + 8 <= D) -> (D + len <= ssp_guard \/ ssp_guard + 8 <= D) ->
      0 < B -> B + f_bufsize f <= 2^47 -> 0 <= D -> D + len <= 2^47 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) -> (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      (D + len <= lo \/ bv_unsigned sp <= D) -> (D + len <= Fp \/ Fp + 232 <= D) -> (D + len <= B \/ B + f_bufsize f <= D) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG D len -> rng_aimg RNG ->
      implAM RNG (stdio_read f B D len) st
        (stdio_read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp closefn readfn seekfn B prev next mode tail D len djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_READ) fc None m (seg_rom asegs)).
  Section Sz18.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma stdio_read_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL RPR BUF DST WACT WB0 RB0 NCH FD -> -> -> L1 BS LMAX ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D0 D47 SB1 SB2 SD1 SD2 SD3 RSTK RFP RBUF RD RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold STDIO_READ, STDIO_READ_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (rd_W sp Fp B (f_bufsize f) D len) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold rd_W, STDIO_READ_DEPTH in MU.
    unfold fcells, file_cells in FC.
    unfold stdio_read.
    replace (f_bufsize f =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn zeta.
    apply implAM_from_evt.
    carve_frame 80%nat ST.
    do 13 zs. do 3 zs. rewrite (sx32_small (f_fd f)) by lia.
    do 6 zs.
    assert (HB1 : (0 <? f_bufsize f) = true) by (apply Z.ltb_lt; lia). rewrite HB1 in *. cbn [Z.b2z] in *.
    destruct (Z.eq_dec len 1) as [L1eq | Lgt].
    - (* [comment removed for export] *)
      subst len. change (1 - 1 =? 0) with true. cbv iota. change (1 - 1) with 0 in *.
      zs. if_true. zs.
      apply evtF_done. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      step_ecall. split.
      { at_nodeA_red; (split; [split_spine | ]); try reflexivity; try lia; try (eapply rng_sub'; [exact RBUF | lia]).
        (* [comment removed for export] *)
        apply (rw_cells_wr_at asegs _ _ _ _ BUF). cbn [cells_size csize]. lia. }
      intros rsp ans Hdec.
      apply (dec_read_Some B (f_bufsize f)) in Hdec; [| lia].
      destruct ans as [e | raw].
      { apply implAM_unr. }
      destruct Hdec as [-> NLE].
      unfold zlength. rewrite length_of_bytes.
      destruct raw as [|b0 rest2].
      + (* [comment removed for export] *)
        cbn [length Z.of_nat Z.eqb delivered_writes].
        apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x9a22c)) with (Z_to_bv 64 0x9a22c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. lia. }
        zs. if_true. zs. zs. zs. zs. zs.
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + (* [comment removed for export] *)
        cbn [delivered_writes].
        set (raw' := b0 :: rest2) in *. assert (ER : raw' = b0 :: rest2) by reflexivity. assert (LRW : length raw' = S (length rest2)) by reflexivity.
        clearbody raw'. cbn [length] in NLE.
        replace (Z.of_nat (length raw') =? 0) with false by (rewrite LRW; reflexivity).
        replace (Z.of_nat (length raw') <=? 0) with false by (rewrite LRW; reflexivity).
        apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x9a22c)) with (Z_to_bv 64 0x9a22c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 2:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
        zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
        zs. zs. zs. zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
        assert (HR : ov_read_bytes asegs mC (wa (B + 0)) 1 = Some [b0]).
        { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB. rewrite ER in BB.
          rewrite (bytes_at_read asegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
        zs. zs.
        assert (HS : store_ok asegs mC (wa (D + 0)) 1 = true).
        { apply (wr_at_store_ok asegs mC D 1 0 1); [| lia | lia].
          apply (rw_cells_wr_at asegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
        zs.
        change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a _) _) =>
          replace a with (wa D) by (unfold wa; f_equal; lia) end.
        pose proof (rw_cells_CB_prefix_write asegs mC D _ _ [b0] DST ltac:(cbn; lia)) as DST2. cbn [length] in DST2.
        try clear DST; (store_done).
        zs. do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        subst raw'. cbn [length] in LRW, NLE.
        pose proof (rw_cells_merge asegs mZ B [] [CB (length (b0 :: rest2)) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - length (b0 :: rest2)) (skipn (length (b0 :: rest2)) bufbytes)] []) as BM.
        cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
        replace (length (b0 :: rest2) + (Z.to_nat (f_bufsize f) - length (b0 :: rest2) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by (cbn [length] in NLE |- *; lia).
        unfold stdio_read_post. cbn [fst snd]. replace (Z.to_nat 0) with 0%nat by reflexivity. cbn [of_bytes map f_rbuf set_rbuf]. rewrite !skipn_O, !firstn_O.
        repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
        repeat match goal with |- context [firstn 1 (?a :: ?l)] => change (firstn 1 (a :: l)) with [a] end.
        cbn [app length].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length (b0 :: rest2)) bufbytes), mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        unfold zlength. rewrite ?length_map.
        split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (Z.of_nat (length (b0 :: rest2)) - 0)) by (cbn [length]; lia). exact FC. }
        split; [exact FL|].
        split; [exact BM|].
        split. { intros _. rewrite ?length_map. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons.
                 repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
                 rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. fold (of_bytes rest2). rewrite to_of_bytes. apply firstn_all2. lia. }
        split; [lia|]. split; [lia|].
        split. { cbn [length Nat.sub]. change (to_bytes [bv_unsigned b0]) with (to_bytes (of_bytes [b0])). rewrite to_of_bytes. exact DST2. }
        split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      replace (len - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs.
      apply evtF_done. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      step_ecall. split.
      { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -80) _ |- _ =>
            pose proof (iov_bytes0 _ _ _ _ _ _ _ FRM) as IOV end end.
        at_nodeA_red; (split; [split_spine | ]).
        - reflexivity.
        - lia.
        - reflexivity.
        - reflexivity.
        - cbn; lia.
        - rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
        - lia.
        - cbn [dsts_total]. unfold MAX_RW_COUNT. lia.
        - constructor; [|constructor; [|constructor]]; cbn [fst snd].
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at asegs _ _ _ _ DST). cbn [cells_size csize]. lia.
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at asegs _ _ _ _ BUF). cbn [cells_size csize]. lia.
        - reflexivity.
        - rewrite unsigned_lit by lia. cbn [iovs_of map fst snd]. exact IOV.
        - (* [comment removed for export] *)
          split; [rewrite ?unsigned_lit by lia; eapply rng_sub'; [exact RSTK | cbn [length]; lia]
                 | repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; first [exact RD | exact RBUF | eapply rng_sub'; [exact RD | lia] | eapply rng_sub'; [exact RBUF | lia]]]. }
      intros rsp ans Hdec.
      apply (dec_readv_Some2 D (len - 1) B (f_bufsize f)) in Hdec; [| lia | lia | lia | lia].
      destruct ans as [e | raw].
      { (* [comment removed for export] *) apply implAM_unr. }
      cbv zeta in Hdec. destruct Hdec as [NLE ->].
      set (n := Z.of_nat (length raw)) in *.
      unfold zlength. rewrite length_of_bytes. fold n.
      destruct (Z.eqb_spec n 0) as [N0 | N0].
      + (* [comment removed for export] *)
        replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; exact N0).
        apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x9a1e0)) with (Z_to_bv 64 0x9a1e0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite N0. zs. if_true. zs. if_true. zs. zs. zs. zs. zs.
        (* [comment removed for export] *)
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        assert (raw = []) as -> by (destruct raw; [reflexivity | exfalso; subst n; cbn in N0; lia]).
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r, Nat.sub_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0).
        destruct (Z.leb_spec0 n (len - 1)) as [LE1 | GT1].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with true by (symmetry; apply Z.leb_le; exact LE1).
          apply implAM_from_evt. sys_nret.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x9a1e0)) with (Z_to_bv 64 0x9a1e0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 2:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs.
          do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evtF_done. apply implAM_ret. apply evtF_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          unfold stdio_read_post. cbn [fst snd].
          split; [reflexivity|]. split; [unfold rd_inv; repeat split; auto|]. split; [rewrite length_of_bytes; lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, rp, bufbytes, mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
          split; [unfold fcells, file_cells; exact FC|]. split; [exact FL|].
          split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
          split; [rewrite to_of_bytes, length_of_bytes; exact DST|]. split; [exact GOT | exact GUARD].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with false by (symmetry; apply Z.leb_gt; lia).
          apply implAM_from_evt.
          rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
          lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
              let p' := eval vm_compute in (p + 4)%Z in
              replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
          end.
          rewrite apply_mem_write2.
          assert (LF : length (firstn (Z.to_nat (len - 1)) raw) = Z.to_nat (len - 1)) by (rewrite length_firstn; lia).
          assert (LS : length (skipn (Z.to_nat (len - 1)) raw) = (length raw - Z.to_nat (len - 1))%nat) by (rewrite length_skipn; lia).
          sys_mem_write_inner.
          sys_mem_write.
          rewrite LF in DST. rewrite LS in BUF.
          assert (exists b0 rest2, skipn (Z.to_nat (len - 1)) raw = b0 :: rest2) as (b0 & rest2 & EB2).
          { destruct (skipn (Z.to_nat (len - 1)) raw) as [|b0 r2] eqn:E; [exfalso; cbn in LS; lia | exists b0, r2; reflexivity]. }
          rewrite EB2 in BUF. cbn [length] in BUF.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x9a1e0)) with (Z_to_bv 64 0x9a1e0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs. zs. zs. zs. zs.
          zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
          zs. zs.
          lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
          assert (HR : ov_read_bytes asegs mC (wa (B + 0)) 1 = Some [b0]).
          { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB.
            rewrite (bytes_at_read asegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
          zs. zs.
          assert (HS : store_ok asegs mC (wa (D + (len - 1))) 1 = true).
          { apply (wr_at_store_ok asegs mC D len (len - 1) 1); [| lia | lia].
            apply (rw_cells_wr_at asegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
          zs.
          change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
          (* [comment removed for export] *)
          set (k := Z.to_nat (len - 1)) in *.
          pose proof DST as DST0.
          apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
          cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
          assert (DST2 : rw_cells asegs (write_to_mem mC (wa (D + (len - 1))) [b0]) D
                           [CB (k + 1) (firstn k raw ++ [b0]); CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]).
          { replace (D + (len - 1)) with (D + Z.of_nat k) by lia.
            assert (A1 : rw_cells asegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)]).
            { apply rw_cells_frame; [exact DSTa | lia | cbn; lia | cbn [cells_size csize length]; lia]. }
            pose proof (rw_cells_CB_prefix_write asegs mC (D + Z.of_nat k) _ _ [b0] DSTb ltac:(cbn; lia)) as A2. cbn [length] in A2.
            pose proof (proj2 (rw_cells_app asegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)] [CB 1 [b0]; CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))])) as J.
            cbn [cells_size csize Nat.add app] in J. rewrite ?Nat.add_0_r in J. specialize (J (conj A1 A2)).
            apply (rw_cells_merge asegs _ D [] [CB k (firstn k raw); CB 1 [b0]] [CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]) in J.
            cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J. exact J. }
          clear DSTa DSTb.
          try clear DST; (store_done).
          zs. do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evtF_done. apply implAM_ret. apply evtF_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          (* [comment removed for export] *)
          pose proof (rw_cells_merge asegs mZ B [] [CB (length raw - k) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - (length raw - k)) (skipn (length raw - k) bufbytes)] []) as BM.
          cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
          replace (length raw - k + (Z.to_nat (f_bufsize f) - (length raw - k) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by lia.
          assert (RB : skipn 1 (skipn k (of_bytes raw)) = of_bytes rest2).
          { unfold of_bytes. rewrite !skipn_map, EB2. reflexivity. }
          assert (HD : firstn k (of_bytes raw) ++ firstn 1 (skipn k (of_bytes raw)) = of_bytes (firstn k raw ++ [b0])).
          { unfold of_bytes. rewrite firstn_map, skipn_map, EB2, map_app. reflexivity. }
          assert (LR2 : Z.of_nat (length rest2) = n - len).
          { apply (f_equal (@length byte)) in EB2. rewrite length_skipn in EB2. cbn [length] in EB2. lia. }
          unfold stdio_read_post. cbn [fst snd]. rewrite RB, HD. cbn [f_rbuf set_rbuf].
          split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; lia|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length raw - k) bufbytes), mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes, length_app; cbn [length]; repeat f_equal; lia|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          unfold zlength. rewrite !length_of_bytes.
          split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (n - (len - 1))) by lia. exact FC. }
          split; [exact FL|].
          split; [exact BM|].
          split. { intros _. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons. cbn [skipn].
                   rewrite ?skipn_O, ?length_of_bytes, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, to_of_bytes. apply firstn_all2. lia. }
          split; [lia|]. split; [lia|].
          split. { rewrite to_of_bytes, length_app, length_firstn. cbn [length].
                   replace (Nat.min k (length raw) + 1)%nat with (k + 1)%nat by lia.
                   rewrite skipn_skipn in DST2. replace (1 + k)%nat with (k + 1)%nat in DST2 by lia.
                   replace (Z.to_nat len - (k + 1))%nat with (Z.to_nat len - k - 1)%nat by lia. exact DST2. }
          split; [exact GOT | exact GUARD].
  Qed.
  End Sz18.
  Theorem stdio_read_spec : ltac:(let t := eval cbv delta [stdio_read_spec__stmt] in stdio_read_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_read_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End StdioRead.
End TwB.
End F_stdio_read.

(* [comment removed for export] *)
Module F_stdio_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

Definition STDIO_EXIT_ENTRY : Z := 0x9a5b4.
Definition EXIT_LOOP : Z := 0x9a6f4.      (* [comment removed for export] *)
Definition EXIT_NEXT : Z := 0x9a6ec.      (* [comment removed for export] *)
Definition EXIT_SYNC : Z := 0x9a724.      (* [comment removed for export] *)
Definition EXIT_DEPTH : Z := 144.         (* [comment removed for export] *)

Section Exit.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition ex_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - EXIT_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition exit_body_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (Fp next : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EXIT_NEXT) fc None m' (seg_rom asegs)
      /\ munch (ex_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (Fp + 112) [C8 (Z_to_bv 64 next)]
      /\ ssp_cells m' canary.

  Section Body.
    Variables (RNG : footprint) (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - EXIT_DEPTH.
    Hypothesis GLO : 0x603000 <= lo.
    Hypothesis Fp0 : 0 < Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RIMG : rng_aimg RNG.

    Lemma fcells_next_cell : forall mm flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
      rw_cells asegs mm Fp (fcells flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl) ->
      rw_cells asegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)].
    Proof using Type. pin_using tt.
      intros. unfold fcells, file_cells in H.
      do 15 (apply (proj1 (rw_cells_app asegs mm _ [_] _)) in H as [_ H]).
      apply (proj1 (rw_cells_app asegs mm _ [_] _)) in H as [H _]. cbn [cells_size csize Nat.add] in H.
      match type of H with rw_cells _ _ ?a _ => replace a with (Fp + 112) in H by lia end. exact H.
    Qed.

    (* [comment removed for export] *)
    Definition exit_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> f_fd f1 = f_fd f ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp) -> mem_inv asegs m1 ->
      munch (ex_W sp Fp) m m1 -> wmono asegs m m1 ->
      implAM RNG (sync_read_pos f1) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_SYNC) fc None m1 (seg_rom asegs)).
    Section Sz2.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_sync__body : ltac2:(SecDiet.SzSec.bodyP 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD Fp0 RSTK RFP RIMG. pin_using (fun (FD Fp0 : unit) => tt).
      intros FC1 RCH RP0 RPHI FD1 SSP1 ST1 MI1 MU1 WM1.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof (fcells_next_cell _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC1) as NXC.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold ex_W, EXIT_DEPTH, EXIT_SYNC, EXIT_NEXT in *.
      destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      unfold sync_read_pos. unfold zlength in *.
      assert (CASES : f_rbuf f1 = [] \/ f_rbuf f1 <> []) by (destruct (f_rbuf f1); [left; reflexivity | right; discriminate]).
      destruct CASES as [RB | RB].
      - (* [comment removed for export] *)
        rewrite RB. apply implAM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        apply evtF_done. unfold exit_body_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [exact NXC|]. split; [exact GOT | exact GUARD].
      - (* [comment removed for export] *)
        replace (match f_rbuf f1 with [] => mret tt | _ :: _ => (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt) end : M St unit)
          with (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt : M St unit)
          by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | reflexivity]).
        assert (NB1 : 1 <= Z.of_nat (length (f_rbuf f1))) by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | cbn; lia]).
        specialize (RCH RB). specialize (FD RCH).
        apply implAM_from_evt.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. unfold F_STDIO_SEEK in *. zs.
        apply evtF_done. rewrite FD1.
        eapply implAM_bind.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact RFP | exact RIMG | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x9a744)) with (Z_to_bv 64 0x9a744 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply implAM_ret. zs.
        apply evtF_done. unfold exit_body_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [exact NXC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz2.
    Lemma exit_sync : ltac:(let t := eval cbv delta [exit_sync__stmt] in exit_sync__stmt in exact t).
    Proof using FD Fp0 RSTK RFP RIMG. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'exit_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition exit_body__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rp : Z) (mode : word) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv asegs m ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      rng RNG B (f_bufsize f) -> rng0 RNG ->
      implAM RNG (close_file f) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_LOOP) fc None m (seg_rom asegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes : ltac2:(SecDiet.SzSec.tyM 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_body__body : ltac2:(SecDiet.SzSec.bodyP 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI CH ST SP47 SSP MI B0 BShi BS0 WBL BSZ SEPB RBUF R0.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_LOOP, EXIT_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof (munch_refl (ex_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
      pose proof WBL as WBL'. unfold zlength in WBL'.
      assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
      unfold close_file.
      assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
      destruct CASES as [WBN | WBN].
      - (* [comment removed for export] *)
        rewrite WBN. apply implM_retb.
        unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
        apply implAM_from_evt.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
        apply evtF_done.
        eapply exit_sync with (f1 := f); fastfirst (first
          [ noevar_assumption | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM | exact RCH | exact ST
          | unfold fcells, file_cells; exact FC
          | reflexivity | assumption | lia ]).
      - (* [comment removed for export] *)
        replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
          by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
        assert (WACT : f_wactive f = true).
        { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
        rewrite WACT in FC.
        assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
        unfold fcells, file_cells in FC.
        change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
        apply implAM_from_evt.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs. zs. zs.
        assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
        zs. rewrite (ret_pc_even (wfn_of f)) by lia.
        apply evtF_done.
        unfold boxed in BUF.
        assert (BUFB : bytes_at asegs m B (to_bytes (f_wbuf f))).
        { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
        eapply implAM_bind.
        { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
            (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
            (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
            rewrite ?unsigned_lit by lia.
          all: first [ reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                     | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RFP | exact RIMG | exact RSTK | exact RBUF
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | unfold zlength in *; lia] | apply rng0_use; [exact R0 | unfold zlength; cbn [length Z.of_nat]; lia]])
                     | apply bytes_at_nil; lia
                     | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                     | left; reflexivity
                     | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                     | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                     | match goal with |- ?g => idtac "WF side:" g end ]. }
        cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
        destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        unfold wf_W, WRITEFN_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
        replace (ret_pc (Z_to_bv 64 0x9a724)) with (Z_to_bv 64 0x9a724 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply exit_sync with (f1 := f_after_write f) (rp := rp); rewrite ?rbuf_after_write'; first
          [ exact SSP2 | exact MI2 | exact ST2 | exact RCH
          | eapply munch_weaken; [| exact MU2]; unfold sub_fp, ex_W, EXIT_DEPTH; cbn [outside]; intros; lia
          | exact WM2
          | rewrite wfn_after_write'; exact FC2
          | unfold f_after_write; destruct (f_stdoutw f); reflexivity
          | reflexivity | assumption | lia
          | match goal with |- ?g => idtac "SY side:" g end ].
    Qed.
    End Sz3.
    Theorem exit_body : ltac:(let t := eval cbv delta [exit_body__stmt] in exit_body__stmt in exact t).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes. ltac2:(SecDiet.SzSec.closeP 'exit_body__body "vvvvvvvvvvvvvvvvvvv"). Qed.
  End Body.

  (* [comment removed for export] *)
  Definition exit_next__stmt : Prop := forall RNG (sp gp tp : word) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp nx : Z) (mm : mem),
    rw_cells asegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)] -> 0 <= Fp -> Fp + 232 < 2^64 -> 0 <= nx < 2^64 -> mem_inv asegs mm ->
    rng RNG (Fp + 112) 8 ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 nx) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (if nx =? 0 then 0x9a5cc else EXIT_LOOP)) fc None mm (seg_rom asegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_NEXT) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables RNG sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm : ltac2:(SecDiet.SzSec.tyM 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_next__body : ltac2:(SecDiet.SzSec.bodyP 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros NX Fp0 FPHI NXR MI RNXT.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold EXIT_NEXT, EXIT_LOOP. zs. zs. if_cases K; zify_cond K.
    - replace (nx =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. cbv delta [mkR]. reflexivity.
    - replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz4.
  Lemma exit_next : ltac:(let t := eval cbv delta [exit_next__stmt] in exit_next__stmt in exact t).
  Proof using Type. intros RNG sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm. ltac2:(SecDiet.SzSec.closeP 'exit_next__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_entry__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (hd lo : Z) (m : mem),
    rw_cells asegs m A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> rw_cells asegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x603000 <= lo -> mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists (x1 a0' a1' a2' a3' : word) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 hd) s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 (if hd =? 0 then 0x9a5cc else EXIT_LOOP)) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STDIO_EXIT_ENTRY) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m : ltac2:(SecDiet.SzSec.tyM 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_entry__body : ltac2:(SecDiet.SzSec.bodyP 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros OH HDR NL ST LO GLO MI RSTK RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold STDIO_EXIT_ENTRY, EXIT_LOOP, A_OFL_HEAD in *. unfold NEED_LOCKS in NL.
    carve_frame 16%nat ST. zs. zs. zs.
    zs. (* [comment removed for export] *)
    carve_frame 16%nat ST; rename FR0 into FRL || idtac.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs.
    match goal with H : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H ST (bv_unsigned sp + -16) end. zs.
    zs. (* [comment removed for export] *)
    zs. if_cases K; zify_cond K.
    - replace (hd =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
    - replace (hd =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; repeat f_equal; rewrite ?Z.mod_small in K by lia; try lia; reflexivity|].
      split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma exit_entry : ltac:(let t := eval cbv delta [exit_entry__stmt] in exit_entry__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m. ltac2:(SecDiet.SzSec.closeP 'exit_entry__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdin__stmt : Prop := forall RNG (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    rw_cells asegs mm A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] -> rw_cells asegs mm A_STDIN stdin_cells -> mem_inv asegs mm ->
    rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists (a0' a1' : word), ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 A_STDIN) s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x9a628) fc None mm (seg_rom asegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a5cc) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm : ltac2:(SecDiet.SzSec.tyM 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_stdin__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US SIN MI RIMG.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDIN_USED, A_STDIN in *. unfold stdin_cells, file_cells, A_STDIN_BUF, F_STDIO_CLOSE, F_STDIO_READ, F_STDIO_SEEK in SIN.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    apply evtF_done. eexists _, _. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz6.
  Lemma exit_stdin : ltac:(let t := eval cbv delta [exit_stdin__stmt] in exit_stdin__stmt in exact t).
  Proof using Type. intros RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm. ltac2:(SecDiet.SzSec.closeP 'exit_stdin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stderr__stmt : Prop := forall RNG (ra sp gp tp : word) (x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (mm : mem) (f : file_st) (flags mode : word) (rp : Z) (tail : list byte) (lo : Z),
    rw_cells asegs mm A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] ->
    rw_cells asegs mm A_STDERR (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                                 (if f_wactive f then A_STDERR_BUF + f_bufsize f else 0) (if f_wactive f then A_STDERR_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDERR_BUF else 0)
                                 0 (wfn_of f) F_STDIO_SEEK A_STDERR_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    f_wbuf f = [] -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    rw_cells asegs mm (bv_unsigned sp + -16) [C8 s0'; C8 ra] -> stk asegs mm lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 16 -> mem_inv asegs mm ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists (a0' a1' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom asegs)
        /\ stk asegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a684) fc None mm (seg_rom asegs)).
  Section Sz7.
  Variables RNG ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo : ltac2:(SecDiet.SzSec.tyM 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_stderr__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US FC WBN RBN RP FR ST LO MI RSTK RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDERR_USED, A_STDERR, A_STDERR_BUF in *. unfold fcells, file_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC.
    rewrite WBN, RBN in FC. change (zlength []) with 0 in FC. rewrite !Z.add_0_r in FC.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. destruct (f_wactive f); reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    apply evtF_done. eexists _, _. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz7.
  Lemma exit_stderr : ltac:(let t := eval cbv delta [exit_stderr__stmt] in exit_stderr__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo. ltac2:(SecDiet.SzSec.closeP 'exit_stderr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdout__stmt : Prop := forall RNG (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (st : St) (f : file_st) (flags mode : word) (rp : Z) (tail bufbytes : list byte) (lo : Z) (canary : word),
    rw_cells asegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
    rw_cells asegs m A_STDOUT (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                             (if f_wactive f then A_STDOUT_BUF + f_bufsize f else 0) (if f_wactive f then A_STDOUT_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDOUT_BUF else 0)
                             0 (wfn_of f) F_STDIO_SEEK A_STDOUT_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    Z.land (bv_unsigned flags) F_SVB = 0 ->
    rw_cells asegs m A_STDOUT_BUF [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_bufsize f = BUFSIZ -> zlength (f_wbuf f) <= f_bufsize f ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - EXIT_DEPTH -> 0x603000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
    implAM RNG (close_file f) st
      (fun _ st' ms' => st' = st /\
         exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
         ms' = MS (mkR x1' sp gp tp t0' t1' t2' (Z_to_bv 64 A_STDOUT) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x9a684) fc None m' (seg_rom asegs)
         /\ munch (ex_W sp A_STDOUT) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
         /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary)
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a628) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_stdout__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US FC FL64 BUF BUFP WB0 RBN RP CHN FD12 BS WBL ST LO GLO SP47 SSP MI RSTK RIMG R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_DEPTH in *.
    unfold A_STDOUT_USED, A_STDOUT, A_STDOUT_BUF, BUFSIZ in *.
    pose proof (munch_refl (ex_W sp 695440) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    rewrite RBN in FC. change (zlength (@nil Z)) with 0 in FC. rewrite Z.add_0_r in FC.
    unfold close_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb. unfold sync_read_pos. rewrite RBN. apply implAM_ret.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      apply evtF_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact SSP0].
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC. rewrite BS in FC, BUF.
      change (rw_cells asegs m 6299856 [CB (Z.to_nat 1024) bufbytes]) with (boxed (rw_cells asegs m 6299856 [CB (Z.to_nat 1024) bufbytes])) in BUF.
      apply implAM_from_evt.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evtF_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at asegs m 6299856 (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat 1024) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
      eapply implAM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := 695440) (flags := flags) (rpos := rp) (rend := rp) (closefn := F_STDIO_CLOSE) (wend := 6299856 + 1024) (readfn := 0)
          (seekfn := F_STDIO_SEEK) (B := 6299856) (bufsize := 1024) (prev := 0) (next := 0) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: first [ reflexivity | rewrite BS; exact FC | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RIMG | exact RSTK
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RIMG | unfold zlength in *; lia] | apply rng0_use; [exact R0 | unfold zlength; cbn [length Z.of_nat]; lia]])
                   | apply bytes_at_nil; lia
                   | rewrite CHN; exact FD12
                   | left; reflexivity
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   | match goal with |- ?g => idtac "WFo side:" g end ]. }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x9a664)) with (Z_to_bv 64 0x9a664 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold sync_read_pos. rewrite rbuf_after_write', RBN. apply implAM_ret.
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      apply evtF_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, ex_W, EXIT_DEPTH; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2| exact SSP2].
  Qed.
  End Sz8.
  Theorem exit_stdout : ltac:(let t := eval cbv delta [exit_stdout__stmt] in exit_stdout__stmt in exact t).
  Proof using Type. intros RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'exit_stdout__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Exit.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

Definition STDIO_EXIT_ENTRY : Z := 0x9a998.
Definition EXIT_LOOP : Z := 0x9aad8.      (* [comment removed for export] *)
Definition EXIT_NEXT : Z := 0x9aad0.      (* [comment removed for export] *)
Definition EXIT_SYNC : Z := 0x9ab08.      (* [comment removed for export] *)
Definition EXIT_DEPTH : Z := 144.         (* [comment removed for export] *)

Section Exit.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition ex_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - EXIT_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition exit_body_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (Fp next : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EXIT_NEXT) fc None m' (seg_rom asegs)
      /\ munch (ex_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (Fp + 112) [C8 (Z_to_bv 64 next)]
      /\ ssp_cells m' canary.

  Section Body.
    Variables (RNG : footprint) (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - EXIT_DEPTH.
    Hypothesis GLO : 0x604000 <= lo.
    Hypothesis Fp0 : 0 < Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RIMG : rng_aimg RNG.

    Lemma fcells_next_cell : forall mm flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
      rw_cells asegs mm Fp (fcells flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl) ->
      rw_cells asegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)].
    Proof using Type. pin_using tt.
      intros. unfold fcells, file_cells in H.
      do 15 (apply (proj1 (rw_cells_app asegs mm _ [_] _)) in H as [_ H]).
      apply (proj1 (rw_cells_app asegs mm _ [_] _)) in H as [H _]. cbn [cells_size csize Nat.add] in H.
      match type of H with rw_cells _ _ ?a _ => replace a with (Fp + 112) in H by lia end. exact H.
    Qed.

    (* [comment removed for export] *)
    Definition exit_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> f_fd f1 = f_fd f ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp) -> mem_inv asegs m1 ->
      munch (ex_W sp Fp) m m1 -> wmono asegs m m1 ->
      implAM RNG (sync_read_pos f1) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_SYNC) fc None m1 (seg_rom asegs)).
    Section Sz2.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_sync__body : ltac2:(SecDiet.SzSec.bodyP 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD Fp0 RSTK RFP RIMG. pin_using (fun (FD Fp0 : unit) => tt).
      intros FC1 RCH RP0 RPHI FD1 SSP1 ST1 MI1 MU1 WM1.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof (fcells_next_cell _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC1) as NXC.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold ex_W, EXIT_DEPTH, EXIT_SYNC, EXIT_NEXT in *.
      destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      unfold sync_read_pos. unfold zlength in *.
      assert (CASES : f_rbuf f1 = [] \/ f_rbuf f1 <> []) by (destruct (f_rbuf f1); [left; reflexivity | right; discriminate]).
      destruct CASES as [RB | RB].
      - (* [comment removed for export] *)
        rewrite RB. apply implAM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        apply evtF_done. unfold exit_body_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [exact NXC|]. split; [exact GOT | exact GUARD].
      - (* [comment removed for export] *)
        replace (match f_rbuf f1 with [] => mret tt | _ :: _ => (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt) end : M St unit)
          with (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt : M St unit)
          by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | reflexivity]).
        assert (NB1 : 1 <= Z.of_nat (length (f_rbuf f1))) by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | cbn; lia]).
        specialize (RCH RB). specialize (FD RCH).
        apply implAM_from_evt.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. unfold F_STDIO_SEEK in *. zs.
        apply evtF_done. rewrite FD1.
        eapply implAM_bind.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact RFP | exact RIMG | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x9ab28)) with (Z_to_bv 64 0x9ab28 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply implAM_ret. zs.
        apply evtF_done. unfold exit_body_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [exact NXC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz2.
    Lemma exit_sync : ltac:(let t := eval cbv delta [exit_sync__stmt] in exit_sync__stmt in exact t).
    Proof using FD Fp0 RSTK RFP RIMG. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'exit_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition exit_body__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rp : Z) (mode : word) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv asegs m ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      rng RNG B (f_bufsize f) -> rng0 RNG ->
      implAM RNG (close_file f) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_LOOP) fc None m (seg_rom asegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes : ltac2:(SecDiet.SzSec.tyM 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_body__body : ltac2:(SecDiet.SzSec.bodyP 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI CH ST SP47 SSP MI B0 BShi BS0 WBL BSZ SEPB RBUF R0.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_LOOP, EXIT_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof (munch_refl (ex_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
      pose proof WBL as WBL'. unfold zlength in WBL'.
      assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
      unfold close_file.
      assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
      destruct CASES as [WBN | WBN].
      - (* [comment removed for export] *)
        rewrite WBN. apply implM_retb.
        unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
        apply implAM_from_evt.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
        apply evtF_done.
        eapply exit_sync with (f1 := f); fastfirst (first
          [ noevar_assumption | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM | exact RCH | exact ST
          | unfold fcells, file_cells; exact FC
          | reflexivity | assumption | lia ]).
      - (* [comment removed for export] *)
        replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
          by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
        assert (WACT : f_wactive f = true).
        { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
        rewrite WACT in FC.
        assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
        unfold fcells, file_cells in FC.
        change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
        apply implAM_from_evt.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs. zs. zs.
        assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
        zs. rewrite (ret_pc_even (wfn_of f)) by lia.
        apply evtF_done.
        unfold boxed in BUF.
        assert (BUFB : bytes_at asegs m B (to_bytes (f_wbuf f))).
        { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
        eapply implAM_bind.
        { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
            (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
            (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
            rewrite ?unsigned_lit by lia.
          all: first [ reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                     | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RFP | exact RIMG | exact RSTK | exact RBUF
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | unfold zlength in *; lia] | apply rng0_use; [exact R0 | unfold zlength; cbn [length Z.of_nat]; lia]])
                     | apply bytes_at_nil; lia
                     | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                     | left; reflexivity
                     | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                     | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                     | match goal with |- ?g => idtac "WF side:" g end ]. }
        cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
        destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        unfold wf_W, WRITEFN_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
        replace (ret_pc (Z_to_bv 64 0x9ab08)) with (Z_to_bv 64 0x9ab08 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply exit_sync with (f1 := f_after_write f) (rp := rp); rewrite ?rbuf_after_write'; first
          [ exact SSP2 | exact MI2 | exact ST2 | exact RCH
          | eapply munch_weaken; [| exact MU2]; unfold sub_fp, ex_W, EXIT_DEPTH; cbn [outside]; intros; lia
          | exact WM2
          | rewrite wfn_after_write'; exact FC2
          | unfold f_after_write; destruct (f_stdoutw f); reflexivity
          | reflexivity | assumption | lia
          | match goal with |- ?g => idtac "SY side:" g end ].
    Qed.
    End Sz3.
    Theorem exit_body : ltac:(let t := eval cbv delta [exit_body__stmt] in exit_body__stmt in exact t).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes. ltac2:(SecDiet.SzSec.closeP 'exit_body__body "vvvvvvvvvvvvvvvvvvv"). Qed.
  End Body.

  (* [comment removed for export] *)
  Definition exit_next__stmt : Prop := forall RNG (sp gp tp : word) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp nx : Z) (mm : mem),
    rw_cells asegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)] -> 0 <= Fp -> Fp + 232 < 2^64 -> 0 <= nx < 2^64 -> mem_inv asegs mm ->
    rng RNG (Fp + 112) 8 ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 nx) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (if nx =? 0 then 0x9a9b0 else EXIT_LOOP)) fc None mm (seg_rom asegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_NEXT) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables RNG sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm : ltac2:(SecDiet.SzSec.tyM 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_next__body : ltac2:(SecDiet.SzSec.bodyP 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros NX Fp0 FPHI NXR MI RNXT.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold EXIT_NEXT, EXIT_LOOP. zs. zs. if_cases K; zify_cond K.
    - replace (nx =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. cbv delta [mkR]. reflexivity.
    - replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz4.
  Lemma exit_next : ltac:(let t := eval cbv delta [exit_next__stmt] in exit_next__stmt in exact t).
  Proof using Type. intros RNG sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm. ltac2:(SecDiet.SzSec.closeP 'exit_next__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_entry__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (hd lo : Z) (m : mem),
    rw_cells asegs m A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> rw_cells asegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x604000 <= lo -> mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists (x1 a0' a1' a2' a3' : word) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 hd) s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 (if hd =? 0 then 0x9a9b0 else EXIT_LOOP)) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STDIO_EXIT_ENTRY) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m : ltac2:(SecDiet.SzSec.tyM 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_entry__body : ltac2:(SecDiet.SzSec.bodyP 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros OH HDR NL ST LO GLO MI RSTK RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold STDIO_EXIT_ENTRY, EXIT_LOOP, A_OFL_HEAD in *. unfold NEED_LOCKS in NL.
    carve_frame 16%nat ST. zs. zs. zs.
    zs. (* [comment removed for export] *)
    carve_frame 16%nat ST; rename FR0 into FRL || idtac.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs.
    match goal with H : rw_cells asegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H ST (bv_unsigned sp + -16) end. zs.
    zs. (* [comment removed for export] *)
    zs. if_cases K; zify_cond K.
    - replace (hd =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
    - replace (hd =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; repeat f_equal; rewrite ?Z.mod_small in K by lia; try lia; reflexivity|].
      split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma exit_entry : ltac:(let t := eval cbv delta [exit_entry__stmt] in exit_entry__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m. ltac2:(SecDiet.SzSec.closeP 'exit_entry__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdin__stmt : Prop := forall RNG (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    rw_cells asegs mm A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] -> rw_cells asegs mm A_STDIN stdin_cells -> mem_inv asegs mm ->
    rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists (a0' a1' : word), ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 A_STDIN) s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x9aa0c) fc None mm (seg_rom asegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a9b0) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm : ltac2:(SecDiet.SzSec.tyM 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_stdin__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US SIN MI RIMG.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDIN_USED, A_STDIN in *. unfold stdin_cells, file_cells, A_STDIN_BUF, F_STDIO_CLOSE, F_STDIO_READ, F_STDIO_SEEK in SIN.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    apply evtF_done. eexists _, _. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz6.
  Lemma exit_stdin : ltac:(let t := eval cbv delta [exit_stdin__stmt] in exit_stdin__stmt in exact t).
  Proof using Type. intros RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm. ltac2:(SecDiet.SzSec.closeP 'exit_stdin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stderr__stmt : Prop := forall RNG (ra sp gp tp : word) (x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (mm : mem) (f : file_st) (flags mode : word) (rp : Z) (tail : list byte) (lo : Z),
    rw_cells asegs mm A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] ->
    rw_cells asegs mm A_STDERR (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                                 (if f_wactive f then A_STDERR_BUF + f_bufsize f else 0) (if f_wactive f then A_STDERR_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDERR_BUF else 0)
                                 0 (wfn_of f) F_STDIO_SEEK A_STDERR_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    f_wbuf f = [] -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    rw_cells asegs mm (bv_unsigned sp + -16) [C8 s0'; C8 ra] -> stk asegs mm lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 16 -> mem_inv asegs mm ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists (a0' a1' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom asegs)
        /\ stk asegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9aa68) fc None mm (seg_rom asegs)).
  Section Sz7.
  Variables RNG ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo : ltac2:(SecDiet.SzSec.tyM 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_stderr__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US FC WBN RBN RP FR ST LO MI RSTK RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDERR_USED, A_STDERR, A_STDERR_BUF in *. unfold fcells, file_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC.
    rewrite WBN, RBN in FC. change (zlength []) with 0 in FC. rewrite !Z.add_0_r in FC.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. destruct (f_wactive f); reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    apply evtF_done. eexists _, _. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz7.
  Lemma exit_stderr : ltac:(let t := eval cbv delta [exit_stderr__stmt] in exit_stderr__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo. ltac2:(SecDiet.SzSec.closeP 'exit_stderr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdout__stmt : Prop := forall RNG (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (st : St) (f : file_st) (flags mode : word) (rp : Z) (tail bufbytes : list byte) (lo : Z) (canary : word),
    rw_cells asegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
    rw_cells asegs m A_STDOUT (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                             (if f_wactive f then A_STDOUT_BUF + f_bufsize f else 0) (if f_wactive f then A_STDOUT_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDOUT_BUF else 0)
                             0 (wfn_of f) F_STDIO_SEEK A_STDOUT_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    Z.land (bv_unsigned flags) F_SVB = 0 ->
    rw_cells asegs m A_STDOUT_BUF [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_bufsize f = BUFSIZ -> zlength (f_wbuf f) <= f_bufsize f ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - EXIT_DEPTH -> 0x604000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
    implAM RNG (close_file f) st
      (fun _ st' ms' => st' = st /\
         exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
         ms' = MS (mkR x1' sp gp tp t0' t1' t2' (Z_to_bv 64 A_STDOUT) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x9aa68) fc None m' (seg_rom asegs)
         /\ munch (ex_W sp A_STDOUT) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
         /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary)
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9aa0c) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma exit_stdout__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US FC FL64 BUF BUFP WB0 RBN RP CHN FD12 BS WBL ST LO GLO SP47 SSP MI RSTK RIMG R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_DEPTH in *.
    unfold A_STDOUT_USED, A_STDOUT, A_STDOUT_BUF, BUFSIZ in *.
    pose proof (munch_refl (ex_W sp 696432) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    rewrite RBN in FC. change (zlength (@nil Z)) with 0 in FC. rewrite Z.add_0_r in FC.
    unfold close_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb. unfold sync_read_pos. rewrite RBN. apply implAM_ret.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      apply evtF_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact SSP0].
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC. rewrite BS in FC, BUF.
      change (rw_cells asegs m 6300880 [CB (Z.to_nat 1024) bufbytes]) with (boxed (rw_cells asegs m 6300880 [CB (Z.to_nat 1024) bufbytes])) in BUF.
      apply implAM_from_evt.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evtF_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at asegs m 6300880 (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat 1024) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
      eapply implAM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := 696432) (flags := flags) (rpos := rp) (rend := rp) (closefn := F_STDIO_CLOSE) (wend := 6300880 + 1024) (readfn := 0)
          (seekfn := F_STDIO_SEEK) (B := 6300880) (bufsize := 1024) (prev := 0) (next := 0) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: first [ reflexivity | rewrite BS; exact FC | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RIMG | exact RSTK
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RIMG | unfold zlength in *; lia] | apply rng0_use; [exact R0 | unfold zlength; cbn [length Z.of_nat]; lia]])
                   | apply bytes_at_nil; lia
                   | rewrite CHN; exact FD12
                   | left; reflexivity
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   | match goal with |- ?g => idtac "WFo side:" g end ]. }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x9aa48)) with (Z_to_bv 64 0x9aa48 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold sync_read_pos. rewrite rbuf_after_write', RBN. apply implAM_ret.
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      apply evtF_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, ex_W, EXIT_DEPTH; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2| exact SSP2].
  Qed.
  End Sz8.
  Theorem exit_stdout : ltac:(let t := eval cbv delta [exit_stdout__stmt] in exit_stdout__stmt in exact t).
  Proof using Type. intros RNG sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'exit_stdout__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Exit.
End TwB.
End F_stdio_exit.

(* [comment removed for export] *)
Module F_fread.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD : Z := 0x9a954.
Definition FREAD_LOOP : Z := 0x9a9f4.
Definition FREAD_DEPTH : Z := 2304.   (* [comment removed for export] *)

Lemma to_bytes_app' : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

Lemma divu_one : forall a : word, mul_div M_DIVU a (Z_to_bv 64 1) = a.
Proof.
  intros a. unfold mul_div. cbn [bv_unsigned Z.eqb].
  replace (bv_unsigned (Z_to_bv 64 1) =? 0) with false by reflexivity. cbv iota.
  apply bv_eq. rewrite bv_divu_unsigned. change (bv_unsigned (Z_to_bv 64 1)) with 1. apply Z.div_1_r.
Qed.

Lemma retval_size1 : forall nmemb, 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) nmemb = nmemb.
Proof.
  intros nmemb Hn. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma wfn_of_rd : forall f f', f_stdoutw f' = f_stdoutw f -> wfn_of f' = wfn_of f.
Proof. intros f f' E. unfold wfn_of. rewrite E. reflexivity. Qed.
Lemma lbf_of_rd : forall f f', f_lbf_nl f' = f_lbf_nl f -> lbf_of f' = lbf_of f.
Proof. intros f f' E. unfold lbf_of. rewrite E. reflexivity. Qed.

Section Fread.
  Context {rc : runConstT}.
  Context {St : Type}.

  Lemma implM_retb : forall {A B} RNG (a : A) (k : A -> M St B) (s : St) Q ms,
    implAM RNG (k a) s Q ms -> implAM RNG (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B RNG a k s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Definition fr_inv (f0 f : file_st) : Prop :=
    f_fd f = f_fd f0 /\ f_chan f = f_chan f0 /\ f_bufsize f = f_bufsize f0 /\ f_nord f = f_nord f0 /\ f_nowr f = f_nowr f0
    /\ f_wactive f = false /\ f_wbuf f = [].

  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Definition fr_W : list (Z * Z) := [(bv_unsigned sp - FREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + n)].

  Definition fread_post : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fr_inv f0 (snd r) /\ Z.of_nat (length (fst r)) <= n /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (rp' : Z) (bufbytes' rest' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch fr_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 F_STDIO_READ (wfn_of (snd r)) seekfn B bs prev next (f_fd f0) mode' (lbf_of (snd r)) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells asegs m' B [CB (Z.to_nat bs) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + bs
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells asegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat n - length (fst r)) rest']
      /\ ssp_cells m' canary.

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis DSEP1 : D + n <= got_ssp \/ got_ssp + 8 <= D.
  Hypothesis DSEP2 : D + n <= ssp_guard \/ ssp_guard + 8 <= D.
  Hypothesis B0 : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis D0 : 0 <= D.
  Hypothesis D47 : D + n <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis SD1 : D + n <= lo \/ bv_unsigned sp <= D.
  Hypothesis SD2 : D + n <= Fp \/ Fp + 232 <= D.
  Hypothesis SD3 : D + n <= B \/ B + bs <= D.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B bs.
  Hypothesis RD : rng RNG D n.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis R0 : rng0 RNG.

  (* [comment removed for export] *)
  Lemma fread_loop_spec : forall fuel (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fcur : file_st) (flags1 mode1 : word) (rp1 : Z)
      (bufbytes1 rest : list byte) (acc : list Z) (off l : Z) (m1 : mem),
    rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 Fp (fcells flags1 rp1 rp1 closefn 0 0 0 F_STDIO_READ (wfn_of fcur) seekfn B bs prev next (f_fd f0) mode1 (lbf_of fcur) tail) ->
    flags_ok fcur flags1 -> fr_inv f0 fcur -> f_rbuf fcur = [] -> 0 <= rp1 < 2^63 ->
    rw_cells asegs m1 B [CB (Z.to_nat bs) bufbytes1] ->
    rw_cells asegs m1 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest] -> off = zlength acc -> off + l = n -> 1 <= l ->
    Forall (fun z => 0 <= z < 256) acc ->
    ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -64) -> mem_inv asegs m1 ->
    munch fr_W m m1 -> wmono asegs m m1 ->
    implAM RNG (fread_loop fuel fcur B (D + off) l acc) st fread_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 (D + off)) (Z_to_bv 64 l) (Z_to_bv 64 1) (Z_to_bv 64 n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREAD_LOOP) fc None m1 (seg_rom asegs)).
  Proof using B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 RSTK RFP RBUF RD RIMG R0. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 : unit) => tt).
    induction fuel as [|fuel IH]; intros until m1; intros FR1 FC1 FL1 INV1 RB1 RP1 BUF1 DST1 OFF OL L1 FACC SSP1 ST1 MI1 MU1 WM1.
    { cbn [fread_loop]. apply implAM_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_LOOP, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    destruct INV1 as (Ifd & Ich & Ibs & Ind & Inw & Iwa & Iwb).
    pose proof (rw_cells_bound _ _ _ _ DST1) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
    assert (LACC : length (to_bytes acc) = length acc) by apply length_to_bytes.
    unfold zlength in OFF.
    cbn [fread_loop]. replace (l <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    eapply implAM_bind.
    { pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fr_W, FREAD_DEPTH in MU1.
      apply implAM_from_evt. zs. zs.
      apply evtF_done.
      eapply (toread_spec (St:=St)) with (f := fcur) (Fp := Fp) (flags := flags1) (rpos := rp1) (rend := rp1) (closefn := closefn) (readfn := F_STDIO_READ)
        (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode1) (tail := tail) (bufbytes := bufbytes1) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; rewrite ?Iwa, ?Ibs, ?Ifd, ?Iwb, ?Ich.
      all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (proj1 FL1)]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (proj1 (proj2 (proj2 FL1)))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (proj1 (proj2 (proj2 (proj2 (proj2 FL1)))))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [rewrite NCH; exact FD]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SSP0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | unfold TOREAD_DEPTH; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [(lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF | exact RD
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | rewrite ?Tbs, ?Ibs; lia] | eapply rng_sub'; [exact RD | lia]])]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RBUF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact R0]) ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [fst snd] in He, TRI. destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold tr_W, TOREAD_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x9a9fc)) with (Z_to_bv 64 0x9a9fc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof TRI as TRI'. destruct TRI as (Tfd & Tch & Tbs & Tnd & Tnw & Teof & Twa & Twb & Trb & _).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BUF2 : rw_cells asegs m2 B [CB (Z.to_nat (f_bufsize f0)) bufbytes1]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (DST2 : rw_cells asegs m2 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact DST1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (MU12 : munch fr_W m m2).
    { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fr_W, FREAD_DEPTH; cbn [outside]; intros; lia. }
    assert (WM12 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    assert (FL2 : flags_ok f2 flags1) by (unfold flags_ok in *; rewrite ?Tch, Tnd, Tnw, Teof; first [exact FL1 | rewrite <- ?Tch; exact FL1]).
    clear FR1 BUF1 DST1 MU2 WM2 MI1 ST1.
    pose proof FC2 as FC. unfold fcells, file_cells in FC.
    destruct SSP2 as [GOT2 GUARD2].
    cbn [fst snd] in *. subst e.
    apply implAM_from_evt.
    destruct (f_eof fcur) eqn:EOF.
    - (* [comment removed for export] *)
      cbn [Z.b2z Z.opp]. zs. if_cases Hx; zify_cond Hx. 2:{ exfalso. vm_compute in Hx. lia. }
      apply evtF_done. apply implM_retb. apply implAM_ret.
      zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
      zs. zs. rewrite divu_one. do 10 zs.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. cbn [fst snd].
      unfold fread_post. cbn [fst snd].
      split; [reflexivity|]. split; [unfold fr_inv; repeat split; first [congruence | assumption]|]. split; [lia|]. split; [solve [frange]|]. split; [solve [frange]|].
      replace (n - l) with (zlength acc) by (unfold zlength; lia).
      do 14 eexists. exists flags1, x14, (B + f_bufsize fcur), bufbytes1, rest, m2.
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU12|]. split; [exact WM12|]. split; [exact MI2|]. split; [exact ST2|].
      rewrite Trb. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      split; [unfold fcells, file_cells; rewrite <- ?Ibs, <- ?Ifd; exact FC|]. split; [exact FL2|].
      split; [exact BUF2|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
      split; [replace (Z.to_nat n - length acc)%nat with (Z.to_nat l) by lia; exact DST2|]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      cbn [Z.b2z Z.opp]. zs. if_cases Hx; zify_cond Hx. 1:{ exfalso. vm_compute in Hx. lia. }
      zs. zs. zs. zs. unfold F_STDIO_READ at 1. zs.
      apply evtF_done. cbv beta.
      (* [comment removed for export] *)
      pose proof DST2 as DSTa. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in DSTa. destruct DSTa as [DSTa DSTb].
      cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r, ?LACC in DSTb.
      replace (D + Z.of_nat (length acc)) with (D + off) in DSTb by lia.
      eapply implAM_bind.
      { eapply (stdio_read_spec (St:=St)) with (f := f2) (Fp := Fp) (flags := flags1) (rp := B + f_bufsize fcur) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := _) (tail := tail) (bufbytes := bufbytes1) (D := D + off) (len := l) (djunk := rest)
          (lo := lo) (canary := canary);
          rewrite ?unsigned_lit by lia; rewrite ?Tfd, ?Tch, ?Tbs, ?Ifd, ?Ich, ?Ibs.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; rewrite <- ?Ibs, <- ?Ifd; exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact DSTb]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Twa]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Twb]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Trb]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NCH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FD]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact L1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT2 | exact GUARD2]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | unfold STDIO_READ_DEPTH; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SB2]) | unfold STDIO_READ_DEPTH; lia | unfold STDIO_READ_DEPTH; lia | unfold STDIO_READ_DEPTH; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [(lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF | exact RD
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | rewrite ?Tbs, ?Ibs; lia] | eapply rng_sub'; [exact RD | lia]])]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RBUF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [(lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF | exact RD
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | rewrite ?Tbs, ?Ibs; lia] | eapply rng_sub'; [exact RD | lia]])]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros [bsr f3] st3 ms3 (-> & RDI & BL & RBE & GF3 & GRB3 & PO). cbn [fst snd] in RDI, BL, RBE, PO |- *. destruct_exs PO.
      destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & FL3 & BUF3 & RREL3 & RP3 & RP3' & DST3 & SSP3).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      unfold rd_W, STDIO_READ_DEPTH in MU3. rewrite !unsigned_lit in MU3, ST3 by lia.
      replace (ret_pc (Z_to_bv 64 0x9aa14)) with (Z_to_bv 64 0x9aa14 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RDI as (Rfd & Rch & Rbs & Rnd & Rnw & Rwa & Rwb & Rsw & Rlbf & Reof).
      rewrite <- (wfn_of_rd f2 f3 Rsw), <- (lbf_of_rd f2 f3 Rlbf) in FC3. rewrite Tbs, Tfd in FC3. rewrite Tbs in BUF3, RREL3.
      rewrite ?Ibs, ?Ifd in FC3. rewrite ?Ibs in BUF3. rewrite ?Ibs in RREL3.
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ m2 m3); [exact FR2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (DSTa3 : rw_cells asegs m3 D [CB (length acc) (to_bytes acc)]).
      { eapply (rw_cells_transport asegs _ m2 m3); [exact DSTa | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (MU13 : munch fr_W m m3).
      { apply (munch_trans _ m m2 m3); [exact MU12|]. eapply munch_weaken; [| exact MU3].
        unfold fr_W, FREAD_DEPTH. intros a. cbn [outside fst snd]. clear - Tbs Ibs OFF OL L1 SPHI LO. intros Ha. lia. }
      assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM12 | exact WM3]).
      destruct SSP3 as [GOT3 GUARD3].
      assert (FRI3 : fr_inv f0 f3) by (unfold fr_inv; repeat split; congruence).
      pose proof (bytes_at_bound _ _ _ _ (rw_cells_bytes_at _ _ _ _ DST3)) as BB3. cbn [cells_bytes cbytes] in BB3.
      rewrite ?length_app, ?length_to_bytes, ?length_skipn in BB3.
      (* [comment removed for export] *)
      assert (DJ : rw_cells asegs m3 D [CB (length (acc ++ bsr)) (to_bytes (acc ++ bsr)); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]).
      { pose proof (proj2 (rw_cells_app asegs m3 D [CB (length acc) (to_bytes acc)] [CB (length bsr) (to_bytes bsr); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)])) as J.
        cbn [cells_size csize Nat.add] in J. rewrite ?Nat.add_0_r in J. replace (D + Z.of_nat (length acc)) with (D + off) in J by lia.
        specialize (J (conj DSTa3 DST3)).
        apply (rw_cells_merge asegs m3 D [] [CB (length acc) (to_bytes acc); CB (length bsr) (to_bytes bsr)] [CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]) in J.
        cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J.
        rewrite length_app, to_bytes_app'. exact J. }
      clear DSTa DST3 FC DST2 BUF2 MU3 WM3.
      pose proof FC3 as FC. unfold fcells, file_cells in FC.
      apply implAM_from_evt. zs.
      destruct bsr as [|c0 bsr'].
      + (* [comment removed for export] *)
        if_cases Hz; zify_cond Hz. 2:{ exfalso. unfold zlength in Hz. cbn [length Z.of_nat] in Hz. rewrite ?Z.mod_small in Hz by lia. lia. }
        zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
        zs. zs. rewrite divu_one. do 10 zs.
        release_frame FR3 ST3 (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold fread_post. cbn [fst snd].
        split; [reflexivity|]. split; [exact FRI3|]. split; [lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (n - l) with (zlength acc) by (unfold zlength; lia).
        do 14 eexists. exists x29, x14, x30, x31, (skipn 0 rest), m3.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU13|]. split; [exact WM13|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact FC3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact RREL3|]. split; [lia|]. split; [lia|].
        split; [rewrite app_nil_r in DJ; cbn [length] in DJ; rewrite Nat.sub_0_r in DJ; replace (Z.to_nat n - length acc)%nat with (Z.to_nat l) by lia; exact DJ|].
        split; [exact GOT3 | exact GUARD3].
      + unfold zlength in *. cbn [length] in *.
        if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
        zs. zs. zs.
        if_cases Hl; zify_cond Hl.
        * (* [comment removed for export] *)
          apply evtF_done.
          assert (RB3 : f_rbuf f3 = []) by (apply RBE; unfold zlength in *; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia).
          rewrite RB3 in FC3. unfold zlength in FC3. cbn [length Z.of_nat] in FC3. rewrite Z.add_0_r in FC3.
          replace (D + off + Z.of_nat (S (length bsr'))) with (D + (off + Z.of_nat (S (length bsr')))) by lia.
          eapply implM_at_eq; [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f3 x29 x14 x30 x31 (skipn (S (length bsr')) rest) (acc ++ c0 :: bsr') (off + Z.of_nat (S (length bsr'))) (l - Z.of_nat (S (length bsr'))) m3) | cbv delta [mkR]; reflexivity];
            [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FRI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [replace (Z.to_nat (l - Z.of_nat (S (length bsr')))) with (Z.to_nat l - S (length bsr'))%nat by lia; exact DJ]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia]) | unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [solve [frange]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT3 | exact GUARD3]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MU13]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WM13]) ].
        * (* [comment removed for export] *)
          zs. zs. zs. rewrite retval_size1 by lia. zs. if_true. do 10 zs.
          release_frame FR3 ST3 (bv_unsigned sp).
          apply evtF_done.
          destruct fuel as [|fuel']; [apply implAM_unr|].
          cbn [fread_loop]. replace (l - Z.of_nat (S (length bsr')) <=? 0) with true by (symmetry; apply Z.leb_le; lia).
          apply implAM_ret. apply evtF_done.
          unfold fread_post. cbn [fst snd].
          split; [reflexivity|]. split; [exact FRI3|]. split; [rewrite length_app; unfold zlength in *; cbn [length] in *; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
          replace (zlength (acc ++ c0 :: bsr')) with n by (unfold zlength in *; rewrite length_app; cbn [length] in *; lia).
          do 14 eexists. exists x29, x14, x30, x31, (skipn (length (c0 :: bsr')) rest), m3.
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU13|]. split; [exact WM13|]. split; [exact MI3|]. split; [exact ST3|].
          split; [exact FC3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact RREL3|]. split; [exact RP3|]. split; [exact RP3'|].
          split; [replace (Z.to_nat n - length (acc ++ c0 :: bsr'))%nat with (Z.to_nat l - S (length bsr'))%nat by (rewrite length_app; cbn [length]; clear - OFF OL NB; lia); exact DJ|].
          split; [exact GOT3 | exact GUARD3].
  Qed.

End Fread.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD : Z := 0x9ad38.
Definition FREAD_LOOP : Z := 0x9add8.
Definition FREAD_DEPTH : Z := 2304.   (* [comment removed for export] *)

Lemma to_bytes_app' : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

Lemma divu_one : forall a : word, mul_div M_DIVU a (Z_to_bv 64 1) = a.
Proof.
  intros a. unfold mul_div. cbn [bv_unsigned Z.eqb].
  replace (bv_unsigned (Z_to_bv 64 1) =? 0) with false by reflexivity. cbv iota.
  apply bv_eq. rewrite bv_divu_unsigned. change (bv_unsigned (Z_to_bv 64 1)) with 1. apply Z.div_1_r.
Qed.

Lemma retval_size1 : forall nmemb, 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) nmemb = nmemb.
Proof.
  intros nmemb Hn. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma wfn_of_rd : forall f f', f_stdoutw f' = f_stdoutw f -> wfn_of f' = wfn_of f.
Proof. intros f f' E. unfold wfn_of. rewrite E. reflexivity. Qed.
Lemma lbf_of_rd : forall f f', f_lbf_nl f' = f_lbf_nl f -> lbf_of f' = lbf_of f.
Proof. intros f f' E. unfold lbf_of. rewrite E. reflexivity. Qed.

Section Fread.
  Context {rc : runConstT}.
  Context {St : Type}.

  Lemma implM_retb : forall {A B} RNG (a : A) (k : A -> M St B) (s : St) Q ms,
    implAM RNG (k a) s Q ms -> implAM RNG (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B RNG a k s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Definition fr_inv (f0 f : file_st) : Prop :=
    f_fd f = f_fd f0 /\ f_chan f = f_chan f0 /\ f_bufsize f = f_bufsize f0 /\ f_nord f = f_nord f0 /\ f_nowr f = f_nowr f0
    /\ f_wactive f = false /\ f_wbuf f = [].

  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Definition fr_W : list (Z * Z) := [(bv_unsigned sp - FREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + n)].

  Definition fread_post : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fr_inv f0 (snd r) /\ Z.of_nat (length (fst r)) <= n /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (rp' : Z) (bufbytes' rest' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch fr_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 F_STDIO_READ (wfn_of (snd r)) seekfn B bs prev next (f_fd f0) mode' (lbf_of (snd r)) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells asegs m' B [CB (Z.to_nat bs) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + bs
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells asegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat n - length (fst r)) rest']
      /\ ssp_cells m' canary.

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis DSEP1 : D + n <= got_ssp \/ got_ssp + 8 <= D.
  Hypothesis DSEP2 : D + n <= ssp_guard \/ ssp_guard + 8 <= D.
  Hypothesis B0 : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis D0 : 0 <= D.
  Hypothesis D47 : D + n <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis SD1 : D + n <= lo \/ bv_unsigned sp <= D.
  Hypothesis SD2 : D + n <= Fp \/ Fp + 232 <= D.
  Hypothesis SD3 : D + n <= B \/ B + bs <= D.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B bs.
  Hypothesis RD : rng RNG D n.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis R0 : rng0 RNG.

  (* [comment removed for export] *)
  Lemma fread_loop_spec : forall fuel (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fcur : file_st) (flags1 mode1 : word) (rp1 : Z)
      (bufbytes1 rest : list byte) (acc : list Z) (off l : Z) (m1 : mem),
    rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 Fp (fcells flags1 rp1 rp1 closefn 0 0 0 F_STDIO_READ (wfn_of fcur) seekfn B bs prev next (f_fd f0) mode1 (lbf_of fcur) tail) ->
    flags_ok fcur flags1 -> fr_inv f0 fcur -> f_rbuf fcur = [] -> 0 <= rp1 < 2^63 ->
    rw_cells asegs m1 B [CB (Z.to_nat bs) bufbytes1] ->
    rw_cells asegs m1 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest] -> off = zlength acc -> off + l = n -> 1 <= l ->
    Forall (fun z => 0 <= z < 256) acc ->
    ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -64) -> mem_inv asegs m1 ->
    munch fr_W m m1 -> wmono asegs m m1 ->
    implAM RNG (fread_loop fuel fcur B (D + off) l acc) st fread_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 (D + off)) (Z_to_bv 64 l) (Z_to_bv 64 1) (Z_to_bv 64 n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREAD_LOOP) fc None m1 (seg_rom asegs)).
  Proof using B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 RSTK RFP RBUF RD RIMG R0. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 : unit) => tt).
    induction fuel as [|fuel IH]; intros until m1; intros FR1 FC1 FL1 INV1 RB1 RP1 BUF1 DST1 OFF OL L1 FACC SSP1 ST1 MI1 MU1 WM1.
    { cbn [fread_loop]. apply implAM_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_LOOP, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    destruct INV1 as (Ifd & Ich & Ibs & Ind & Inw & Iwa & Iwb).
    pose proof (rw_cells_bound _ _ _ _ DST1) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
    assert (LACC : length (to_bytes acc) = length acc) by apply length_to_bytes.
    unfold zlength in OFF.
    cbn [fread_loop]. replace (l <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    eapply implAM_bind.
    { pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fr_W, FREAD_DEPTH in MU1.
      apply implAM_from_evt. zs. zs.
      apply evtF_done.
      eapply (toread_spec (St:=St)) with (f := fcur) (Fp := Fp) (flags := flags1) (rpos := rp1) (rend := rp1) (closefn := closefn) (readfn := F_STDIO_READ)
        (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode1) (tail := tail) (bufbytes := bufbytes1) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; rewrite ?Iwa, ?Ibs, ?Ifd, ?Iwb, ?Ich.
      all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (proj1 FL1)]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (proj1 (proj2 (proj2 FL1)))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (proj1 (proj2 (proj2 (proj2 (proj2 FL1)))))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [rewrite NCH; exact FD]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SSP0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold TOREAD_DEPTH; lia]) | unfold TOREAD_DEPTH; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [(lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF | exact RD
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | rewrite ?Tbs, ?Ibs; lia] | eapply rng_sub'; [exact RD | lia]])]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RBUF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact R0]) ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [fst snd] in He, TRI. destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold tr_W, TOREAD_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x9ade0)) with (Z_to_bv 64 0x9ade0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof TRI as TRI'. destruct TRI as (Tfd & Tch & Tbs & Tnd & Tnw & Teof & Twa & Twb & Trb & _).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BUF2 : rw_cells asegs m2 B [CB (Z.to_nat (f_bufsize f0)) bufbytes1]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (DST2 : rw_cells asegs m2 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact DST1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (MU12 : munch fr_W m m2).
    { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fr_W, FREAD_DEPTH; cbn [outside]; intros; lia. }
    assert (WM12 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    assert (FL2 : flags_ok f2 flags1) by (unfold flags_ok in *; rewrite ?Tch, Tnd, Tnw, Teof; first [exact FL1 | rewrite <- ?Tch; exact FL1]).
    clear FR1 BUF1 DST1 MU2 WM2 MI1 ST1.
    pose proof FC2 as FC. unfold fcells, file_cells in FC.
    destruct SSP2 as [GOT2 GUARD2].
    cbn [fst snd] in *. subst e.
    apply implAM_from_evt.
    destruct (f_eof fcur) eqn:EOF.
    - (* [comment removed for export] *)
      cbn [Z.b2z Z.opp]. zs. if_cases Hx; zify_cond Hx. 2:{ exfalso. vm_compute in Hx. lia. }
      apply evtF_done. apply implM_retb. apply implAM_ret.
      zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
      zs. zs. rewrite divu_one. do 10 zs.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. cbn [fst snd].
      unfold fread_post. cbn [fst snd].
      split; [reflexivity|]. split; [unfold fr_inv; repeat split; first [congruence | assumption]|]. split; [lia|]. split; [solve [frange]|]. split; [solve [frange]|].
      replace (n - l) with (zlength acc) by (unfold zlength; lia).
      do 14 eexists. exists flags1, x14, (B + f_bufsize fcur), bufbytes1, rest, m2.
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU12|]. split; [exact WM12|]. split; [exact MI2|]. split; [exact ST2|].
      rewrite Trb. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      split; [unfold fcells, file_cells; rewrite <- ?Ibs, <- ?Ifd; exact FC|]. split; [exact FL2|].
      split; [exact BUF2|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
      split; [replace (Z.to_nat n - length acc)%nat with (Z.to_nat l) by lia; exact DST2|]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      cbn [Z.b2z Z.opp]. zs. if_cases Hx; zify_cond Hx. 1:{ exfalso. vm_compute in Hx. lia. }
      zs. zs. zs. zs. unfold F_STDIO_READ at 1. zs.
      apply evtF_done. cbv beta.
      (* [comment removed for export] *)
      pose proof DST2 as DSTa. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in DSTa. destruct DSTa as [DSTa DSTb].
      cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r, ?LACC in DSTb.
      replace (D + Z.of_nat (length acc)) with (D + off) in DSTb by lia.
      eapply implAM_bind.
      { eapply (stdio_read_spec (St:=St)) with (f := f2) (Fp := Fp) (flags := flags1) (rp := B + f_bufsize fcur) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := _) (tail := tail) (bufbytes := bufbytes1) (D := D + off) (len := l) (djunk := rest)
          (lo := lo) (canary := canary);
          rewrite ?unsigned_lit by lia; rewrite ?Tfd, ?Tch, ?Tbs, ?Ifd, ?Ich, ?Ibs.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; rewrite <- ?Ibs, <- ?Ifd; exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact DSTb]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Twa]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Twb]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Trb]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NCH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FD]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact L1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT2 | exact GUARD2]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_READ_DEPTH; lia]) | unfold STDIO_READ_DEPTH; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SB2]) | unfold STDIO_READ_DEPTH; lia | unfold STDIO_READ_DEPTH; lia | unfold STDIO_READ_DEPTH; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [(lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF | exact RD
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | rewrite ?Tbs, ?Ibs; lia] | eapply rng_sub'; [exact RD | lia]])]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RBUF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [(lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF | exact RD
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | rewrite ?Tbs, ?Ibs; lia] | eapply rng_sub'; [exact RD | lia]])]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros [bsr f3] st3 ms3 (-> & RDI & BL & RBE & GF3 & GRB3 & PO). cbn [fst snd] in RDI, BL, RBE, PO |- *. destruct_exs PO.
      destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & FL3 & BUF3 & RREL3 & RP3 & RP3' & DST3 & SSP3).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      unfold rd_W, STDIO_READ_DEPTH in MU3. rewrite !unsigned_lit in MU3, ST3 by lia.
      replace (ret_pc (Z_to_bv 64 0x9adf8)) with (Z_to_bv 64 0x9adf8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RDI as (Rfd & Rch & Rbs & Rnd & Rnw & Rwa & Rwb & Rsw & Rlbf & Reof).
      rewrite <- (wfn_of_rd f2 f3 Rsw), <- (lbf_of_rd f2 f3 Rlbf) in FC3. rewrite Tbs, Tfd in FC3. rewrite Tbs in BUF3, RREL3.
      rewrite ?Ibs, ?Ifd in FC3. rewrite ?Ibs in BUF3. rewrite ?Ibs in RREL3.
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ m2 m3); [exact FR2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (DSTa3 : rw_cells asegs m3 D [CB (length acc) (to_bytes acc)]).
      { eapply (rw_cells_transport asegs _ m2 m3); [exact DSTa | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (MU13 : munch fr_W m m3).
      { apply (munch_trans _ m m2 m3); [exact MU12|]. eapply munch_weaken; [| exact MU3].
        unfold fr_W, FREAD_DEPTH. intros a. cbn [outside fst snd]. clear - Tbs Ibs OFF OL L1 SPHI LO. intros Ha. lia. }
      assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM12 | exact WM3]).
      destruct SSP3 as [GOT3 GUARD3].
      assert (FRI3 : fr_inv f0 f3) by (unfold fr_inv; repeat split; congruence).
      pose proof (bytes_at_bound _ _ _ _ (rw_cells_bytes_at _ _ _ _ DST3)) as BB3. cbn [cells_bytes cbytes] in BB3.
      rewrite ?length_app, ?length_to_bytes, ?length_skipn in BB3.
      (* [comment removed for export] *)
      assert (DJ : rw_cells asegs m3 D [CB (length (acc ++ bsr)) (to_bytes (acc ++ bsr)); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]).
      { pose proof (proj2 (rw_cells_app asegs m3 D [CB (length acc) (to_bytes acc)] [CB (length bsr) (to_bytes bsr); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)])) as J.
        cbn [cells_size csize Nat.add] in J. rewrite ?Nat.add_0_r in J. replace (D + Z.of_nat (length acc)) with (D + off) in J by lia.
        specialize (J (conj DSTa3 DST3)).
        apply (rw_cells_merge asegs m3 D [] [CB (length acc) (to_bytes acc); CB (length bsr) (to_bytes bsr)] [CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]) in J.
        cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J.
        rewrite length_app, to_bytes_app'. exact J. }
      clear DSTa DST3 FC DST2 BUF2 MU3 WM3.
      pose proof FC3 as FC. unfold fcells, file_cells in FC.
      apply implAM_from_evt. zs.
      destruct bsr as [|c0 bsr'].
      + (* [comment removed for export] *)
        if_cases Hz; zify_cond Hz. 2:{ exfalso. unfold zlength in Hz. cbn [length Z.of_nat] in Hz. rewrite ?Z.mod_small in Hz by lia. lia. }
        zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
        zs. zs. rewrite divu_one. do 10 zs.
        release_frame FR3 ST3 (bv_unsigned sp).
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold fread_post. cbn [fst snd].
        split; [reflexivity|]. split; [exact FRI3|]. split; [lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (n - l) with (zlength acc) by (unfold zlength; lia).
        do 14 eexists. exists x29, x14, x30, x31, (skipn 0 rest), m3.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU13|]. split; [exact WM13|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact FC3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact RREL3|]. split; [lia|]. split; [lia|].
        split; [rewrite app_nil_r in DJ; cbn [length] in DJ; rewrite Nat.sub_0_r in DJ; replace (Z.to_nat n - length acc)%nat with (Z.to_nat l) by lia; exact DJ|].
        split; [exact GOT3 | exact GUARD3].
      + unfold zlength in *. cbn [length] in *.
        if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
        zs. zs. zs.
        if_cases Hl; zify_cond Hl.
        * (* [comment removed for export] *)
          apply evtF_done.
          assert (RB3 : f_rbuf f3 = []) by (apply RBE; unfold zlength in *; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia).
          rewrite RB3 in FC3. unfold zlength in FC3. cbn [length Z.of_nat] in FC3. rewrite Z.add_0_r in FC3.
          replace (D + off + Z.of_nat (S (length bsr'))) with (D + (off + Z.of_nat (S (length bsr')))) by lia.
          eapply implM_at_eq; [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f3 x29 x14 x30 x31 (skipn (S (length bsr')) rest) (acc ++ c0 :: bsr') (off + Z.of_nat (S (length bsr'))) (l - Z.of_nat (S (length bsr'))) m3) | cbv delta [mkR]; reflexivity];
            [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FRI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [replace (Z.to_nat (l - Z.of_nat (S (length bsr')))) with (Z.to_nat l - S (length bsr'))%nat by lia; exact DJ]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia]) | unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [solve [frange]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT3 | exact GUARD3]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MU13]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WM13]) ].
        * (* [comment removed for export] *)
          zs. zs. zs. rewrite retval_size1 by lia. zs. if_true. do 10 zs.
          release_frame FR3 ST3 (bv_unsigned sp).
          apply evtF_done.
          destruct fuel as [|fuel']; [apply implAM_unr|].
          cbn [fread_loop]. replace (l - Z.of_nat (S (length bsr')) <=? 0) with true by (symmetry; apply Z.leb_le; lia).
          apply implAM_ret. apply evtF_done.
          unfold fread_post. cbn [fst snd].
          split; [reflexivity|]. split; [exact FRI3|]. split; [rewrite length_app; unfold zlength in *; cbn [length] in *; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
          replace (zlength (acc ++ c0 :: bsr')) with n by (unfold zlength in *; rewrite length_app; cbn [length] in *; lia).
          do 14 eexists. exists x29, x14, x30, x31, (skipn (length (c0 :: bsr')) rest), m3.
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU13|]. split; [exact WM13|]. split; [exact MI3|]. split; [exact ST3|].
          split; [exact FC3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact RREL3|]. split; [exact RP3|]. split; [exact RP3'|].
          split; [replace (Z.to_nat n - length (acc ++ c0 :: bsr'))%nat with (Z.to_nat l - S (length bsr'))%nat by (rewrite length_app; cbn [length]; clear - OFF OL NB; lia); exact DJ|].
          split; [exact GOT3 | exact GUARD3].
  Qed.

End Fread.
End TwB.
End F_fread.

(* [comment removed for export] *)
Module F_fread_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import PerfA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac disjoint_goal ::= disjoint_goal_rel.  Local Ltac tlia ::= tlia_rel.  Local Ltac slia ::= slia_rel.   (* [comment removed for export] *)
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= lia_rel_pin.   (* [comment removed for export] *)
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rw_cells_CB0' : forall m A n bs, rw_cells asegs m A [CB n bs] -> rw_cells asegs m A [CB n bs; CB 0 []].
Proof.
  intros m A n bs [[W B] R]. split; [split|].
  - cbn in *. repeat split; try reflexivity. exact (proj1 W).
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact B.
  - cbn [cells_size csize Nat.add] in *. rewrite Nat.add_0_r in *. exact R.
Qed.

Section FreadMain.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis DSEP1 : D + n <= got_ssp \/ got_ssp + 8 <= D.
  Hypothesis DSEP2 : D + n <= ssp_guard \/ ssp_guard + 8 <= D.
  Hypothesis B0 : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis D0 : 0 <= D.
  Hypothesis D47 : D + n <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis SD1 : D + n <= lo \/ bv_unsigned sp <= D.
  Hypothesis SD2 : D + n <= Fp \/ Fp + 232 <= D.
  Hypothesis SD3 : D + n <= B \/ B + bs <= D.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + bs)].
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis APWF : appW [(Fp, Fp + 232)].
  Hypothesis SOB : sobj RNG m B (B + bs).
  Hypothesis SOD : sobj RNG m D (D + n).
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B bs.
  Hypothesis RD : rng RNG D n.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis R0 : rng0 RNG.

  (* [comment removed for export] *)
  Definition fread_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp : Z) (bufbytes djunk : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      flags_ok f0 flags ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] ->
      (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs /\ firstn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes) = to_bytes (f_rbuf f0)) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      rw_cells asegs m D [CB (Z.to_nat n) djunk] ->
      f_wactive f0 = false -> f_wbuf f0 = [] -> Forall (fun z => 0 <= z < 256) (f_rbuf f0) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Fp ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      implAM RNG (fread_file f0 B D n) st (fread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk : ltac2:(SecDiet.SzSec.tyM 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO : unit) => tt).
    intros FC FL BUF RREL RP0 RPHI DST WACT WB0 RBR -> -> -> -> ST SSP MI.
    pose proof (sobj_appW _ _ _ _ SOB) as APWB. pose proof (sobj_appW _ _ _ _ SOD) as APWD.
    (* [comment removed for export] *)
    change (?P) with (sf_hide P) in BSEP1; change (?P) with (sf_hide P) in BSEP2.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (fr_W sp f0 Fp B D n) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold fr_W, FREAD_DEPTH in MU.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    unfold fread_file. cbv zeta.
    apply implAM_from_evt.
    carve_frame 64%nat ST.
    try clear FC0; (do 9 zs). do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    assert (CASES : f_rbuf f0 = [] \/ f_rbuf f0 <> []) by (destruct (f_rbuf f0); [left; reflexivity | right; discriminate]).
    destruct CASES as [RB | RB].
    - (* [comment removed for export] *)
      rewrite RB in *. unfold zlength in *. cbn [length Z.of_nat Z.to_nat firstn skipn] in *. rewrite Z.min_l by lia. rewrite Z.add_0_r in FC |- *. rewrite Z.add_0_r, Z.sub_0_r.
      cbn [Z.to_nat firstn skipn].
      if_true.
      change (Z.to_nat (Z.of_nat 0)) with 0%nat. rewrite !skipn_O, !firstn_O.
      zs. rewrite Z.mul_1_r. zs. if_cases Hn; zify_cond Hn.
      + (* [comment removed for export] *)
        apply evtF_done.
        replace (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B D n []) with (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B (D + 0) n [] : M St (list Z * file_st)) by (rewrite Z.add_0_r; reflexivity).
        eapply implM_at_eq; [eapply (fread_loop_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 RSTK RFP RBUF RD RIMG R0 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf [] f0) flags _ rp bufbytes djunk [] 0 n)
                            | cbv delta [mkR]; rewrite Z.add_0_r; reflexivity];
          first [ exact FR | exact FC | exact FL | exact BUF | apply rw_cells_CB0; exact DST | exact ST | exact MI | exact MU | exact WM | solve [frange]
                | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                | unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]
                | reflexivity | rewrite ?Z.mod_small in Hn by lia; lia
                | match goal with |- ?g => idtac "FL0:" g end ].
      + (* [comment removed for export] *)
        zs. zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. cbn [fread_loop]. change (n <=? 0) with (n <=? 0).
        replace (n <=? 0) with true by (symmetry; apply Z.leb_le; rewrite ?Z.mod_small in Hn by lia; lia).
        apply implAM_ret. apply evtF_done.
        unfold fread_post. cbn [fst snd f_rbuf set_rbuf length to_bytes map].
        split; [reflexivity|]. split; [unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]|]. split; [lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (Z_to_bv 64 n : word) with (Z_to_bv 64 (zlength (@nil Z)) : word) by (f_equal; unfold zlength; cbn; rewrite ?Z.mod_small in Hn by lia; lia).
        do 14 eexists. exists flags, (Z_to_bv 64 (Z.lor ((bv_unsigned (sx32 mode) + -1) mod 18446744073709551616) (bv_unsigned (sx32 mode)))), rp, bufbytes, djunk, m0.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [exact FL|]. split; [exact BUF|].
        split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat n - 0)%nat with 0%nat by (rewrite ?Z.mod_small in Hn by lia; lia); replace (Z.to_nat n) with 0%nat in DST by (rewrite ?Z.mod_small in Hn by lia; lia); apply rw_cells_CB0; exact DST|].
        split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      specialize (RREL RB).  destruct RREL as (RR1 & RR2 & RR3).
      assert (NB1 : 1 <= zlength (f_rbuf f0)) by (destruct (f_rbuf f0); [exfalso; exact (RB eq_refl) | unfold zlength; cbn; lia]).
      unfold zlength in *.
      if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. rewrite Z.mul_1_r. zs.
      (* [comment removed for export] *)
      assert (SRCB : bytes_at asegs m0 rp (to_bytes (f_rbuf f0))).
      { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
        pose proof (rw_cells_bound _ _ _ _ BUF) as BBn. cbn [cells_size csize] in BBn.
        assert (LBB : length bufbytes = Z.to_nat (f_bufsize f0)) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
        pose proof (bytes_at_skipn _ _ _ (Z.to_nat (rp - B)) BB ltac:(lia)) as BSK. replace (B + Z.of_nat (Z.to_nat (rp - B))) with rp in BSK by lia.
        rewrite <- RR3. rewrite <- (firstn_skipn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes)) in BSK.
        exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BSK)). }
      replace (rp + Z.of_nat (length (f_rbuf f0)) - rp) with (Z.of_nat (length (f_rbuf f0))) by lia.
      pose proof (bytes_at_bound _ _ _ _ SRCB) as SB. rewrite length_to_bytes in SB.
      assert (LBB : length bufbytes = Z.to_nat (f_bufsize f0)) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
      if_cases Hc; zify_cond Hc.
      * (* [comment removed for export] *)
        rewrite !Z.min_l by lia.
        zs. zs.
        pose proof DST as DST0.
        apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) djunk [] [length (f_rbuf f0); Z.to_nat n - length (f_rbuf f0)]%nat) in DST0; [| cbn; lia].
        cbn [mk_CB_cells app] in DST0.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
        cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r in DSTb.
        clear DST. zs.
        ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOD MU WM as SODn.
        change (?P) with (sf_hide P) in FSEP1; change (?P) with (sf_hide P) in FSEP2; change (?P) with (sf_hide P) in SB2.
        call memcpy_wb_spec.
        1:{ exact SRCB. }
        1:{ rewrite length_to_bytes, Nat2Z.id. reflexivity. }
        1:{ rewrite Nat2Z.id. exact DSTa. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KLO. } 1:{ exact ENVn. }
        1:{ eapply sobj_sub; [exact SOBn | lia | lia | lia]. } 1:{ eapply sobj_sub; [exact SODn | lia | lia | lia]. } 1:{ lia. } 1:{ lia. }
        all: try (lazymatch goal with |- rng _ _ _ => first [eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | lia] | eapply rng_sub'; [exact RD | lia]] end).
        try clear ST. rename PC into ST. rename PC0 into PC.
        unfold sf_hide in FSEP1, FSEP2, SB2.
        rewrite !Nat2Z.id in *.
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 1:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        apply evtF_done.
        lazymatch goal with |- implAM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
        rewrite firstn_all.
        lazymatch goal with DB : rw_cells asegs mA (D + Z.of_nat (length (f_rbuf f0))) _ |- _ => rename DB into DSTb' | _ => idtac "noDSTb" end.
        assert (DJ : rw_cells asegs mA D [CB (length (f_rbuf f0)) (to_bytes (f_rbuf f0)); CB (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) (firstn (Z.to_nat n - length (f_rbuf f0)) (skipn (length (f_rbuf f0)) djunk))]).
        { apply (proj2 (rw_cells_app asegs mA D [_] [_])). cbn [cells_size csize Nat.add]. rewrite ?Nat.add_0_r. split; [exact PC|].
          replace (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) with (Z.to_nat n - length (f_rbuf f0))%nat by lia. exact DSTb'. }
        eapply (fread_loop_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 RSTK RFP RBUF RD RIMG R0 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf (skipn (length (f_rbuf f0)) (f_rbuf f0)) f0) flags _ (rp + Z.of_nat (length (f_rbuf f0))) bufbytes);
          fastfirst (first [ noevar_assumption | exact FR | exact FC | exact FL | exact DJ | exact ST | exact MI | exact MU | exact WM | solve [frange]
                | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                | unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]
                | cbn [f_rbuf set_rbuf]; apply skipn_all
                | unfold zlength; rewrite ?Z.mod_small in Hl by lia; lia
                | assumption
                ]).
      * (* [comment removed for export] *)
        rewrite !Z.min_r by lia.
        zs. zs. zs.
        assert (SRCn : bytes_at asegs m0 rp (firstn (Z.to_nat n) (to_bytes (f_rbuf f0)))).
        { rewrite <- (firstn_skipn (Z.to_nat n) (to_bytes (f_rbuf f0))) in SRCB. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRCB)). }
        clear SRCB. zs.
        ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOD MU WM as SODn.
        change (?P) with (sf_hide P) in FSEP1; change (?P) with (sf_hide P) in FSEP2; change (?P) with (sf_hide P) in SB2.
        call memcpy_wb_spec.
        1:{ exact SRCn. }
        1:{ rewrite length_firstn, length_to_bytes. lia. }
        1:{ exact DST. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KLO. } 1:{ exact ENVn. }
        1:{ eapply sobj_sub; [exact SOBn | lia | lia | lia]. } 1:{ exact SODn. } 1:{ lia. } 1:{ lia. }
        all: try (lazymatch goal with |- rng _ _ _ => first [eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | lia] | eapply rng_sub'; [exact RD | lia]] end).
        try clear ST. rename PC into ST. rename PC0 into PC.
        unfold sf_hide in FSEP1, FSEP2, SB2.
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. cbn [fread_loop].
        replace (n - n <=? 0) with true by (symmetry; apply Z.leb_le; lia).
        apply implAM_ret. apply evtF_done.
        unfold fread_post. cbn [fst snd f_rbuf set_rbuf].
        split; [reflexivity|]. split; [unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]|].
        split; [rewrite length_firstn; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (zlength (firstn (Z.to_nat n) (f_rbuf f0))) with n by (unfold zlength; rewrite length_firstn; lia).
        lazymatch goal with H : mem_inv asegs mZ |- _ => rename H into MIZ end.
        do 14 eexists. eexists flags, _, (rp + n), bufbytes, [], mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MIZ|]. split; [exact ST|].
        unfold zlength. rewrite length_skipn.
        split. { unfold fcells, file_cells. replace (rp + n + Z.of_nat (length (f_rbuf f0) - Z.to_nat n)) with (rp + Z.of_nat (length (f_rbuf f0))) by lia. exact FC. }
        split; [exact FL|]. split; [exact BUF|].
        split. { intros _. split; [clear - RR1 NB; lia|]. split; [clear - RR1 RR2 Hc NB; lia|].
                 rewrite to_bytes_skipn, <- RR3. replace (Z.to_nat (rp + n - B)) with (Z.to_nat n + Z.to_nat (rp - B))%nat by (clear - RR1 NB; lia).
                 rewrite <- skipn_skipn, skipn_firstn_comm. reflexivity. }
        split; [clear - RP0 RR1 NB; lia|]. split; [clear - RPHI Hc NB RP0; lia|].
        split. { rewrite length_firstn, to_bytes_firstn. replace (Nat.min (Z.to_nat n) (length (f_rbuf f0))) with (Z.to_nat n) by lia. rewrite Nat.sub_diag. apply rw_cells_CB0'. exact PC. }
        split; [exact GOT | exact GUARD].
  Qed.
  End Sz2.
  Theorem fread_spec : ltac:(let t := eval cbv delta [fread_spec__stmt] in fread_spec__stmt in exact t).
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk. ltac2:(SecDiet.SzSec.closeP 'fread_spec__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End FreadMain.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.PerfA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac disjoint_goal ::= disjoint_goal_rel.  Local Ltac tlia ::= tlia_rel.  Local Ltac slia ::= slia_rel.   (* [comment removed for export] *)
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= lia_rel_pin.   (* [comment removed for export] *)
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rw_cells_CB0' : forall m A n bs, rw_cells asegs m A [CB n bs] -> rw_cells asegs m A [CB n bs; CB 0 []].
Proof.
  intros m A n bs [[W B] R]. split; [split|].
  - cbn in *. repeat split; try reflexivity. exact (proj1 W).
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact B.
  - cbn [cells_size csize Nat.add] in *. rewrite Nat.add_0_r in *. exact R.
Qed.

Section FreadMain.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis DSEP1 : D + n <= got_ssp \/ got_ssp + 8 <= D.
  Hypothesis DSEP2 : D + n <= ssp_guard \/ ssp_guard + 8 <= D.
  Hypothesis B0 : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis D0 : 0 <= D.
  Hypothesis D47 : D + n <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis SD1 : D + n <= lo \/ bv_unsigned sp <= D.
  Hypothesis SD2 : D + n <= Fp \/ Fp + 232 <= D.
  Hypothesis SD3 : D + n <= B \/ B + bs <= D.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + bs)].
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis APWF : appW [(Fp, Fp + 232)].
  Hypothesis SOB : sobj RNG m B (B + bs).
  Hypothesis SOD : sobj RNG m D (D + n).
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B bs.
  Hypothesis RD : rng RNG D n.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis R0 : rng0 RNG.

  (* [comment removed for export] *)
  Definition fread_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp : Z) (bufbytes djunk : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      flags_ok f0 flags ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] ->
      (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs /\ firstn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes) = to_bytes (f_rbuf f0)) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      rw_cells asegs m D [CB (Z.to_nat n) djunk] ->
      f_wactive f0 = false -> f_wbuf f0 = [] -> Forall (fun z => 0 <= z < 256) (f_rbuf f0) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Fp ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      implAM RNG (fread_file f0 B D n) st (fread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk : ltac2:(SecDiet.SzSec.tyM 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO : unit) => tt).
    intros FC FL BUF RREL RP0 RPHI DST WACT WB0 RBR -> -> -> -> ST SSP MI.
    pose proof (sobj_appW _ _ _ _ SOB) as APWB. pose proof (sobj_appW _ _ _ _ SOD) as APWD.
    (* [comment removed for export] *)
    change (?P) with (sf_hide P) in BSEP1; change (?P) with (sf_hide P) in BSEP2.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (fr_W sp f0 Fp B D n) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold fr_W, FREAD_DEPTH in MU.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    unfold fread_file. cbv zeta.
    apply implAM_from_evt.
    carve_frame 64%nat ST.
    try clear FC0; (do 9 zs). do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    assert (CASES : f_rbuf f0 = [] \/ f_rbuf f0 <> []) by (destruct (f_rbuf f0); [left; reflexivity | right; discriminate]).
    destruct CASES as [RB | RB].
    - (* [comment removed for export] *)
      rewrite RB in *. unfold zlength in *. cbn [length Z.of_nat Z.to_nat firstn skipn] in *. rewrite Z.min_l by lia. rewrite Z.add_0_r in FC |- *. rewrite Z.add_0_r, Z.sub_0_r.
      cbn [Z.to_nat firstn skipn].
      if_true.
      change (Z.to_nat (Z.of_nat 0)) with 0%nat. rewrite !skipn_O, !firstn_O.
      zs. rewrite Z.mul_1_r. zs. if_cases Hn; zify_cond Hn.
      + (* [comment removed for export] *)
        apply evtF_done.
        replace (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B D n []) with (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B (D + 0) n [] : M St (list Z * file_st)) by (rewrite Z.add_0_r; reflexivity).
        eapply implM_at_eq; [eapply (fread_loop_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 RSTK RFP RBUF RD RIMG R0 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf [] f0) flags _ rp bufbytes djunk [] 0 n)
                            | cbv delta [mkR]; rewrite Z.add_0_r; reflexivity];
          first [ exact FR | exact FC | exact FL | exact BUF | apply rw_cells_CB0; exact DST | exact ST | exact MI | exact MU | exact WM | solve [frange]
                | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                | unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]
                | reflexivity | rewrite ?Z.mod_small in Hn by lia; lia
                | match goal with |- ?g => idtac "FL0:" g end ].
      + (* [comment removed for export] *)
        zs. zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. cbn [fread_loop]. change (n <=? 0) with (n <=? 0).
        replace (n <=? 0) with true by (symmetry; apply Z.leb_le; rewrite ?Z.mod_small in Hn by lia; lia).
        apply implAM_ret. apply evtF_done.
        unfold fread_post. cbn [fst snd f_rbuf set_rbuf length to_bytes map].
        split; [reflexivity|]. split; [unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]|]. split; [lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (Z_to_bv 64 n : word) with (Z_to_bv 64 (zlength (@nil Z)) : word) by (f_equal; unfold zlength; cbn; rewrite ?Z.mod_small in Hn by lia; lia).
        do 14 eexists. exists flags, (Z_to_bv 64 (Z.lor ((bv_unsigned (sx32 mode) + -1) mod 18446744073709551616) (bv_unsigned (sx32 mode)))), rp, bufbytes, djunk, m0.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [exact FL|]. split; [exact BUF|].
        split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat n - 0)%nat with 0%nat by (rewrite ?Z.mod_small in Hn by lia; lia); replace (Z.to_nat n) with 0%nat in DST by (rewrite ?Z.mod_small in Hn by lia; lia); apply rw_cells_CB0; exact DST|].
        split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      specialize (RREL RB).  destruct RREL as (RR1 & RR2 & RR3).
      assert (NB1 : 1 <= zlength (f_rbuf f0)) by (destruct (f_rbuf f0); [exfalso; exact (RB eq_refl) | unfold zlength; cbn; lia]).
      unfold zlength in *.
      if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. rewrite Z.mul_1_r. zs.
      (* [comment removed for export] *)
      assert (SRCB : bytes_at asegs m0 rp (to_bytes (f_rbuf f0))).
      { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
        pose proof (rw_cells_bound _ _ _ _ BUF) as BBn. cbn [cells_size csize] in BBn.
        assert (LBB : length bufbytes = Z.to_nat (f_bufsize f0)) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
        pose proof (bytes_at_skipn _ _ _ (Z.to_nat (rp - B)) BB ltac:(lia)) as BSK. replace (B + Z.of_nat (Z.to_nat (rp - B))) with rp in BSK by lia.
        rewrite <- RR3. rewrite <- (firstn_skipn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes)) in BSK.
        exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BSK)). }
      replace (rp + Z.of_nat (length (f_rbuf f0)) - rp) with (Z.of_nat (length (f_rbuf f0))) by lia.
      pose proof (bytes_at_bound _ _ _ _ SRCB) as SB. rewrite length_to_bytes in SB.
      assert (LBB : length bufbytes = Z.to_nat (f_bufsize f0)) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
      if_cases Hc; zify_cond Hc.
      * (* [comment removed for export] *)
        rewrite !Z.min_l by lia.
        zs. zs.
        pose proof DST as DST0.
        apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) djunk [] [length (f_rbuf f0); Z.to_nat n - length (f_rbuf f0)]%nat) in DST0; [| cbn; lia].
        cbn [mk_CB_cells app] in DST0.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
        cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r in DSTb.
        clear DST. zs.
        ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOD MU WM as SODn.
        change (?P) with (sf_hide P) in FSEP1; change (?P) with (sf_hide P) in FSEP2; change (?P) with (sf_hide P) in SB2.
        call memcpy_wb_spec.
        1:{ exact SRCB. }
        1:{ rewrite length_to_bytes, Nat2Z.id. reflexivity. }
        1:{ rewrite Nat2Z.id. exact DSTa. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KLO. } 1:{ exact ENVn. }
        1:{ eapply sobj_sub; [exact SOBn | lia | lia | lia]. } 1:{ eapply sobj_sub; [exact SODn | lia | lia | lia]. } 1:{ lia. } 1:{ lia. }
        all: try (lazymatch goal with |- rng _ _ _ => first [eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | lia] | eapply rng_sub'; [exact RD | lia]] end).
        try clear ST. rename PC into ST. rename PC0 into PC.
        unfold sf_hide in FSEP1, FSEP2, SB2.
        rewrite !Nat2Z.id in *.
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 1:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        apply evtF_done.
        lazymatch goal with |- implAM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
        rewrite firstn_all.
        lazymatch goal with DB : rw_cells asegs mA (D + Z.of_nat (length (f_rbuf f0))) _ |- _ => rename DB into DSTb' | _ => idtac "noDSTb" end.
        assert (DJ : rw_cells asegs mA D [CB (length (f_rbuf f0)) (to_bytes (f_rbuf f0)); CB (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) (firstn (Z.to_nat n - length (f_rbuf f0)) (skipn (length (f_rbuf f0)) djunk))]).
        { apply (proj2 (rw_cells_app asegs mA D [_] [_])). cbn [cells_size csize Nat.add]. rewrite ?Nat.add_0_r. split; [exact PC|].
          replace (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) with (Z.to_nat n - length (f_rbuf f0))%nat by lia. exact DSTb'. }
        eapply (fread_loop_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 RSTK RFP RBUF RD RIMG R0 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf (skipn (length (f_rbuf f0)) (f_rbuf f0)) f0) flags _ (rp + Z.of_nat (length (f_rbuf f0))) bufbytes);
          fastfirst (first [ noevar_assumption | exact FR | exact FC | exact FL | exact DJ | exact ST | exact MI | exact MU | exact WM | solve [frange]
                | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                | unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]
                | cbn [f_rbuf set_rbuf]; apply skipn_all
                | unfold zlength; rewrite ?Z.mod_small in Hl by lia; lia
                | assumption
                ]).
      * (* [comment removed for export] *)
        rewrite !Z.min_r by lia.
        zs. zs. zs.
        assert (SRCn : bytes_at asegs m0 rp (firstn (Z.to_nat n) (to_bytes (f_rbuf f0)))).
        { rewrite <- (firstn_skipn (Z.to_nat n) (to_bytes (f_rbuf f0))) in SRCB. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRCB)). }
        clear SRCB. zs.
        ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOD MU WM as SODn.
        change (?P) with (sf_hide P) in FSEP1; change (?P) with (sf_hide P) in FSEP2; change (?P) with (sf_hide P) in SB2.
        call memcpy_wb_spec.
        1:{ exact SRCn. }
        1:{ rewrite length_firstn, length_to_bytes. lia. }
        1:{ exact DST. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KLO. } 1:{ exact ENVn. }
        1:{ eapply sobj_sub; [exact SOBn | lia | lia | lia]. } 1:{ exact SODn. } 1:{ lia. } 1:{ lia. }
        all: try (lazymatch goal with |- rng _ _ _ => first [eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | lia] | eapply rng_sub'; [exact RD | lia]] end).
        try clear ST. rename PC into ST. rename PC0 into PC.
        unfold sf_hide in FSEP1, FSEP2, SB2.
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        release_frame FR ST (bv_unsigned sp).
        apply evtF_done. cbn [fread_loop].
        replace (n - n <=? 0) with true by (symmetry; apply Z.leb_le; lia).
        apply implAM_ret. apply evtF_done.
        unfold fread_post. cbn [fst snd f_rbuf set_rbuf].
        split; [reflexivity|]. split; [unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]|].
        split; [rewrite length_firstn; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (zlength (firstn (Z.to_nat n) (f_rbuf f0))) with n by (unfold zlength; rewrite length_firstn; lia).
        lazymatch goal with H : mem_inv asegs mZ |- _ => rename H into MIZ end.
        do 14 eexists. eexists flags, _, (rp + n), bufbytes, [], mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MIZ|]. split; [exact ST|].
        unfold zlength. rewrite length_skipn.
        split. { unfold fcells, file_cells. replace (rp + n + Z.of_nat (length (f_rbuf f0) - Z.to_nat n)) with (rp + Z.of_nat (length (f_rbuf f0))) by lia. exact FC. }
        split; [exact FL|]. split; [exact BUF|].
        split. { intros _. split; [clear - RR1 NB; lia|]. split; [clear - RR1 RR2 Hc NB; lia|].
                 rewrite to_bytes_skipn, <- RR3. replace (Z.to_nat (rp + n - B)) with (Z.to_nat n + Z.to_nat (rp - B))%nat by (clear - RR1 NB; lia).
                 rewrite <- skipn_skipn, skipn_firstn_comm. reflexivity. }
        split; [clear - RP0 RR1 NB; lia|]. split; [clear - RPHI Hc NB RP0; lia|].
        split. { rewrite length_firstn, to_bytes_firstn. replace (Nat.min (Z.to_nat n) (length (f_rbuf f0))) with (Z.to_nat n) by lia. rewrite Nat.sub_diag. apply rw_cells_CB0'. exact PC. }
        split; [exact GOT | exact GUARD].
  Qed.
  End Sz2.
  Theorem fread_spec : ltac:(let t := eval cbv delta [fread_spec__stmt] in fread_spec__stmt in exact t).
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk. ltac2:(SecDiet.SzSec.closeP 'fread_spec__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End FreadMain.
End TwB.
End F_fread_top.
