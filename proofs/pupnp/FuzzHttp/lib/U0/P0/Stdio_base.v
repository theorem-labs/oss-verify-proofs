(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Walk ITree Nodes Decode SysStep SFModel.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Export F_syscalls.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).

Notation RSTDOUT := 0x2b570%Z (only parsing).
Notation RSTDOUT_BUF := 0x5bef0%Z (only parsing).
Notation RSTDERR := 0x2b480%Z (only parsing).
Notation RSTDERR_BUF := 0x5bee8%Z (only parsing).
Notation F_STDOUT_WRITE := 0x1b234%Z (only parsing).
Notation F_STDIO_WRITE := 0x1acfc%Z (only parsing).
Notation F_STDIO_CLOSE := 0x1a738%Z (only parsing).
Notation F_STDIO_SEEK := 0x1a764%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x1a738);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x1a764); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
   CB 80 tail].

Definition ssp_cells (m : mem) (canary : word) : Prop :=
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].

Definition stdout_file (m : mem) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells rsegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells rsegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells rsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE RSTDERR_BUF 0 2 mode 0xffffffff tail).

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap.
  change (bv_swrap 32 (e mod 2^64)) with (((e mod 2^64) + 2^31) mod 2^32 - 2^31)%Z.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
  (9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64)%Z with 18446744073709551616%Z in *.
  Z.div_mod_to_equations. lia.
Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma zb_to_bytes : forall l, to_bytes l = zb l.
Proof. reflexivity. Qed.
Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Definition boxed (P : Prop) : Prop := P.

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
    rewrite (cells_bytes_length cs1 W1) in B2. LiaTuning.ctauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. LiaTuning.ctauto.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at rsegs m' Src src.

Lemma memcpy_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
  evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x240e0) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ ?m _) => idtac "PC=" pc;
   repeat match goal with H : rw_cells _ m _ _ |- _ => let T := type of H in idtac H ":" T; fail end | |- ?G => idtac "NOT MS GOAL" G end.

Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl ?segs _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM segs c s Q ms) | _ => idtac end.

Ltac src_now SRC SEPS MU LSB :=
  unfold boxed in SRC;
  lazymatch goal with
  | |- bytes_at _ ?m' ?S (to_bytes ?s) =>
      destruct SEPS as [-> | [SEP1 SEP2]];
      [ apply bytes_at_nil; lia
      | apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
  end.
