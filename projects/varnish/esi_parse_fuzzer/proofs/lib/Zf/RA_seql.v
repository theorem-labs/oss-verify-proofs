(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1 RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition SN_WRITE : Z := 0xa15c0.
Definition GOT_SSP : Z := 0xa9818.       (* [comment removed for export] *)
Definition SSP_GUARD : Z := 0x607c18.     (* [comment removed for export] *)
Definition VSNPRINTF : Z := 0xa14f4.
Definition VFPRINTF : Z := 0x9e3c8.
Definition PRINTF_CORE : Z := 0x9e578.
Definition FWRITEX : Z := 0x9e008.
Definition TOWRITE : Z := 0x9e1f8.
Definition POP_ARG : Z := 0x9f3a8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x7fff7f800000.
Section CEIL.
Context {Clg : Ceiling}.
Lemma globals_top_ceiling : GLOBALS_TOP <= alloc_ceiling.
Proof. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold GLOBALS_TOP. lia. Qed.
End CEIL.
(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x60a000.
Definition dst_ok (D : Z) (n : nat) : Prop := (0 <= D)%Z /\ ~ (D < IMG_HI /\ IMG_LO < D + Z.of_nat n)%Z.
(* [comment removed for export] *)
Definition dst_zone (D n : Z) : Prop :=
  (kHighMemBeg_z <= D \/ (0x60a000 <= D /\ D + n <= 2147446784) \/ D + n <= 0x10000)%Z.
(* [comment removed for export] *)
Lemma dst_zone_sub : forall D n D' n', dst_zone D n -> (D <= D')%Z -> (D' + n' <= D + n)%Z -> dst_zone D' n'.
Proof. intros D n D' n' H H1 H2. unfold dst_zone in *. lia. Qed.
(* [comment removed for export] *)
Ltac solve_wlow ::= try (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv);
                    cbn [wlow]; unfold dst_zone, kHighMemBeg_z in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.

(* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells rsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] /\ ro_cells rsegs m SSP_GUARD [C8 canary].
  (* [comment removed for export] *)
Lemma lowP_ssp_cells : forall canary, lowP (fun m => ssp_cells m canary).
Proof. intros. apply lowP_and; apply lowP_ro_cells; cbn; unfold in_zone, GOT_SSP, SSP_GUARD, kHighMemBeg_z; lia. Qed.

Definition z64 : word := Z_to_bv 64 0.
Definition m1w : word := Z_to_bv 64 (-1).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition snfile (flags : word) (wend wpos wbase buf bufsize : Z) (mode : word) (CK : Z) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 SN_WRITE); C8 z64; C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 z64; C4 z64; C8 z64; C4 mode; C4 m1w; C4 m1w; C4 z64;
   C8 (Z_to_bv 64 CK);
   C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Lemma snfile_size : forall flags wend wpos wbase buf bufsize mode CK,
  cells_size (snfile flags wend wpos wbase buf bufsize mode CK) = 232%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section Sink.
  Variables (Fp B D : Z) (n : nat).
  Definition dl (w : list byte) : list byte := firstn (n - 1) w.

  Definition sink (m : word -> option byte) (mode : word) (w p : list byte) : Prop :=
    exists jb jd,
      rw_cells rsegs m Fp (snfile z64 (B + 80) (B + Z.of_nat (length p)) B B 80 mode (Fp + 232))
      /\ rw_cells rsegs m (Fp + 232) [C8 (Z_to_bv 64 (D + Z.of_nat (length (dl w))));
                                      C8 (Z_to_bv 64 ((Z.of_nat n - 1) - Z.of_nat (length (dl w))))]
      /\ rw_cells rsegs m B [CB 80 (p ++ jb)]
      /\ rw_cells rsegs m D [CB n (dl w ++ Z_to_bv 8 0 :: jd)]
      /\ (1 <= n)%nat.

  Lemma dl_nil : dl [] = [].
  Proof. unfold dl. apply firstn_nil. Qed.

  Lemma dl_length : forall w, (length (dl w) <= n - 1)%nat.
  Proof. intros. unfold dl. rewrite firstn_length. lia. Qed.

  Lemma dl_app : forall w q, dl (w ++ q) = dl w ++ firstn (n - 1 - length (dl w)) q.
  Proof.
    intros. unfold dl. rewrite firstn_app. rewrite firstn_length. f_equal. f_equal.
    destruct (Nat.le_ge_cases (length w) (n - 1)); [rewrite Nat.min_r by lia | rewrite Nat.min_l by lia]; lia.
  Qed.

  Lemma sink_plen : forall m mode w p, sink m mode w p -> (length p <= 80)%nat.
  Proof.
    (intros m mode w p; (first [ intro dR_5; dex2 dR_5 as jb jd; dand4 dR_5 as _ _ HB _ | intro dR_5; dand6 dR_5 as jb jd _ _ HB _ | intros (jb & jd & _ & _ & HB & _) ])). pose proof (rw_CB_length _ _ _ _ _ HB) as L.
    rewrite length_app in L. lia.
  Qed.
End Sink.

(* [comment removed for export] *)
Definition fwx (written pending bs : list byte) : list byte * list byte :=
  if (Z.of_nat (length bs) <=? 80 - Z.of_nat (length pending))%Z
  then (written, pending ++ bs)
  else (written ++ pending ++ bs, []).

Lemma fwx_fits : forall w p bs, (Z.of_nat (length bs) <= 80 - Z.of_nat (length p))%Z -> fwx w p bs = (w, p ++ bs).
Proof. intros. unfold fwx. replace (_ <=? _)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma fwx_spills : forall w p bs, (80 - Z.of_nat (length p) < Z.of_nat (length bs))%Z -> fwx w p bs = (w ++ p ++ bs, []).
Proof. intros. unfold fwx. replace (_ <=? _)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma fwx_total : forall w p bs, fst (fwx w p bs) ++ snd (fwx w p bs) = w ++ p ++ bs.
Proof. intros. unfold fwx. destruct (_ <=? _)%Z; cbn; rewrite ?app_assoc, ?app_nil_r; reflexivity. Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N); (bv_unsigned sp - 2240, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at rsegs m' Src src.
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^32)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
  asan_memcpy_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 2240 <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (Dst + N <= lo \/ bv_unsigned sp <= Dst)%Z -> (Src + N <= lo \/ bv_unsigned sp <= Src)%Z ->
  (N = 0%Z \/ (range_ok m Src N /\ range_ok m Dst N)) ->
  evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x574f8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros BA LEN DC SEP HN HS HD MI CE ST LOLE CEIL SPD SPS RNG.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memcpy_icpt_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN;
      [exact BA | exact LEN | exact DC | exact SEP | exact MI | exact CE | exact ST | unfold MEMCPY_ICPT_STACK; lia | exact CEIL
      | exact SPD | exact SPS | lia | exact RNG]. }
  intros ms' P. unfold memcpy_icpt_post, memcpy_postv, MEMCPY_ICPT_STACK in *. rewrite ED, ES, EN in P. exact P.
Qed.

Definition memset_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst C N : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N); (bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) (repeat (Z_to_bv 8 C) (Z.to_nat N))].
Lemma memset_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst C N : Z) (junk : list byte) (lo : Z),
  rw_cells rsegs m Dst [CB (Z.to_nat N) junk] -> (0 <= N < 2^32)%Z -> (0 <= C < 256)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
  asan_memset_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 2224 <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (Dst + N <= lo \/ bv_unsigned sp <= Dst)%Z ->
  (N = 0%Z \/ range_ok m Dst N) ->
  evt rsegs (memset_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst C N lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x574f4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DC HN HC HD MI CE ST LOLE CEIL SPD RNG.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memset_icpt_spec with (junk := junk); rewrite ?ED, ?EN;
      [exact DC | exact MI | exact CE | exact ST | unfold MEMSET_ICPT_STACK; lia | exact CEIL | exact SPD | lia | exact RNG]. }
  intros ms' P. unfold memset_icpt_post, memset_postv, MEMSET_ICPT_STACK in *. rewrite ED, EC, EN in P.
  rewrite Z.mod_small in P by lia. exact P.
Qed.

Lemma lowP_asan_memcpy_cells : lowP asan_memcpy_cells.
Proof.
  unfold asan_memcpy_cells. repeat (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]).
  first [apply lowP_map_cells | apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia].
Qed.
Lemma lowP_asan_memset_cells : lowP asan_memset_cells.
Proof.
  unfold asan_memset_cells. repeat (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]).
  first [apply lowP_map_cells | apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia].
Qed.
Lemma lowP_strnlen_icpt_cells : lowP strnlen_icpt_cells.
Proof.
  unfold strnlen_icpt_cells, asan_inited_cell. repeat (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]).
  first [apply lowP_map_cells | apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia].
Qed.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at rsegs m VA (u64s slots).

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma va_read8 : forall m VA slots (i : Z) w a,
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  (first [ pose proof ((u64s_split _ _ _ Hn)) as dR_1; dex2 dR_1 as pre post; dand4 dR_1 as E Hlen Eu Hlu | pose proof ((u64s_split _ _ _ Hn)) as dR_1; dand6 dR_1 as pre post E Hlen Eu Hlu | destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu) ]).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma va_read4 : forall m VA slots (i : Z) w a,
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes rsegs m a 4 = Some (le4 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  (first [ pose proof ((u64s_split _ _ _ Hn)) as dR_2; dex2 dR_2 as pre post; dand4 dR_2 as E Hlen Eu Hlu | pose proof ((u64s_split _ _ _ Hn)) as dR_2; dand6 dR_2 as pre post E Hlen Eu Hlu | destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu) ]).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le4_z64 : le4 z64 = [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. unfold le4, z64. rewrite unsigned_lit by lia. cbn. reflexivity. Qed.
Lemma snfile_flags_read : forall m Fp wend wpos wbase buf bsz mode CK,
  rw_cells rsegs m Fp (snfile z64 wend wpos wbase buf bsz mode CK) ->
  ov_read_bytes rsegs m (wa (Fp + 0)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros. pose proof (bytes_at_read rsegs _ Fp _ 0 1 (bytes_at_of_rw_cells _ _ _ _ H) ltac:(lia) ltac:(cbn; lia)) as R.
  unfold snfile in R. cbn [cells_bytes cbytes Z.to_nat skipn] in R. rewrite le4_z64 in R. cbn [firstn app] in R. exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RO_TOP : Z := 0x35000.   (* [comment removed for export] *)
Definition PC1_DEPTH : Z := 544.    (* [comment removed for export] *)
Definition PC2_DEPTH : Z := 4928.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pc1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Definition pass1_stmt (FMT : list cell) (la : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A AP NLA NLT : Z) (canary : word),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 AP -> a3 = Z_to_bv 64 NLA -> a4 = Z_to_bv 64 NLT ->
  stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary -> mem_inv rsegs m ->
  (lo <= bv_unsigned sp - PC1_DEPTH)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  (0 <= AP < 2^64)%Z -> (0 <= NLA < 2^64)%Z -> (0 <= NLT < 2^64)%Z ->
  (A + la <= GLOBALS_TOP)%Z -> (GLOBALS_TOP <= lo)%Z ->
  evt rsegs (pc1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition hs_shadow (m : word -> option byte) (HS : Z) (hs : list byte) : Prop :=
  hs = [] \/ exists L, (1 <= L)%Z /\ range_ok m HS L /\ (forall P, 0 <= P -> memchr_len 0 P hs <= L)%Z.

Lemma lowP_hs_shadow : forall HS hs, lowP (fun m => hs_shadow m HS hs).
Proof.
  intros HS hs W m m' MU HW [H | (L & L1 & R & HL)]; [left; exact H| right]. exists L. split; [exact L1|]. split; [|exact HL].
  exact (lowP_range_ok HS L ltac:(lia) W m m' MU HW R).
Qed.

Lemma hs_shadow_strnlen : forall m HS hs P,
  hs_shadow m HS hs -> memchr_ok HS 0 P hs -> (0 <= P)%Z ->
  memchr_len 0 P hs = 0%Z \/ range_ok m HS (memchr_len 0 P hs).
Proof.
  intros m HS hs P HSH OK P0. pose proof (memchr_len_bound 0 P hs P0) as B.
  destruct (Z.eq_dec (memchr_len 0 P hs) 0) as [E|NE]; [left; exact E| right].
  destruct HSH as [-> | (L & L1 & R & HL)].
  - exfalso. unfold memchr_len, memchr_ok in *. rewrite firstn_nil in *. cbn in *. lia.
  - eapply range_ok_prefix; [exact R|]. specialize (HL P P0). lia.
Qed.

Lemma strnlen_le_memchr_len : forall P hs, (0 <= P)%Z -> (strnlen_res P hs <= memchr_len 0 P hs)%Z.
Proof.
  intros P hs HP. unfold strnlen_res, memchr_len. destruct (find_byte 0 (firstn (Z.to_nat P) hs)); lia.
Qed.
Lemma hs_shadow_out : forall m HS hs P,
  hs_shadow m HS hs -> memchr_ok HS 0 P hs -> (0 <= P)%Z ->
  strnlen_res P hs = 0%Z \/ range_ok m HS (strnlen_res P hs).
Proof.
  intros m HS hs P HSH OK P0. pose proof (strnlen_le_memchr_len P hs P0) as LE.
  destruct (Z.eq_dec (strnlen_res P hs) 0) as [E|NE]; [left; exact E| right].
  assert (SP : (0 <= strnlen_res P hs)%Z).
  { unfold strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat P) hs)); lia. }
  destruct (hs_shadow_strnlen m HS hs P HSH OK P0) as [Z0 | R]; [exfalso; lia|].
  eapply range_ok_prefix; [exact R| lia].
Qed.

(* [comment removed for export] *)
Definition sf2 (A la D : Z) (n : nat) (HS : Z) (hs : list byte) (SB : Z) (K : nat) (zlo zhi : Z)
    (m : word -> option byte) : Prop :=
     asan_memcpy_cells m /\ strnlen_icpt_cells m
  /\ range_ok m A la /\ range_ok m D (Z.of_nat n) /\ hs_shadow m HS hs
  /\ bytes_at rsegs m SB (zeros K) /\ zsh_bounds SB K zlo zhi
  /\ (2147446784 <= SB)%Z.   (* [comment removed for export] *)

Lemma lowP_sf2 : forall A la D n HS hs SB K zlo zhi, (0 <= la)%Z ->
  lowP (sf2 A la D n HS hs SB K zlo zhi).
Proof.
  (intros A la D n HS hs SB K zlo zhi Hla W m m' MU HW; (first [ intro dR_6; dand8 dR_6 as C1 C2 R1 R2 H5 ZS ZB SBL | intros (C1 & C2 & R1 & R2 & H5 & ZS & ZB & SBL) ])). (first [ pose proof (ZB) as dR_3; dand4 dR_3 as B1 B2 B3 _ | pose proof ZB as (B1 & B2 & B3 & _) ]).
  split; [exact (lowP_asan_memcpy_cells W m m' MU HW C1)|]. split; [exact (lowP_strnlen_icpt_cells W m m' MU HW C2)|].
  split; [exact (lowP_range_ok A la Hla W m m' MU HW R1)|].
  split; [exact (lowP_range_ok D (Z.of_nat n) ltac:(lia) W m m' MU HW R2)|].
  split; [exact (lowP_hs_shadow _ _ W m m' MU HW H5)|]. split; [|exact (conj ZB SBL)].
  eapply bytes_at_transport; [exact ZS| exact MU| apply low_disjoint; [exact HW|]].
  rewrite zeros_length. unfold in_zone, kHighShadowEnd_z, kHighMemBeg_z in *. lia.
Qed.

Lemma sf2_RA : forall A la D n HS hs SB K zlo zhi m, sf2 A la D n HS hs SB K zlo zhi m -> range_ok m A la.
Proof. intros until m. ((first [ intro dR_7; dand4 dR_7 as _ _ R _ | intros (_ & _ & R & _) ])). exact R. Qed.
Lemma sf2_RD : forall A la D n HS hs SB K zlo zhi m, sf2 A la D n HS hs SB K zlo zhi m -> range_ok m D (Z.of_nat n).
Proof. intros until m. ((first [ intro dR_8; dand5 dR_8 as _ _ _ R _ | intros (_ & _ & _ & R & _) ])). exact R. Qed.
Lemma sf2_HS : forall A la D n HS hs SB K zlo zhi m, sf2 A la D n HS hs SB K zlo zhi m -> hs_shadow m HS hs.
Proof. intros until m. ((first [ intro dR_9; dand6 dR_9 as _ _ _ _ R _ | intros (_ & _ & _ & _ & R & _) ])). exact R. Qed.
Lemma sf2_SC : forall A la D n HS hs SB K zlo zhi m, sf2 A la D n HS hs SB K zlo zhi m -> strnlen_icpt_cells m.
Proof. intros until m. ((first [ intro dR_10; dand3 dR_10 as _ R _ | intros (_ & R & _) ])). exact R. Qed.
Lemma sf2_ZS : forall A la D n HS hs SB K zlo zhi m, sf2 A la D n HS hs SB K zlo zhi m -> bytes_at rsegs m SB (zeros K).
Proof. intros until m. ((first [ intro dR_11; dand7 dR_11 as _ _ _ _ _ R _ | intros (_ & _ & _ & _ & _ & R & _) ])). exact R. Qed.
Lemma sf2_ZB : forall A la D n HS hs SB K zlo zhi m, sf2 A la D n HS hs SB K zlo zhi m -> zsh_bounds SB K zlo zhi.
Proof. intros until m. ((first [ intro dR_12; dand8 dR_12 as _ _ _ _ _ _ R _ | intros (_ & _ & _ & _ & _ & _ & R & _) ])). exact R. Qed.
(* [comment removed for export] *)
Lemma sf2_stack_range : forall A la D n HS hs SB K zlo zhi m a k,
  sf2 A la D n HS hs SB K zlo zhi m -> (zlo <= a)%Z -> (a + k <= zhi)%Z -> (1 <= k)%Z -> range_ok m a k.
Proof. intros until k. intros SF H1 H2 H3. eapply range_ok_of_zeros; [eapply sf2_ZS; exact SF| eapply sf2_ZB; exact SF| lia| lia| lia]. Qed.
Lemma sf2_fmt_range : forall A la D n HS hs SB K zlo zhi m a k,
  sf2 A la D n HS hs SB K zlo zhi m -> (A <= a)%Z -> (a + k <= A + la)%Z -> (1 <= k)%Z -> range_ok m a k.
Proof. intros until k. intros SF H1 H2 H3. eapply range_ok_sub; [eapply sf2_RA; exact SF| lia| lia| lia]. Qed.

(* [comment removed for export] *)
Definition pc2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte)
    (nargs : Z) (o : list byte) (canary : word)
    (A la : Z) (SB : Z) (K : nat)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (w' p' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 4928, bv_unsigned sp + 8); (B, B + 80); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ sink Fp B D n m' mode w' p' /\ w' ++ p' = o
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * nargs))]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary
    /\ sf2 A la D n HS hs SB K (bv_unsigned sp - 544) (bv_unsigned sp + 96) m'.

Definition pass2_stmt (FMT : list cell) (la : Z) (nargs : Z)
    (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word)
    (SB : Z) (K : nat),
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
  (* [comment removed for export] *)
  stk rsegs m lo q -> ro_cells rsegs m A FMT -> ssp_cells m canary -> sink Fp B D n m mode [] [] ->
  rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs ->
  mem_inv rsegs m ->
  sf2 A la D n HS hs SB K (q - 544) (q + 96) m ->
  (* [comment removed for export] *)
  Fp = (q + 416)%Z -> B = (q + 16)%Z ->      (* [comment removed for export] *)
  (lo <= q - PC2_DEPTH)%Z -> (alloc_ceiling <= lo)%Z -> (q + 672 <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->   (* [comment removed for export] *)
  (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z -> dst_zone D (Z.of_nat n) -> (Z.of_nat n <= 2^31)%Z ->   (* [comment removed for export] *)
  (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
  evt rsegs (pc2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fp B D n mode VA slots HS hs nargs (OUT slots hs) canary A la SB K m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).

End CEIL2.

(* [comment removed for export] *)
Ltac unpack_sink H FL CKC BUF DST :=
  let jb := fresh "jb" in let jd := fresh "jd" in let N1 := fresh "N1" in
  (first [ dex2 H as jb jd; dand5 H as FL CKC BUF DST N1 | dand7 H as jb jd FL CKC BUF DST N1 | destruct H as (jb & jd & FL & CKC & BUF & DST & N1) ]).
Ltac pack_sink :=
  lazymatch goal with |- sink _ _ _ _ _ _ _ _ =>
    eexists _, _; refine (conj _ (conj _ (conj _ (conj _ _))));
    [ eassumption | eassumption | eassumption | eassumption | assumption ]
  end.
Ltac clear_rdf := repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => clear H end.
Ltac rdf := clear_rdf;
  match goal with FL : rw_cells _ _ _ (snfile _ _ _ _ _ _ _ _) |- _ =>
    let R := fresh "RDF" in pose proof (snfile_flags_read _ _ _ _ _ _ _ _ _ FL) as R end.
Ltac name_junk FR :=
  repeat match type of FR with context [CB ?n (skipn ?a ?b)] => let j := fresh "jk" in set (j := skipn a b) in FR; clearbody j end;
  repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
