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
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU.

Module RU_sszg.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU RU_mkfg RU_mz6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Definition SN_WRITE : Z := 0x2ae18.
Definition GOT_SSP : Z := 0x307c8.       (* [comment removed for export] *)
Definition SSP_GUARD : Z := 0x62768.     (* [comment removed for export] *)
Definition VSNPRINTF : Z := 0x2ad4c.
Definition VFPRINTF : Z := 0x263d0.
Definition PRINTF_CORE : Z := 0x26580.
Definition FWRITEX : Z := 0x25c44.
Definition TOWRITE : Z := 0x25e34.
Definition POP_ARG : Z := 0x273b0.

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x70000.
(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x64000.
Definition dst_ok (D : Z) (n : nat) : Prop := (0 <= D)%Z /\ ~ (D < IMG_HI /\ IMG_LO < D + Z.of_nat n)%Z.

(* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells rsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] /\ rw_cells rsegs m SSP_GUARD [C8 canary].

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
    (intros m mode w p; (first [ intro dR_4; dex2 dR_4 as jb jd; dand4 dR_4 as _ _ HB _ | intro dR_4; dand6 dR_4 as jb jd _ _ HB _ | intros (jb & jd & _ & _ & HB & _) ])). pose proof (rw_CB_length _ _ _ _ _ HB) as L.
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
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at rsegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
  bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
  evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2aff4) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.

Definition memset_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) (repeat (Z_to_bv 8 C) (Z.to_nat N))].
Lemma memset_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst C N : Z) (junk : list byte),
  rw_cells rsegs m Dst [CB (Z.to_nat N) junk] -> (0 <= N < 2^64)%Z -> (0 <= C < 256)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
  evt rsegs (memset_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst C N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b3f8) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DC HN HC HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memset_spec with (junk := junk); rewrite ?ED, ?EN; [exact DC | exact MI]. }
  intros ms' P. unfold memset_post, memset_postv in *. rewrite ED, EC, EN in P. rewrite Z.mod_small in P by lia. exact P.
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
Definition RO_TOP : Z := 0x17000.   (* [comment removed for export] *)
Definition PC1_DEPTH : Z := 544.    (* [comment removed for export] *)
Definition PC2_DEPTH : Z := 608.    (* [comment removed for export] *)

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
Definition pc2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte)
    (nargs : Z) (o : list byte) (canary : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (w' p' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 608, bv_unsigned sp + 8); (B, B + 80); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ sink Fp B D n m' mode w' p' /\ w' ++ p' = o
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * nargs))]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary.

Definition pass2_stmt (FMT : list cell) (la : Z) (nargs : Z)
    (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word),
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
  (* [comment removed for export] *)
  stk rsegs m lo q -> ro_cells rsegs m A FMT -> ssp_cells m canary -> sink Fp B D n m mode [] [] ->
  rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs ->
  mem_inv rsegs m ->
  (* [comment removed for export] *)
  Fp = (q + 368)%Z -> B = (q + 16)%Z ->
  (lo <= q - PC2_DEPTH)%Z -> (GLOBALS_TOP <= lo)%Z -> (q + 672 <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
  (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z ->
  (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
  evt rsegs (pc2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fp B D n mode VA slots HS hs nargs (OUT slots hs) canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).

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
End RU_sszg.


Module RU_sk2l.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU RU_mkfg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_mkfg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_sszg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@DB2]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp wend bufp bufsize : Z) (mode : word) (CK S0 N B Sr l lo : Z) (dn : nat) (p bs jd : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    let k := Z.of_nat (length (firstn (Z.to_nat N) (p ++ bs))) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (S0, S0 + Z.of_nat dn)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Fp (snfile z64 wend bufp bufp bufp bufsize mode CK)
    /\ rw_cells rsegs m' CK [C8 (Z_to_bv 64 (S0 + k)); C8 (Z_to_bv 64 (N - k))]
    /\ rw_cells rsegs m' S0 [CB dn (firstn (Z.to_nat N) (p ++ bs) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat k)) jd)]
    /\ bytes_at rsegs m' B p /\ bytes_at rsegs m' Sr bs.

Section SnWrite.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : word -> option byte)
            (Fp wend bufp bufsize : Z) (mode : word) (CK S0 N B Sr l lo : Z) (dn : nat) (p bs jd : list byte).
  Hypothesis LEN : length bs = Z.to_nat l.
  Hypothesis N0 : (0 <= N)%Z.
  Hypothesis ND : (N + 1 <= Z.of_nat dn)%Z.
  Hypothesis Hl : (0 <= l < 2^63)%Z.
  Hypothesis HB : (B + Z.of_nat (length p) < 2^63)%Z.
  Hypothesis Hbuf : (0 <= bufp < 2^64)%Z.
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 64)%Z.
  (* [comment removed for export] *)
  Hypothesis L1 : (S0 + Z.of_nat dn <= lo)%Z.
  Hypothesis L2 : (bv_unsigned sp <= B)%Z.
  Hypothesis L3 : (B + 80 <= Fp)%Z.
  Hypothesis L4 : (CK = Fp + 232)%Z.
  Hypothesis L5 : (Sr + l <= B)%Z.
  Hypothesis L6 : (~ (lo < Sr + l /\ Sr < bv_unsigned sp))%Z.
  Hypothesis L7 : (~ (S0 < Sr + l /\ Sr < S0 + Z.of_nat dn))%Z.   (* [comment removed for export] *)
  Hypothesis LP : (Z.of_nat (length p) <= 80)%Z.
  Hypothesis DB : (0 <= S0 /\ S0 + Z.of_nat dn <= 2^64)%Z.
  Hypothesis CB_ : (0 <= CK /\ CK + 16 <= 2^64)%Z.
  Hypothesis FB : (0 <= Fp /\ Fp + 232 <= 2^64)%Z.
  Hypothesis BB : (0 <= B /\ B + Z.of_nat (length p) <= 2^64)%Z.
  Hypothesis SB : (0 <= Sr /\ Sr + Z.of_nat (length bs) <= 2^64)%Z.
  Hypothesis SPR : (0 <= bv_unsigned sp < 2^64)%Z.
  Hypothesis LJ : length jd = dn.

  Notation W := [(bv_unsigned sp - 64, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (S0, S0 + Z.of_nat dn)]%Z.
  Notation POST := (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp wend bufp bufsize mode CK S0 N B Sr l lo dn p bs jd m).
  Notation FRAME mm j8 := (rw_cells rsegs mm (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FILE mm wp wb := (rw_cells rsegs mm Fp (snfile z64 wend wp wb bufp bufsize mode CK)).
  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 l) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 Sr) x19 x20 (Z_to_bv 64 CK) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  (* [comment removed for export] *)
  #[using="LJ FB DB LP L7 L5 L4 L3 L2 L1 LO HB Hl ND N0 LEN"] Lemma sn_from_6e0 : forall mm j8 (k : Z) (dlv : list byte) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
    dlv = firstn (Z.to_nat N) (p ++ bs) -> k = Z.of_nat (length dlv) ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 (S0 + k)); C8 (Z_to_bv 64 (N - k))] ->
    rw_cells rsegs mm S0 [CB dn (dlv ++ skipn (Z.to_nat k) jd)] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs ->
    evt rsegs POST (ST 0x2aebc mm x1 x5 x6 x7 (Z_to_bv 64 (S0 + k)) x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hdlv Hk MI MU WM ST FR FL CKC DST BP BS.
    assert (KN : (0 <= k <= N)%Z). { subst k dlv. rewrite firstn_length. lia. }
    unfold snfile, z64, m1w in FL.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD. clear DST.
    pose proof (u8arr_store_ok rsegs _ _ _ k (Z_to_bv 64 (S0 + k)) DA ltac:(rewrite LD; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs. change (write_to_mem mm (Z_to_bv 64 (S0 + k)) [Z_to_bv 8 0]) with (write_to_mem mm (wa (S0 + k)) [Z_to_bv 8 0]).
    pose proof (u8arr_write rsegs _ _ _ k (Z_to_bv 8 0) DA ltac:(rewrite LD; lia)) as DA2. clear DA.
    store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LD in DST. clear DA2.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end). cbv zeta.
    rewrite <- Hdlv, <- Hk.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { unfold snfile, z64, m1w. assumption. }
    split. { exact CKC. }
    split. { rewrite upd_after_prefix in DST; [exact DST | lia | ].
             rewrite length_app, length_skipn in LD. lia. }
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ FB CB_ DB LP L7 L5 L4 L3 L2 L1 LO HB Hl ND N0 LEN"] Lemma sn_from_6c8 : forall mm j8 (k1 k2 : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    k1 = Z.min N (Z.of_nat (length p)) -> k2 = Z.min (N - k1) l -> (0 < k2)%Z ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 (S0 + k1)); C8 (Z_to_bv 64 (N - k1))] ->
    rw_cells rsegs mm S0 [CB dn (firstn (Z.to_nat k1) p ++ firstn (Z.to_nat k2) bs ++ skipn (Z.to_nat k1 + Z.to_nat k2) jd)] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs ->
    evt rsegs POST (ST 0x2aea4 mm x1 x5 x6 x7 (Z_to_bv 64 (S0 + k1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 k2) (Z_to_bv 64 k1) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk1 Hk2 K2 MI MU WM ST FR FL CKC DST BP BS.
    pose proof (Z.le_min_l N (Z.of_nat (length p))). pose proof (Z.le_min_r N (Z.of_nat (length p))).
    pose proof (Z.le_min_l (N - k1) l). pose proof (Z.le_min_r (N - k1) l).
    assert (K1 : (0 <= k1)%Z) by (subst k1; apply Z.min_glb; lia).
    unfold snfile, z64, m1w in FL.
    zs. zs. zs. zs. zs. zs.
    replace (S0 + k1 + k2)%Z with (S0 + (k1 + k2))%Z by lia. replace (N - k1 - k2)%Z with (N - (k1 + k2))%Z by lia.
    eapply sn_from_6e0 with (dlv := firstn (Z.to_nat k1) p ++ firstn (Z.to_nat k2) bs); try eassumption.
    - (* [comment removed for export] *)
      destruct (Z.le_ge_cases (Z.of_nat (length p)) N) as [Hle|Hge].
      + assert (E1 : k1 = Z.of_nat (length p)) by lia. rewrite E1, Nat2Z.id, firstn_all.
        rewrite firstn_app. rewrite (firstn_all2 p) by lia. f_equal.
        assert (E2 : k2 = Z.min (N - Z.of_nat (length p)) (Z.of_nat (length bs))) by lia.
        destruct (Z.le_ge_cases (N - Z.of_nat (length p)) (Z.of_nat (length bs))).
        * f_equal. lia.
        * rewrite !firstn_all2 by lia. reflexivity.
      + assert (E1 : k1 = N) by lia. assert (k2 = 0%Z) by lia. lia.
    - rewrite length_app, !firstn_length, LEN. lia.
    - replace (S0 + (k1 + k2))%Z with (S0 + k1 + k2)%Z by lia. replace (N - (k1 + k2))%Z with (N - k1 - k2)%Z by lia. assumption.
    - replace (Z.to_nat (k1 + k2)) with (Z.to_nat k1 + Z.to_nat k2)%nat by lia. rewrite <- app_assoc. exact DST.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ SB FB CB_ DB LP L7 L5 L4 L3 L2 L1 LO HB Hl ND N0 LEN"] Lemma sn_from_6b0 : forall mm j8 (k1 : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    k1 = Z.min N (Z.of_nat (length p)) ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 (S0 + k1)); C8 (Z_to_bv 64 (N - k1))] ->
    rw_cells rsegs mm S0 [CB dn (firstn (Z.to_nat k1) p ++ skipn (Z.to_nat k1) jd)] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs ->
    evt rsegs POST (ST 0x2ae8c mm x1 x5 x6 x7 (Z_to_bv 64 (S0 + k1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (N - k1)) (Z_to_bv 64 k1) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk1 MI MU WM ST FR FL CKC DST BP BS.
    pose proof (Z.le_min_l N (Z.of_nat (length p))). pose proof (Z.le_min_r N (Z.of_nat (length p))).
    assert (K1 : (0 <= k1)%Z) by (subst k1; apply Z.min_glb; lia).
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
    zs. brf K1'.
    - (* [comment removed for export] *)
      zs. brf K2.
      + (* [comment removed for export] *)
        replace (S0 + k1)%Z with (S0 + (k1 + 0))%Z by lia. 
        eapply sn_from_6e0 with (dlv := firstn (Z.to_nat k1) p); try eassumption.
        * assert (E1 : k1 = N) by lia. rewrite E1. rewrite firstn_app_le by lia. reflexivity.
        * rewrite firstn_length. lia.
        * replace (S0 + (k1 + 0))%Z with (S0 + k1)%Z by lia. replace (N - (k1 + 0))%Z with (N - k1)%Z by lia. exact CKC.
        * replace (Z.to_nat (k1 + 0)) with (Z.to_nat k1) by lia. exact DST.
      + (* [comment removed for export] *)
        destruct (rw_cells_CB_split3 rsegs _ _ _ _ (Z.to_nat k1) (Z.to_nat (N - k1)) DST ltac:(lia)) as (DA & DB2 & DC). clear DST.
        rewrite firstn_app_le, firstn_firstn, Nat.min_id in DA by (rewrite firstn_length; lia).
        zs. zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          eapply evt_cut; [ eapply memcpy_callv with (src := firstn (Z.to_nat (N - k1)) bs) | post_call_lit rsegs mq ] end.
        { eapply bytes_at_prefix. rewrite firstn_skipn. exact BS. }
        { rewrite firstn_length, LEN. lia. }
        { eapply rwc_eq; [exact DB2 | lia]. }
        { lia. } { lia. } { lia. } { lia. } { exact MI. }
        match goal with Hb : rw_cells _ ?mq (S0 + k1)%Z _, MIq : mem_inv _ ?mq |- _ =>
          pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ DA ltac:(eapply rwc_eq; [exact Hb| lia]) DC) as DST; clear DA Hb DC;
          rename MIq into MI2 end.
        replace (Z.to_nat k1 + Z.to_nat (N - k1) + (dn - Z.to_nat k1 - Z.to_nat (N - k1)))%nat with dn in DST by lia.
        eapply (sn_from_6c8 _ _ k1 (N - k1)); try eassumption; try lia.
        rewrite skipn_app_exact in DST by (rewrite firstn_length; lia). exact DST.
      - (* [comment removed for export] *)
        zs. zs. brf K2.
        + (* [comment removed for export] *)
          replace (S0 + k1)%Z with (S0 + (k1 + 0))%Z by lia.
          eapply sn_from_6e0 with (dlv := firstn (Z.to_nat k1) p); try eassumption.
          * assert (E1 : bs = []) by (destruct bs; [reflexivity| cbn in LEN; lia]). rewrite E1, app_nil_r.
            destruct (Z.le_ge_cases (Z.of_nat (length p)) N).
            -- assert (E2 : k1 = Z.of_nat (length p)) by lia. rewrite E2, Nat2Z.id, firstn_all, firstn_all2 by lia. reflexivity.
            -- f_equal. lia.
          * rewrite firstn_length. lia.
          * replace (S0 + (k1 + 0))%Z with (S0 + k1)%Z by lia. replace (N - (k1 + 0))%Z with (N - k1)%Z by lia. exact CKC.
          * replace (Z.to_nat (k1 + 0)) with (Z.to_nat k1) by lia. exact DST.
        + destruct (rw_cells_CB_split3 rsegs _ _ _ _ (Z.to_nat k1) (Z.to_nat l) DST ltac:(lia)) as (DA & DB2 & DC). clear DST.
          rewrite firstn_app_le, firstn_firstn, Nat.min_id in DA by (rewrite firstn_length; lia).
          zs. zs. zs.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
            eapply evt_cut; [ eapply memcpy_callv with (src := bs) | post_call_lit rsegs mq ] end.
          { exact BS. }
          { exact LEN. }
          { eapply rwc_eq; [exact DB2 | lia]. }
          { lia. } { lia. } { lia. } { lia. } { exact MI. }
          match goal with Hb : rw_cells _ ?mq (S0 + k1)%Z _, MIq : mem_inv _ ?mq |- _ =>
            pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ DA ltac:(eapply rwc_eq; [exact Hb| lia]) DC) as DST; clear DA Hb DC;
            rename MIq into MI2 end.
          replace (Z.to_nat k1 + Z.to_nat l + (dn - Z.to_nat k1 - Z.to_nat l))%nat with dn in DST by lia.
          eapply (sn_from_6c8 _ _ k1 l); try eassumption; try lia.
          rewrite skipn_app_exact in DST by (rewrite firstn_length; lia).
          rewrite <- LEN, firstn_all. rewrite LEN. exact DST.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ SB BB FB CB_ DB LP L7 L5 L4 L3 L2 L1 LO HB Hl ND N0 LEN"] Lemma sn_from_688 : forall mm j8 (k1 : Z) x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    k1 = Z.min N (Z.of_nat (length p)) ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 N)] ->
    rw_cells rsegs mm S0 [CB dn jd] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs ->
    evt rsegs POST (ST 0x2ae64 mm ra x5 x6 x7 x10 (Z_to_bv 64 B) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 k1) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk1 MI MU WM ST FR FL CKC DST BP BS.
    pose proof (Z.le_min_l N (Z.of_nat (length p))). pose proof (Z.le_min_r N (Z.of_nat (length p))).
    assert (K1 : (0 <= k1)%Z) by (subst k1; apply Z.min_glb; lia).
    zs. zs. brf K0.
    - (* [comment removed for export] *)
      rewrite K0. replace (Z_to_bv 64 S0) with (Z_to_bv 64 (S0 + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 N) with (Z_to_bv 64 (N - 0)) by (f_equal; lia).
      eapply (sn_from_6b0 _ _ 0%Z); try eassumption; try lia.
      rewrite Z.add_0_r, Z.sub_0_r. exact CKC.
    - destruct (rw_cells_CB_split3 rsegs _ _ _ _ 0%nat (Z.to_nat k1) DST ltac:(lia)) as (DA & DB2 & DC). clear DST.
      cbn [firstn skipn] in DB2. rewrite Z.add_0_r in DB2.
      zs. zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        eapply evt_cut; [ eapply memcpy_callv with (src := firstn (Z.to_nat k1) p) | post_call_lit rsegs mq ] end.
      { eapply bytes_at_prefix. rewrite firstn_skipn. exact BP. }
      { rewrite firstn_length. lia. }
      { exact DB2. }
      { lia. } { lia. } { lia. } { lia. } { exact MI. }
      unfold snfile, z64, m1w in FL.
      zs. zs. zs. zs. zs. zs.
      match goal with Hb : rw_cells _ ?mq S0 [CB (Z.to_nat k1) _], MIq : mem_inv _ ?mq |- _ =>
        pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ DA ltac:(eapply rwc_eq; [exact Hb| cbn; lia]) ltac:(eapply rwc_eq; [exact DC | cbn; lia])) as DST; clear DA Hb DC;
        rename MIq into MI2 end.
      cbn [firstn app Nat.add] in DST. rewrite Nat.sub_0_r in DST.
      replace (Z.to_nat k1 + (dn - Z.to_nat k1))%nat with dn in DST by lia.
      eapply (sn_from_6b0 _ _ k1); try eassumption; try lia.
  Qed.

  #[using="LJ SPR SB BB FB CB_ DB LP L7 L6 L5 L4 L3 L2 L1 LO HB Hl ND N0 LEN"] Lemma sn_write_body : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m Fp (snfile z64 wend (B + Z.of_nat (length p)) B bufp bufsize mode CK) ->
    rw_cells rsegs m CK [C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 N)] ->
    rw_cells rsegs m S0 [CB dn jd] ->
    bytes_at rsegs m B p -> bytes_at rsegs m Sr bs -> mem_inv rsegs m ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 Sr) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2ae18) fc None m (seg_rom rsegs)).
  Proof.
    intros until t6. intros ST FL CKC DST BP BS MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold snfile, z64, m1w in FL.
    carve_frame 64%nat ST.
    do 15 zs.
    zs. replace (B + Z.of_nat (length p) - B)%Z with (Z.of_nat (length p)) by lia.
    zs. zs. brf K1.
    - eapply (sn_from_688 _ _ N); try eassumption; try lia.
    - zs. eapply (sn_from_688 _ _ (Z.of_nat (length p))); try eassumption; try lia.
  Qed.
End SnWrite.

Lemma sn_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Fp wend bufp bufsize : Z) (mode : word) (CK S0 N B Sr l lo : Z) (dn : nat) (p bs jd : list byte),
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 Sr -> a2 = Z_to_bv 64 l ->
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m Fp (snfile z64 wend (B + Z.of_nat (length p)) B bufp bufsize mode CK) ->
  rw_cells rsegs m CK [C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 N)] ->
  rw_cells rsegs m S0 [CB dn jd] ->
  bytes_at rsegs m B p -> bytes_at rsegs m Sr bs -> mem_inv rsegs m ->
  length bs = Z.to_nat l -> (0 <= N)%Z -> (N + 1 <= Z.of_nat dn)%Z -> (0 <= l < 2^63)%Z ->
  (Z.of_nat (length p) <= 80)%Z -> (0 <= bufp < 2^64)%Z ->
  (0 <= lo <= bv_unsigned sp - 64)%Z ->
  (S0 + Z.of_nat dn <= lo)%Z -> (bv_unsigned sp <= B)%Z -> (B + 80 <= Fp)%Z -> (CK = Fp + 232)%Z -> (Fp + 248 <= 2^64)%Z ->
  (Sr + l <= B)%Z -> (~ (lo < Sr + l /\ Sr < bv_unsigned sp))%Z -> (~ (S0 < Sr + l /\ Sr < S0 + Z.of_nat dn))%Z ->
  (Fp + 248 <= 2^63)%Z ->
  evt rsegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp wend bufp bufsize mode CK S0 N B Sr l lo dn p bs jd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2ae18) fc None m (seg_rom rsegs)).
Proof.
  intros until jd. intros -> -> -> ST FL CKC DST BP BS MI LEN N0 ND Hl LP Hbuf LO L1 L2 L3 L4 F64 L5 L6 L7 F63.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ FL) as FB. rewrite snfile_size in FB.
  pose proof (bytes_at_bound _ _ _ _ BP) as BB. pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LJ.
  eapply sn_write_body; try eassumption; try lia.
Qed.
End RU_sk2l.

Module RU_f8qh.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU RU_mkfg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_mkfg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_sszg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_sk2l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sn_layout (sp : word) (lo Fp B D : Z) (n : nat) (Sr l : Z) : Prop :=
  (0 <= lo <= bv_unsigned sp - 64)%Z /\ (D + Z.of_nat n <= lo)%Z /\ (bv_unsigned sp <= B)%Z /\ (B + 80 <= Fp)%Z
  /\ (Fp + 248 <= 2^63)%Z /\ (Sr + l <= B)%Z /\ (~ (lo < Sr + l /\ Sr < bv_unsigned sp))%Z
  /\ (~ (D < Sr + l /\ Sr < D + Z.of_nat n))%Z /\ (0 <= Sr)%Z /\ (0 <= D)%Z.

Definition sn_write_sink_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ sink Fp B D n m' mode (w ++ p ++ bs) []
    /\ bytes_at rsegs m' Sr bs.

Lemma sn_write_sink : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z),
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 Sr -> a2 = Z_to_bv 64 l ->
  stk rsegs m lo (bv_unsigned sp) ->
  sink Fp B D n m mode w p ->
  bytes_at rsegs m Sr bs -> length bs = Z.to_nat l -> (0 <= l < 2^63)%Z ->
  sn_layout sp lo Fp B D n Sr l ->
  mem_inv rsegs m ->
  evt rsegs (sn_write_sink_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B D n mode w p bs Sr l lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2ae18) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros Ha0 Ha1 Ha2 ST SNK BS LEN Hl LAY MI.
  (first [ dex2 SNK as jb jd; dand5 SNK as FL CKC BUF DST N1 | dand7 SNK as jb jd FL CKC BUF DST N1 | destruct SNK as (jb & jd & FL & CKC & BUF & DST & N1) ]).
  (first [ dand10 LAY as LO L1 L2 L3 F63 L5 L6 L7 SR0 D0 | destruct LAY as (LO & L1 & L2 & L3 & F63 & L5 & L6 & L7 & SR0 & D0) ]).
  pose proof (dl_length n w) as DLL.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LD. rewrite length_app in LD. cbn [length] in LD.
  pose proof (rw_CB_length _ _ _ _ _ BUF) as LB. rewrite length_app in LB.
  (* [comment removed for export] *)
  (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ (length (dl n w)) (n - length (dl n w)) DST ltac:(lia))) as dR_3; dand3 dR_3 as DA DB DC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ (length (dl n w)) (n - length (dl n w)) DST ltac:(lia)) as (DA & DB & DC) ]). clear DC.
  rewrite firstn_app_le, firstn_all in DA by lia.
  rewrite skipn_app, skipn_all, Nat.sub_diag in DB. cbn [skipn app] in DB.
  rewrite firstn_all2 in DB by (cbn; lia).
  eapply evt_mono.
  { eapply (sn_write_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              Fp (B + 80) B 80 mode (Fp + 232) (D + Z.of_nat (length (dl n w))) (Z.of_nat n - 1 - Z.of_nat (length (dl n w))) B Sr l lo
              (n - length (dl n w))%nat p bs (Z_to_bv 8 0 :: jd));
      try eassumption; try reflexivity; try lia.
    - eapply bytes_at_prefix. pose proof (bytes_at_of_rw_cells _ _ _ _ BUF) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
  cbv beta. intros ms' P. unfold sn_write_post in P. cbv zeta in P.
  (first [ dex15 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m'; dand10 P as -> MU WM MI' ST' FL' CKC' DST' BP' BS' | dand25 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MU WM MI' ST' FL' CKC' DST' BP' BS' | destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & FL' & CKC' & DST' & BP' & BS') ]).
  unfold sn_write_sink_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros. lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [|exact BS'].
  (* [comment removed for export] *)
  set (k := Z.of_nat (length (firstn (Z.to_nat (Z.of_nat n - 1 - Z.of_nat (length (dl n w)))) (p ++ bs)))) in *.
  assert (Hdl : dl n (w ++ p ++ bs) = dl n w ++ firstn (Z.to_nat (Z.of_nat n - 1 - Z.of_nat (length (dl n w)))) (p ++ bs)).
  { rewrite dl_app. f_equal. f_equal. lia. }
  assert (Hk : length (dl n (w ++ p ++ bs)) = (length (dl n w) + Z.to_nat k)%nat).
  { rewrite Hdl, length_app. subst k. rewrite Nat2Z.id. reflexivity. }
  pose proof (rw_cells_transport rsegs _ _ _ _ _ BUF MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; lia)) as BUF'.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ DA MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; lia)) as DA'.
  exists (p ++ jb), (skipn (Z.to_nat k) jd).
  split. { replace (B + Z.of_nat (@length byte []))%Z with B by (cbn; lia). exact FL'. }
  split. { rewrite Hk, Nat2Z.inj_add, Z2Nat.id by lia.
           replace (D + (Z.of_nat (length (dl n w)) + k))%Z with (D + Z.of_nat (length (dl n w)) + k)%Z by lia.
           replace (Z.of_nat n - 1 - (Z.of_nat (length (dl n w)) + k))%Z with (Z.of_nat n - 1 - Z.of_nat (length (dl n w)) - k)%Z by lia.
           exact CKC'. }
  split. { cbn [app]. exact BUF'. }
  split.
  { pose proof (rw_CB_length _ _ _ _ _ DST') as LD'.
    lazymatch type of DST' with rw_cells _ _ _ [CB _ ?l2] =>
    assert (J : rw_cells rsegs m' D ([] ++ [CB (length (dl n w)) (dl n w); CB (n - length (dl n w)) l2] ++ []));
    [ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact DA'|]; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact DST' |] end.
    apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite app_nil_r, Nat.add_0_r in J.
    replace (length (dl n w) + (n - length (dl n w)))%nat with n in J by lia.
    rewrite Hdl, <- app_assoc. cbn [app].
    change (skipn (S (Z.to_nat k)) (Z_to_bv 8 0 :: jd)) with (skipn (Z.to_nat k) jd) in J. exact J. }
  exact N1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n); (B, B + 80)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ sink Fp B D n m' mode (fst (fwx w p bs)) (snd (fwx w p bs))
    /\ bytes_at rsegs m' Sr bs.

Lemma fwritex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z),
  a0 = Z_to_bv 64 Sr -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  stk rsegs m lo (bv_unsigned sp) ->
  sink Fp B D n m mode w p ->
  bytes_at rsegs m Sr bs -> length bs = Z.to_nat l -> (0 <= l < 2^63)%Z ->
  sn_layout sp lo Fp B D n Sr l ->
  mem_inv rsegs m ->
  evt rsegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B D n mode w p bs Sr l lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x25c44) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros -> -> -> ST SNK BS LEN Hl LAY MI.
  (first [ dex2 SNK as jb jd; dand5 SNK as FL CKC BUF DST N1 | dand7 SNK as jb jd FL CKC BUF DST N1 | destruct SNK as (jb & jd & FL & CKC & BUF & DST & N1) ]).
  pose proof LAY as LAY'. (first [ dand10 LAY as LO L1 L2 L3 F63 L5 L6 L7 SR0 D0 | destruct LAY as (LO & L1 & L2 & L3 & F63 & L5 & L6 & L7 & SR0 & D0) ]).
  pose proof (rw_CB_length _ _ _ _ _ BUF) as LB. rewrite length_app in LB.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n); (B, B + 80)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold snfile, z64, m1w, SN_WRITE in FL.
  carve_frame 64%nat ST.
  do 12 zs.
  zs. brf K0. { exfalso. lia. }
  zs. zs. replace (B + 80 - (B + Z.of_nat (length p)))%Z with (80 - Z.of_nat (length p))%Z by lia.
  zs. brf K1.
  - (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ (length p) (Z.to_nat l) BUF ltac:(lia))) as dR_7; dand3 dR_7 as BA BB BC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ (length p) (Z.to_nat l) BUF ltac:(lia)) as (BA & BB & BC) ]). clear BUF.
    rewrite firstn_app_le, firstn_all in BA by lia.
    zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut; [ eapply memcpy_callv with (src := bs) | post_call_lit rsegs mq ] end.
    { exact BS. } { exact LEN. } { eapply rwc_eq; [exact BB | lia]. }
    { lia. } { lia. } { lia. } { lia. } { assumption. }
    match goal with Hb : rw_cells _ ?mq (B + Z.of_nat (length p))%Z _, MIq : mem_inv _ ?mq |- _ =>
      pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ BA ltac:(eapply rwc_eq; [exact Hb| lia]) ltac:(eapply rwc_eq; [exact BC| lia])) as BUF; clear BA Hb BC;
      rename MIq into MI2 end.
    replace (length p + Z.to_nat l + (80 - length p - Z.to_nat l))%nat with 80%nat in BUF by lia.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold fwritex_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [| assumption].
    unfold fwx. replace (Z.of_nat (length bs) <=? 80 - Z.of_nat (length p))%Z with true by (symmetry; apply Z.leb_le; lia). cbn [fst snd].
    exists (skipn (Z.to_nat l) jb), jd.
    split. { unfold snfile, z64, m1w, SN_WRITE. rewrite length_app, Nat2Z.inj_add, LEN, Z2Nat.id, Z.add_assoc by lia. assumption. }
    split; [assumption|]. split.
    { rewrite <- app_assoc. rewrite skipn_app_exact2 in BUF by lia. exact BUF. }
    split; assumption.
  - (* [comment removed for export] *)
    zs. zs. zs. zs. do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    eapply evt_cut; [ eapply (sn_write_sink ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mq Fp B D n mode w p bs Sr l lo);
                      try reflexivity; try eassumption | ] end.
    { exists jb, jd. refine (conj _ (conj _ (conj _ (conj _ N1)))); [unfold snfile, z64, m1w, SN_WRITE; assumption | assumption | assumption | assumption]. }
    cbv beta. intros ms' P. unfold sn_write_sink_post in P.
    (first [ dex15 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m'; dand7 P as -> MU' WM' MI' ST' SNK' BS' | dand22 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MU' WM' MI' ST' SNK' BS' | destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & SNK' & BS') ]).
    apply evt_done. unfold fwritex_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]. intros. lia. }
    split. { eapply wmono_trans; [exact WM| exact WM']. }
    split; [exact MI'|]. split; [exact ST'|].
    split; [| exact BS'].
    unfold fwx. replace (Z.of_nat (length bs) <=? 80 - Z.of_nat (length p))%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    exact SNK'.
Qed.
End RU_f8qh.


Module RU_pivg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_sszg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Definition T_PTR : Z := 9.
Definition T_INT : Z := 10.

(* [comment removed for export] *)
Definition int_of_slot (v : word) : word := sx32 v.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i : Z) (res : word) (old2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(ARG, ARG + 16); (AP, AP + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' ARG [C8 res; CB 8 old2]
    /\ rw_cells rsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ va_area m' VA slots.

(* [comment removed for export] *)
Lemma pop_arg_int_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ARG AP VA : Z) (slots : list word) (i : Z) (v : word) (old1 old2 : list byte),
  a0 = Z_to_bv 64 ARG -> a1 = Z_to_bv 64 T_INT -> a2 = Z_to_bv 64 AP ->
  rw_cells rsegs m ARG [CB 8 old1; CB 8 old2] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> va_area m VA slots ->
  nth_error slots (Z.to_nat i) = Some v -> (0 <= i)%Z ->
  (ARG + 16 <= AP \/ AP + 8 <= ARG)%Z -> (AP + 8 <= VA)%Z -> (ARG + 16 <= VA)%Z ->
  mem_inv rsegs m ->
  evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i (sx32 v) old2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x273b0) fc None m (seg_rom rsegs)).
Proof.
  intros until old2. intros -> -> -> HA HP HV Hn Hi SEP1 SEP2 SEP3 MI. unfold T_INT. unfold va_area in HV.
  pose proof (munch_refl [(ARG, ARG + 16); (AP, AP + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HA) as B1. pose proof (rw_cells_bound _ _ _ _ HP) as B2. pose proof (bytes_at_bound _ _ _ _ HV) as B3.
  cbn [cells_size csize Nat.add] in B1, B2. rewrite u64s_length in B3. pose proof (nth_error_lt _ _ _ Hn) as IL.
  do 3 zs. if_lit. do 7 zs.
  zs. zs. zs.
  pose proof (va_read4 _ VA slots i v (Z_to_bv 64 (VA + 8 * i)) HV Hn Hi eq_refl) as RD.
  zs. zs. zs.
  replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in * by lia.
  finish. all: unfold va_area; assumption.
Qed.

Lemma pop_arg_ptr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ARG AP VA : Z) (slots : list word) (i : Z) (v : word) (old1 old2 : list byte),
  a0 = Z_to_bv 64 ARG -> a1 = Z_to_bv 64 T_PTR -> a2 = Z_to_bv 64 AP ->
  rw_cells rsegs m ARG [CB 8 old1; CB 8 old2] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> va_area m VA slots ->
  nth_error slots (Z.to_nat i) = Some v -> (0 <= i)%Z ->
  (ARG + 16 <= AP \/ AP + 8 <= ARG)%Z -> (AP + 8 <= VA)%Z -> (ARG + 16 <= VA)%Z ->
  mem_inv rsegs m ->
  evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i v old2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x273b0) fc None m (seg_rom rsegs)).
Proof.
  intros until old2. intros -> -> -> HA HP HV Hn Hi SEP1 SEP2 SEP3 MI. unfold T_PTR. unfold va_area in HV.
  pose proof (munch_refl [(ARG, ARG + 16); (AP, AP + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HA) as B1. pose proof (rw_cells_bound _ _ _ _ HP) as B2. pose proof (bytes_at_bound _ _ _ _ HV) as B3.
  cbn [cells_size csize Nat.add] in B1, B2. rewrite u64s_length in B3. pose proof (nth_error_lt _ _ _ Hn) as IL.
  do 3 zs. if_lit. do 7 zs.
  zs. zs. zs.
  pose proof (va_read8 _ VA slots i v (Z_to_bv 64 (VA + 8 * i)) HV Hn Hi eq_refl) as RD.
  zs. zs. zs.
  replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in * by lia.
  finish. all: unfold va_area; assumption.
Qed.
End RU_pivg.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_sszg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_f8qh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RU_s3fk.RU_pivg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMT_C : list cell := [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99); C1 (Z_to_bv 8 0)].   (* [comment removed for export] *)
Definition FMT_PFX : list cell :=                                                               (* [comment removed for export] *)
  [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 47); C1 (Z_to_bv 8 0)].
Definition FMT_HOST : list cell :=                                                              (* [comment removed for export] *)
  [C1 (Z_to_bv 8 72); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32);
   C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99);
   C1 (Z_to_bv 8 0)].
Definition DIR_S : list cell := [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115)].  (* [comment removed for export] *)
Definition DIR_C : list cell := [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99)].                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sint32 (v : word) : Z := bv_swrap 32 (bv_unsigned v).
(* [comment removed for export] *)
Definition out_s (P : word) (hs : list byte) : list byte := firstn (Z.to_nat (strnlen_res (sint32 P) hs)) hs.
(* [comment removed for export] *)
Definition out_c (ch : word) : list byte := [Z_to_bv 8 (bv_unsigned ch mod 256)].

Lemma swrap32_id : forall z, (- 2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof. intros. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.
Lemma sint32_range : forall v, (- 2^31 <= sint32 v < 2^31)%Z.
Proof. intros. unfold sint32. pose proof (bv_swrap_in_range 32 (bv_unsigned v) ltac:(discriminate)) as R.
  unfold bv_half_modulus, bv_modulus in R. cbn in R. lia. Qed.

Lemma signed_lit : forall z, (- 2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma fr1_recast : forall segs m a q0 q1 q2 q3 q4 rest,
  rw_cells segs m a (C8 q0 :: C8 q1 :: C8 q2 :: C8 q3 :: C8 q4 :: rest) ->
  rw_cells segs m a (CB 40 (le8 q0 ++ le8 q1 ++ le8 q2 ++ le8 q3 ++ le8 q4) :: rest).
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn in W |- *. tauto.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma fra_recast : forall segs m a v j, rw_cells segs m a [C8 v; CB 8 j] -> rw_cells segs m a [CB 8 (le8 v); CB 8 j].
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn in W |- *. tauto.
  - reflexivity.
Qed.
Lemma fr2_recast3 : forall segs m a n1 n3 (l1 l3 : list byte) (b : byte) rest,
  rw_cells segs m a (CB n1 l1 :: C1 b :: CB n3 l3 :: rest) ->
  rw_cells segs m a (CB (n1 + 1 + n3) (l1 ++ b :: l3) :: rest).
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. split; [rewrite length_app; cbn [length]; lia|tauto].
  - cbn [cells_bytes cbytes]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma ro_cells_app : forall segs m A cs1 cs2,
  ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app. rewrite bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.
Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_TOP : Z := 0x26630.
Definition INT_MAX : Z := 2147483647.

Section PCTOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word).
  Variables (FMT : list cell) (m0 : word -> option byte).

  (* [comment removed for export] *)
  Definition pc_lits : list cell :=
    [C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 (Z_to_bv 64 (bv_unsigned sp + 96)); C8 (Z_to_bv 64 (bv_unsigned sp + 264)); C8 (Z_to_bv 64 (bv_unsigned sp + 0));
     C8 (Z_to_bv 64 75913); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SSP_GUARD); C8 (Z_to_bv 64 214748364)].
  Definition pc_saved : list cell :=
    [C8 canary; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition pc_layout : Prop :=
    let q := bv_unsigned sp in
    Fp = (q + 368)%Z /\ B = (q + 16)%Z /\ (0 <= lo)%Z /\ (lo <= q - PC2_DEPTH)%Z /\ (GLOBALS_TOP <= lo)%Z
    /\ (q + 672 <= VA)%Z /\ (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z
    /\ (IMG_LO <= A)%Z /\ (A + Z.of_nat (cells_size FMT) <= RO_TOP)%Z /\ dst_ok D n /\ (D + Z.of_nat n <= lo)%Z
    /\ (HS + Z.of_nat (length hs) <= lo)%Z /\ (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z.

  Definition pctop (off cnt l i : Z) (o : list byte) : machine_state -> Prop :=
    fun ms => exists (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x s9x s11x t3 t4 t5 t6 : word)
                     (j40 ja1 ja2 j304 w p : list byte) (m : word -> option byte),
      ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
                   a0 a1 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 cnt) (Z_to_bv 64 Fp) (Z_to_bv 64 (A + off))
                   s6x s7x s8x s9x (Z_to_bv 64 l) s11x t3 t4 t5 t6)
              F (Z_to_bv 64 PC_TOP) fc None m (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 608, bv_unsigned sp + 8); (B, B + 80); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m0 m
      /\ wmono rsegs m0 m /\ mem_inv rsegs m
      /\ stk rsegs m lo (bv_unsigned sp + -544)
      /\ ro_cells rsegs m A FMT
      /\ rw_cells rsegs m (bv_unsigned sp + -544) (CB 40 j40 :: pc_lits)
      /\ rw_cells rsegs m (bv_unsigned sp + -432) [CB 8 ja1; CB 8 ja2]
      /\ rw_cells rsegs m (bv_unsigned sp + -416) (CB 304 j304 :: pc_saved)
      /\ sink Fp B D n m mode w p /\ w ++ p = o
      /\ rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * i))]
      /\ va_area m VA slots /\ bytes_at rsegs m HS hs /\ ssp_cells m canary.
End PCTOP.

Ltac unpack_top H :=
  let w := fresh "w" in let p := fresh "p" in
  destruct H as (rax & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & s2x & s6x & s7x & s8x & s9x & s11x & x3 & x4 & x5 & x6
                 & j40 & ja1 & ja2 & j304 & w & p & mq & -> & MU & WM & MI & ST & HF & FR1 & FRA & FR2 & SNK & HO & APC & VAA & HSB & SSP1 & SSP2);
  unfold pc_lits in FR1; unfold pc_saved in FR2; unfold GOT_SSP, SSP_GUARD in SSP1, SSP2, FR1; unfold va_area in VAA.

(* [comment removed for export] *)
Ltac sx1 := match goal with |- context [bv_swrap 32 ?z] =>
  lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (swrap32_id z) by lia end end.
Ltac sx2 := match goal with |- context [bv_signed (Z_to_bv 64 ?z)] =>
  lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (signed_lit z) by lia end end.
Ltac sx3 := match goal with |- context [(?a mod 18446744073709551616)%Z] =>
  lazymatch a with context [bv_swrap 32 _] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end.
Ltac sx := repeat first [sx1 | sx3]; repeat sx2.
Ltac sxh K := repeat match type of K with context [bv_swrap 32 ?z] =>
    lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (swrap32_id z) in K by lia end end;
  repeat match type of K with context [(?a mod 18446744073709551616)%Z] =>
    lazymatch a with context [bv_swrap 32 _] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) in K by lia end end;
  repeat match type of K with context [bv_signed (Z_to_bv 64 ?z)] =>
    lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (signed_lit z) in K by lia end end.
Ltac brf K := if_cases K; zify_cond K; sxh K.
Ltac br K := brf K; try (exfalso; lia).
(* [comment removed for export] *)
Ltac pack_top :=
  unfold pctop, pc_lits, pc_saved, PC_TOP, INT_MAX, SSP_GUARD;
  repeat (lazymatch goal with |- ex _ => eexists end);
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))));
  [ | eassumption | eassumption | assumption | try eassumption | eassumption | try eassumption | try eassumption | try eassumption
    | pack_sink | try reflexivity | try eassumption | first [eassumption | unfold va_area; eassumption] | eassumption | assumption | assumption ].
Ltac fwritex_side :=
  lazymatch goal with
  | |- sink _ _ _ _ _ _ _ _ => pack_sink
  | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
  | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; first [ eassumption | apply bytes_at_nil; lia ]
  | |- sn_layout _ _ _ _ _ _ _ _ => unfold sn_layout; rewrite ?unsigned_lit by lia; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia
  | |- mem_inv _ _ => assumption
  | |- @eq nat _ _ => reflexivity || (cbn; lia) || (rewrite ?length_app, ?firstn_length; cbn; lia)
  | |- ?G => first [ reflexivity | lia | idtac "FWX-SIDE-FAIL:" G; fail ]
  end.
Ltac call_fwritex :=
  call_lit fwritex_spec by (idtac; fwritex_side);
  clear_rdf;
  match goal with H : stk _ _ _ _ |- _ => let n := fresh "ST" in rename H into n end;
  match goal with H : sink _ _ _ _ _ _ _ _ |- _ =>
    first [ rewrite fwx_fits in H by (cbn; lia) | rewrite fwx_spills in H by (cbn; lia) | idtac ]; cbn [fst snd] in H; rewrite ?app_nil_r in H;
    let a := fresh "FL" in let b := fresh "CKC" in let c := fresh "BUF" in let d := fresh "DST" in unpack_sink H a b c d end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_entry : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word) (FMT : list cell),
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
  stk rsegs m lo q -> ro_cells rsegs m A FMT -> ssp_cells m canary -> sink Fp B D n m mode [] [] ->
  rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA slots -> bytes_at rsegs m HS hs ->
  mem_inv rsegs m ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT ->
  evt rsegs (pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT m 0 0 0 0 [])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).
Proof.
  intros until FMT. cbv zeta. intros -> -> -> -> -> ST HF [SSP1 SSP2] SNK APC VAA HSB MI LAY.
  (first [ dand13 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD) ]).
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp + 8); (B, B + 80); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB.
  unpack_sink SNK FL CKC BUF DST. unfold va_area in VAA.
  rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
  (* [comment removed for export] *)
  carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB rsegs _ _ [] _ _ [] [8; 8; 304]%nat) in FR0; [|reflexivity].
  cbn [mk_CB_cells app] in FR0.
  apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR0. destruct FR0 as [FRA FRM].
  cbn [cells_size csize Nat.add] in FRM.
  replace (bv_unsigned sp + -432 + Z.of_nat 16)%Z with (bv_unsigned sp + -416)%Z in FRM by lia.
  lazymatch type of FR with rw_cells _ ?mq ?atop ?top => lazymatch type of FRM with rw_cells _ _ ?amid [?mid] =>
    assert (FR2 : rw_cells rsegs mq amid (mid :: top))
      by (apply (proj2 (rw_cells_app rsegs mq amid [mid] top)); split; [exact FRM|];
          cbn [cells_size csize Nat.add]; replace (amid + Z.of_nat 304)%Z with atop by lia; exact FR)
  end end.
  clear FR FRM.
  name_junk FRA. name_junk FR2.
  (* [comment removed for export] *)
  lazymatch type of FR1 with rw_cells _ ?mq ?a [?c0; ?c1; ?c2; ?c3; ?c4; C8 sp; ?c6; ?c7; ?c8; ?c9] =>
    assert (FR1' : rw_cells rsegs mq a [c0; c1; c2; c3; c4; C8 (Z_to_bv 64 (bv_unsigned sp + 0)); c6; c7; c8; c9])
      by (rewrite Z.add_0_r, (Z_to_bv_bv_unsigned sp); exact FR1); clear FR1; rename FR1' into FR1 end.
  apply evt_done. unfold pctop, pc_lits, pc_saved, PC_TOP, INT_MAX, SSP_GUARD.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split. { rewrite Z.add_0_r. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; [eassumption|].
  split; [exact FR1|]. split; [exact FRA|]. split; [exact FR2|].
  split; [pack_sink|]. split; [reflexivity|].
  split. { rewrite Z.mul_0_r, Z.add_0_r. exact APC. }
  split; [exact VAA|]. split; [assumption|]. split; assumption.
Qed.
