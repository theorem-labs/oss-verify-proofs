(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_fwritex.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac flia_has_zdef := match goal with x := _ : Z |- _ => idtac end.   (* [comment removed for export] *)
Local Ltac flia ::= first [ sassumption | tryif flia_has_zdef then first [ slim; lia | lia ] else lia | assumption ].
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITEX : Z := 0x1b724.
Definition FWX_TAIL : Z := 0x1b81c.
Definition FWRITEX_DEPTH : Z := 208.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.add _ (zlength (f_wbuf _))) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (zlength _) => fail   (* [comment removed for export] *)
  | |- inr64 (zlength (firstn (Z.to_nat (Z.sub (zlength _) _)) _)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.sub (Z.add _ (f_bufsize _)) (Z.modulo (Z.add _ (zlength (f_wbuf _))) (18446744073709551616)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = y mod 2^64.
Proof. intros y. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sx32_neg : forall w : word, 2147483648 <= bv_unsigned w mod 4294967296 -> 9223372036854775808 <= bv_unsigned (sx32 w).
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hz. Qed.

(* [comment removed for export] *)
Lemma zbv_mod_sub : forall a k, (Z_to_bv 64 (a mod 18446744073709551616 - k) : word) = Z_to_bv 64 (a - k).
Proof.
  intros a k. rewrite <- (Z_to_bv_mod64 (a mod 18446744073709551616 - k)), <- (Z_to_bv_mod64 (a - k)).
  change (2^64) with 18446744073709551616. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.
Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.
Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.
Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.
Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.
Definition split_at_znth__stmt : Prop := forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Section Sz10.
Variables cs i : ltac2:(SecDiet.SzSec.tyM 'split_at_znth__stmt "vv" @cs).
#[using="Type"] Lemma split_at_znth__body : ltac2:(SecDiet.SzSec.bodyP 'split_at_znth__stmt "vv").
Proof.
  intros Hi.
 unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed.
End Sz10.
Lemma split_at_znth : ltac:(let t := eval cbv delta [split_at_znth__stmt] in split_at_znth__stmt in exact t).
Proof. intros cs i. ltac2:(SecDiet.SzSec.closeP 'split_at_znth__body "vv"). Qed.
Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite firstn_map. reflexivity. Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(Dst, Dst + N)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at ssegs m' Src src.
Definition memcpy_callw__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at ssegs m Src src -> length src = Z.to_nat N -> rw_cells ssegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src) -> (0 <= N < 2^64) -> (0 <= Src < 2^64) -> (0 <= Dst < 2^64) -> mem_inv ssegs m ->
  evt ssegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz13.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_callw__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.
End Sz13.
Lemma memcpy_callw : ltac:(let t := eval cbv delta [memcpy_callw__stmt] in memcpy_callw__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_callw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' Fp (file_cells flags rpos rend closefn wend (wpos + l) wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail)
    /\ rw_cells ssegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at ssegs m' S src.

Definition fwx_tail__stmt : Prop := forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells ssegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells ssegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail) ->
  rw_cells ssegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at ssegs m S src -> Z.of_nat (length src) = l ->
  stk ssegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono ssegs m0 m -> mem_inv ssegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (l = 0 \/ S + l <= lo \/ bv_unsigned sp <= S) -> (l = 0 \/ S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  evt ssegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b81c) fc None m (seg_rom ssegs)).
Section Sz14.
Variables x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo : ltac2:(SecDiet.SzSec.tyM 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
#[using="Type"] Lemma fwx_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  unfold file_cells in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB ssegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  call memcpy_callw.
  1:{ exact SRC. }
  1:{ rewrite Nat2Z.id. reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
  rewrite !Nat2Z.id in *.
  destruct SEPS3 as [L0 | SEPS3].
  all: do 4 step.
  all: do 9 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells ssegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (rw_cells_app ssegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  all: cbn [app] in DST'; rewrite !LEN in *.
  all: unfold fwx_ret_post, file_cells; sys_finish.
  all: lazymatch goal with |- bytes_at _ _ _ ?bs => destruct bs; [apply bytes_at_nil; lia | exfalso; cbn [length] in LEN; lia] end.
Qed.
End Sz14.
Lemma fwx_tail : ltac:(let t := eval cbv delta [fwx_tail__stmt] in fwx_tail__stmt in exact t).
Proof. intros x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo. ltac2:(SecDiet.SzSec.closeP 'fwx_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Scan.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (Fp wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis SRC : bytes_at ssegs m S (to_bytes bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.
  Hypothesis FPR : 0 <= Fp < 2^64.

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b7b8) fc None m (seg_rom ssegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evt ssegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b7d0) fc None m (seg_rom ssegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evt ssegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b7f4) fc None m (seg_rom ssegs)).

  Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evt ssegs POST (scan_st k a3).
  Proof using BYT FD L1 LEN LHI NF SRC. pin_using (fun (BYT FD L1 LEN LHI NF SRC : unit) => tt).
    induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_to_bytes in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes ssegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read ssegs m S (to_bytes bs) (l - 1 - k) 1 SRC) by (rewrite ?length_to_bytes; lia).
      f_equal. unfold to_bytes. rewrite skipn_map, firstn_map. unfold znth.
      destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
      destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
      - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
      - cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
    pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
    assert (CR : 0 <= znth bs (l - 1 - k) < 256).
    { unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
    pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
    replace (l - 1 - k + 1) with (l - k) in SPL by lia.
    step.
    replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
    step.
    unfold zxb. rewrite (unsigned_lit8 _ CR).
    step. if_cases Hnl; zify_cond Hnl.
    - (* [comment removed for export] *) apply FD; [lia|].
      rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
      unfold zlength. rewrite length_firstn. lia.
    - step. step. step.
      if_cases Hend; zify_cond Hend.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
        apply (IH (k + 1)).
        { clear - Hn. lia. }
        { clear - Hk Hend. lia. }
        { replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
          rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
          replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
          cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
        replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
        apply NF.
        rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
        rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
        intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells ssegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at ssegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Section RetB.
  Context {St : Type}.
  Lemma implM_retb : forall {A B} (a : A) (f : A -> M St B) (s : St) Q ms,
    implM ssegs (f a) s Q ms -> implM ssegs (mbind (mret a) f) s Q ms.
  Proof using Type. pin_using tt. intros A B a f s Q ms H. exact H. Qed.
End RetB.

Lemma evt_ms_eq : forall P ms ms', evt ssegs P ms' -> ms = ms' -> evt ssegs P ms.
Proof. intros P ms ms' H ->. exact H. Qed.
Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; rewrite ?length_firstn, ?length_skipn; cbn [length Z.of_nat]; lia]).

(* [comment removed for export] *)
Definition fx_inv (f f' : file_st) : Prop :=
  f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
  /\ f_wactive f' = true /\ f_rbuf f' = (if f_wactive f then f_rbuf f else [])
  /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

Lemma wfn_after_write : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.
Lemma wbuf_after_write : forall f, f_wbuf (f_after_write f) = [].
Proof. intros f. reflexivity. Qed.
Lemma fx_inv_after_write : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (f_after_write f1).
Proof.
  unfold fx_inv, f_after_write. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct (f_stdoutw f1) eqn:E; cbn; rewrite ?E; repeat split; auto; intros HH; discriminate HH.
Qed.
Lemma fx_inv_set_w : forall f0 f1 w, fx_inv f0 f1 -> fx_inv f0 (set_w true w f1).
Proof.
  unfold fx_inv. intros f0 f1 w (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn. repeat split; auto.
Qed.
Lemma lbf_of_cases : forall f, (f_lbf_nl f = true /\ lbf_of f = 10) \/ (f_lbf_nl f = false /\ lbf_of f = 4294967295).
Proof. intros f. unfold lbf_of. destruct (f_lbf_nl f); [left|right]; split; reflexivity. Qed.

(* [comment removed for export] *)
Definition buf_split__stmt : Prop := forall m B n (wbz : list Z) (bufbytes : list byte),
  rw_cells ssegs m B [CB n bufbytes] -> firstn (length wbz) bufbytes = to_bytes wbz -> (length wbz <= n)%nat ->
  rw_cells ssegs m B [CB (length (to_bytes wbz)) (to_bytes wbz)]
  /\ rw_cells ssegs m (B + zlength wbz) [CB (n - length wbz) (skipn (length wbz) bufbytes)].
Section Sz24.
Variables m B n wbz bufbytes : ltac2:(SecDiet.SzSec.tyM 'buf_split__stmt "vvvvv" @m).
#[using="Type"] Lemma buf_split__body : ltac2:(SecDiet.SzSec.bodyP 'buf_split__stmt "vvvvv").
Proof.
  intros BUF BUFP LE.
  assert (LBB : length bufbytes = n) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  apply (rw_cells_split_CB ssegs _ _ [] n bufbytes [] [length wbz; n - length wbz]%nat) in BUF; [| cbn; lia].
  cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
  apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
  rewrite length_to_bytes. unfold zlength. split; [exact BUFa | exact BUFb].
Qed.
End Sz24.
Lemma buf_split : ltac:(let t := eval cbv delta [buf_split__stmt] in buf_split__stmt in exact t).
Proof. intros m B n wbz bufbytes. ltac2:(SecDiet.SzSec.closeP 'buf_split__body "vvvvv"). Qed.

(* [comment removed for export] *)
Definition buf_join__stmt : Prop := forall m B n (pre src rest : list byte),
  rw_cells ssegs m B [CB (length pre) pre] ->
  rw_cells ssegs m (B + Z.of_nat (length pre)) [CB (length src) src; CB (n - length pre - length src) rest] ->
  (length pre + length src <= n)%nat ->
  exists bb, rw_cells ssegs m B [CB n bb] /\ firstn (length pre + length src) bb = pre ++ src.
Section Sz25.
Variables m B n pre src rest : ltac2:(SecDiet.SzSec.tyM 'buf_join__stmt "vvvvvv" @m).
#[using="Type"] Lemma buf_join__body : ltac2:(SecDiet.SzSec.bodyP 'buf_join__stmt "vvvvvv").
Proof.
  intros Ha Hb LE.
  pose proof (rw_cells_bound _ _ _ _ Hb) as BB.
  assert (LR : length rest = (n - length pre - length src)%nat) by (destruct Hb as [[WF _] _]; cbn in WF; exact (proj1 (proj2 WF))).
  assert (J : rw_cells ssegs m B ([] ++ ([CB (length pre) pre] ++ [CB (length src) src; CB (n - length pre - length src)%nat rest]) ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app ssegs _ _ [_] _)); split; [exact Ha|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hb. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite !app_nil_r in J.
  exists (pre ++ src ++ rest). split.
  - replace n with (length pre + (length src + (n - length pre - length src + 0)))%nat at 1 by lia. exact J.
  - rewrite app_assoc, firstn_app, length_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. rewrite length_app. lia.
Qed.
End Sz25.
Lemma buf_join : ltac:(let t := eval cbv delta [buf_join__stmt] in buf_join__stmt in exact t).
Proof. intros m B n pre src rest. ltac2:(SecDiet.SzSec.closeP 'buf_join__body "vvvvvv"). Qed.

Section Cont.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 f1 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
            (s : list Z) (S lo : Z) (canary : word) (m : mem).
  #[local] Notation wb := (f_wbuf f1) (only parsing).
  #[local] Notation bs := (f_bufsize f1) (only parsing).
  #[local] Notation l := (zlength s) (only parsing).
  #[local] Notation RP := (if f_wactive f0 then rpos else 0) (only parsing).
  #[local] Notation RE := (if f_wactive f0 then rend else 0) (only parsing).

  Definition fx_W : list (Z * Z) := [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + f_bufsize f0)].

  (* [comment removed for export] *)
  Definition fwritex_post : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch fx_W m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags RP RE closefn (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells ssegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Hypothesis ACT : f_wactive f1 = true.
  Hypothesis INV01 : fx_inv f0 f1.
  Hypothesis EBS : f_bufsize f1 = f_bufsize f0.
  Hypothesis EFD : f_fd f1 = f_fd f0.
  Hypothesis CH : if f_chan f1 then (f_fd f1 = 1 \/ f_fd f1 = 2) else (3 <= f_fd f1 < 2^31).
  Hypothesis LO : lo <= bv_unsigned sp - FWRITEX_DEPTH.
  Hypothesis GLO : 0x55000 <= lo.
  Hypothesis SP63 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis B0 : 0 < B.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis BS0 : 0 <= bs.
  Hypothesis WBL : zlength wb <= bs.
  Hypothesis S0 : 0 <= S < 2^64.
  Hypothesis S64 : S + l <= 2^64.
  Hypothesis Shi : l = 0 \/ S + l <= 2^47.   (* [comment removed for export] *)
  Hypothesis LENW : zlength wb + l <= 2^26.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) s.
  Hypothesis SEPS : l = 0 \/ ((S + l <= lo \/ bv_unsigned sp <= S) /\ (S + l <= Fp \/ Fp + 232 <= S) /\ (S + l <= B \/ B + bs <= S)).
  Hypothesis SEPB : (B + bs <= lo \/ bv_unsigned sp <= B) /\ (B + bs <= Fp \/ Fp + 232 <= B).
  Hypothesis FL64 : Z.land (bv_unsigned flags) F_SVB = 0.

  (* [comment removed for export] *)
  Definition at40c (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) a0 (Z_to_bv 64 (B + bs)) a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 S) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1b758) fc None m1 (seg_rom ssegs).

  (* [comment removed for export] *)
  Definition at_tail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word) (j8 : list byte) (mode2 : word) (bufbytes2 : list byte) (m2 : mem) (f2 : file_st) (i : Z),
    rw_cells ssegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ssegs m2 Fp (fcells flags RP RE closefn (B + bs) (B + zlength (f_wbuf f2)) B readfn (wfn_of f2) seekfn B bs prev next (f_fd f1) mode2 (lbf_of f2) tail) ->
    rw_cells ssegs m2 B [CB (Z.to_nat bs) bufbytes2] -> firstn (length (f_wbuf f2)) bufbytes2 = to_bytes (f_wbuf f2) ->
    ssp_cells m2 canary -> stk ssegs m2 lo (bv_unsigned sp + -64) -> mem_inv ssegs m2 -> munch fx_W m m2 -> wmono ssegs m m2 ->
    bytes_at ssegs m2 S (to_bytes s) ->
    fx_inv f0 f2 -> 0 <= i <= l -> zlength (f_wbuf f2) + (l - i) <= bs ->
    evt ssegs (fwritex_post (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2) st)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 (l - i)) (Z_to_bv 64 (B + zlength (f_wbuf f2)))
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (S + i)) (Z_to_bv 64 i) x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b81c) fc None m2 (seg_rom ssegs)).
  Section Sz26.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i : ltac2:(SecDiet.SzSec.tyM 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma at_tail__body : ltac2:(SecDiet.SzSec.bodyP 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL : unit) => tt).
    intros FR2 FC2 BUF2 BUFP2 SSP2 ST2 MI2 MU2 WM2 SRC2 INV2 IR FIT.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP2 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC2) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC2) as BSRC. rewrite length_to_bytes in BSRC.
    assert (BS2 : f_bufsize f2 = f_bufsize f1) by (destruct INV01 as (_&_&E1&_); destruct INV2 as (_&_&E2&_); congruence).
    pose proof FIT as FIT'. unfold zlength in FIT', WBL, IR, BSRC |- .
    destruct (buf_split m2 B (Z.to_nat (f_bufsize f1)) (f_wbuf f2) bufbytes2 BUF2 BUFP2 ltac:(lia)) as [BUFa BUFb].
    (* [comment removed for export] *)
    assert (XS : exists S', (Z_to_bv 64 (S + i) : word) = Z_to_bv 64 S' /\ 0 <= S' < 2^64
              /\ bytes_at ssegs m2 S' (to_bytes (skipn (Z.to_nat i) s))
              /\ (S' = S + i \/ (S' = 0 /\ i = Z.of_nat (length s)))).
    { destruct (Z.eq_dec (S + i) (2^64)) as [WRAP|NOWRAP].
      - exists 0. split; [rewrite WRAP; rewrite <- (Z_to_bv_mod64 (2^64)); reflexivity|]. split; [lia|].
        split; [| right; lia]. replace (skipn (Z.to_nat i) s) with (@nil Z) by (symmetry; apply skipn_all2; lia).
        apply bytes_at_nil. lia.
      - exists (S + i). split; [reflexivity|]. split; [lia|]. split; [| left; reflexivity].
        rewrite to_bytes_skipn. replace (S + i) with (S + Z.of_nat (Z.to_nat i)) by lia. apply bytes_at_skipn; [exact SRC2 | rewrite length_to_bytes; lia]. }
    destruct XS as (S' & ES' & HS' & SRCi & S'c). rewrite ES'.
    unfold fcells in FC2.
    eapply evt_mono.
    { eapply fwx_tail with (lo := lo) (m0 := m2) (i := i) (src := to_bytes (skipn (Z.to_nat i) s)) (S := S') (l := Z.of_nat (length s) - i)
         (cap := (Z.to_nat (f_bufsize f1) - length (f_wbuf f2))%nat) (junk := skipn (length (f_wbuf f2)) bufbytes2) (wpos := B + zlength (f_wbuf f2));
        fastfirst (first [ noevar_assumption | exact FR2 | exact FC2 | unfold zlength; exact BUFb | exact SRCi | exact ST2 | exact MI2 | apply wmono_refl | apply munch_refl
              | rewrite ?length_to_bytes, ?length_skipn; unfold zlength in *; (keep_hyps f1 Fp s f2 i FIT' IR sp lo LO GLO SP63 B B0 BShi SEPB S S' SEPS S'c LENW HS'; lia)
              | destruct SEPB as [SB1 SB2]; unfold zlength in *; fail
              | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps f1 Fp B s f2 i S' IR L0 sp lo; lia)
              ]). }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3).
    lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
    rewrite length_to_bytes, length_skipn in DST3.
    unfold zlength in MU3, FC3, DST3, BUFa.
    assert (GOT3 : rw_cells ssegs m3 140832 [C8 (Z_to_bv 64 343304)]).
    { eapply (rw_cells_transport ssegs _ m2 m3); [exact GOT | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP1 BSEP1 FIT'; lia)]. }
    assert (GUARD3 : rw_cells ssegs m3 343304 [C8 canary]).
    { eapply (rw_cells_transport ssegs _ m2 m3); [exact GUARD | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP2 BSEP2 FIT'; lia)]. }
    assert (BUFa3 : rw_cells ssegs m3 B [CB (length (to_bytes (f_wbuf f2))) (to_bytes (f_wbuf f2))]).
    { eapply (rw_cells_transport ssegs _ m2 m3); [exact BUFa | exact MU3 | exact WM3 | cbn; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo f2 i SEPB IR FIT'; lia)]. }
    rewrite length_to_bytes in BUFa3.
    destruct (buf_join m3 B (Z.to_nat (f_bufsize f1)) (to_bytes (f_wbuf f2)) (to_bytes (skipn (Z.to_nat i) s))
                (skipn (length s - Z.to_nat i) (skipn (length (f_wbuf f2)) bufbytes2))) as [bb [BUF3 BUFP3]].
    { rewrite length_to_bytes. exact BUFa3. }
    { rewrite !length_to_bytes, length_skipn. exact DST3. }
    { rewrite !length_to_bytes, length_skipn. lia. }
    replace (i + (Z.of_nat (length s) - i)) with (Z.of_nat (length s)) by lia.
    unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_set_w; exact INV2|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [apply (munch_trans _ m m2 m3); [exact MU2 | eapply munch_weaken; [| exact MU3]; unfold sub_fp, fx_W; cbn [outside]; intros; lia]|].
    split; [eapply wmono_trans; [exact WM2 | exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split.
    { cbn [f_wbuf set_w]. change (wfn_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (wfn_of f2).
      change (lbf_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (lbf_of f2).
      unfold fcells, zlength. rewrite length_app, length_skipn.
      replace (B + Z.of_nat (length (f_wbuf f2) + (length s - Z.to_nat i))) with (B + Z.of_nat (length (f_wbuf f2)) + (Z.of_nat (length s) - i)) by lia.
      exact FC3. }
    split; [exact BUF3|].
    split; [cbn [f_wbuf set_w]; rewrite to_bytes_app, length_app, <- (length_to_bytes (f_wbuf f2)), <- (length_to_bytes (skipn _ s)); exact BUFP3|].
    split; [cbn [f_wbuf set_w]; unfold zlength; rewrite length_app, length_skipn; lia|].
    split; [exact GOT3 | exact GUARD3].
  Qed.
  End Sz26.
  Lemma at_tail : ltac:(let t := eval cbv delta [at_tail__stmt] in at_tail__stmt in exact t).
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i. ltac2:(SecDiet.SzSec.closeP 'at_tail__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Section AtM1.
    Variables (j8 : list byte) (mode1 : word) (bufbytes : list byte) (m1 : mem).
    Hypothesis FR1 : rw_cells ssegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FC1 : rw_cells ssegs m1 Fp (fcells flags RP RE closefn (B + bs) (B + zlength wb) B readfn (wfn_of f1) seekfn B bs prev next (f_fd f1) mode1 (lbf_of f1) tail).
    Hypothesis BUF1 : rw_cells ssegs m1 B [CB (Z.to_nat bs) bufbytes].
    Hypothesis BUFP : firstn (length wb) bufbytes = to_bytes wb.
    Hypothesis SSP1 : ssp_cells m1 canary.
    Hypothesis ST1 : stk ssegs m1 lo (bv_unsigned sp + -64).
    Hypothesis MI1 : mem_inv ssegs m1.
    Hypothesis MU1 : munch fx_W m m1.
    Hypothesis WM1 : wmono ssegs m m1.
    Hypothesis SRC1 : bytes_at ssegs m1 S (to_bytes s).

    Lemma wb_at : bytes_at ssegs m1 B (to_bytes wb).
    Proof using BUF1 BUFP. pin_using (fun (BUF1 BUFP : unit) => tt). eapply CB_prefix_bytes_at; [exact BUF1|]. rewrite length_to_bytes. exact BUFP. Qed.

    (* [comment removed for export] *)
    Definition cont_nofit__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      bs - zlength wb < l ->
      implM ssegs (file_writefn f1 s) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz28.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_nofit__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_nofit__body : ltac2:(SecDiet.SzSec.bodyP 'cont_nofit__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 : unit) => tt).
      intros NOFIT.
 unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fx_W in MU1.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
      unfold zlength in *.
      apply implM_prefix.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
      do 13 zs.
      rewrite (ret_pc_even (wfn_of f1)) by lia.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evt_done.
      eapply implM_post_evt.
      { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
          (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail).
        all: fastfirst (first [ noevar_assumption | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRC1 | exact wb_at | exact FL64
                   | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; (keep_hyps f1 Fp B s BS0 Hr; lia)]]
                   | unfold zlength in *; (keep_hyps f1 Fp B s B0 BShi WBL sp S lo Shi Hr LENW SEPS SEPB; lia) | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp s lo LO; lia)
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                   | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [left; destruct s; [reflexivity | exfalso; unfold zlength in L0; cbn [length] in L0; (keep_hyps f1 Fp z l L0; lia)] | right; unfold zlength in *; split; fail]
                   | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia) ]). }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2.
      pose proof (rw_cells_transport ssegs _ m1 m2 _ _ BUF1 MU2 WM2 ltac:(destruct SEPB as [SB1 SB2]; cbn; (keep_hyps sp f1 Fp B s lo LO BS0 SEPB; lia))) as BUF2.
      apply evt_done. unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_after_write; exact INV01|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { apply (munch_trans _ m m1 m2).
        * exact MU1.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W, FWRITEX_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [rewrite wfn_after_write, wbuf_after_write; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC2|].
      split; [exact BUF2|]. split; [reflexivity|]. split; [rewrite wbuf_after_write; unfold zlength in *; cbn; lia | exact SSP2].
    Qed.
    End Sz28.
    Lemma cont_nofit : ltac:(let t := eval cbv delta [cont_nofit__stmt] in cont_nofit__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_nofit__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_fit_plain__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = false ->
      implM ssegs (mret (set_w true (wb ++ s) f1)) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz29.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_fit_plain__body : ltac2:(SecDiet.SzSec.bodyP 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 : unit) => tt).
      intros FIT LBF.
 unfold at40c. apply implM_ret.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 4294967295) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. zs. zs.
      pose proof (sx32_neg (Z_to_bv 64 4294967295) ltac:(vm_compute; discriminate)) as NEG.
      if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      change (skipn (Z.to_nat 0) s) with s in |- *.
      replace s with (skipn (Z.to_nat 0) s) at 1 by reflexivity.
      replace (Z_to_bv 64 (zlength s) : word) with (Z_to_bv 64 (zlength s - 0) : word) by (f_equal; lia).
      replace (Z_to_bv 64 S : word) with (Z_to_bv 64 (S + 0) : word) by (f_equal; lia).
      eapply at_tail; fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01 | unfold zlength in *; lia ]).
    Qed.
    End Sz29.
    Lemma cont_fit_plain : ltac:(let t := eval cbv delta [cont_fit_plain__stmt] in cont_fit_plain__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_fit_plain__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_lbf__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = true ->
      implM ssegs (f2 <- (if 0 <? after_last_nl s then file_writefn f1 (firstn (Z.to_nat (after_last_nl s)) s) else mret f1) ;;
                   mret (set_w true (f_wbuf f2 ++ skipn (Z.to_nat (after_last_nl s)) s) f2))
            st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz30.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_lbf__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_lbf__body : ltac2:(SecDiet.SzSec.bodyP 'cont_lbf__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 : unit) => tt).
      intros FIT LBF.
 unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 10) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      pose proof (after_last_nl_range s) as IR. unfold zlength in IR.
      apply implM_prefix.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. rewrite (sx32_small 10) by lia. zs. zs.
      if_cases Hl; zify_cond Hl. 1:{ exfalso. lia. }
      zs. if_cases Hz; zify_cond Hz.
      - (* [comment removed for export] *)
        assert (NL0 : after_last_nl s = 0) by (unfold zlength in *; rewrite ?Z.mod_small in Hz by lia; lia).
        rewrite NL0. cbn [Z.ltb Z.to_nat].
        apply evt_done. apply implM_retb. apply implM_ret.
        eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
          fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
      - (* [comment removed for export] *)
        zs. zs. zs. zs.
        eapply evt_ms_eq; [ eapply scan_loop with (k := 0) (n := Z.to_nat (zlength s)) (bs := s) | ms_eq ].
        + exact SRC1.
        + reflexivity.
        + exact BYT.
        + unfold zlength in *; lia.
        + unfold zlength in *; lia.
        + (* [comment removed for export] *)
          intros a3' NL0. zs. zs.
          apply evt_done. rewrite NL0. cbn [Z.ltb Z.to_nat]. apply implM_retb. apply implM_ret.
          change (skipn 0 s) with (skipn (Z.to_nat 0) s).
          eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
            fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                  | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
        + (* [comment removed for export] *)
          intros k a3' Hk Hi.
          assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
          zs. zs. zs. zs. zs. zs.
          rewrite (ret_pc_even (wfn_of f1)) by lia.
          apply evt_done. rewrite Hi. replace (0 <? zlength s - k) with true by (symmetry; apply Z.ltb_lt; lia).
          assert (SRCp : bytes_at ssegs m1 S (to_bytes (firstn (Z.to_nat (zlength s - k)) s))).
          { rewrite to_bytes_firstn. rewrite <- (firstn_skipn (Z.to_nat (zlength s - k)) (to_bytes s)) in SRC1.
            exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC1)). }
          eapply implM_bind.
          { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := firstn (Z.to_nat (zlength s - k)) s) (S := S) (lo := lo) (canary := canary)
              (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
              (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
              (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail);
              rewrite ?unsigned_lit by lia.
            all: fastfirst (first [ noevar_assumption | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRCp | exact wb_at | exact FL64
                       | f_equal; unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk sp SP63 S lo FPLO B0 BShi FIT' Shi LENW SEPS SEPB; lia)
                       | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk; lia)]]
                       | unfold zlength in *; rewrite ?length_firstn; fail | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp B s lo LO; lia)
                       | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                       | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [exfalso; unfold zlength in *; (keep_hyps f1 Fp B s k Hk L0; lia) | right; unfold zlength in *; rewrite ?length_firstn; split; fail]
                       | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia)
                       ]). }
          cbv beta. intros f2 st2 ms2 (-> & -> & PO). destruct_exs PO.
          destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
          lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
          unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
          apply implM_ret.
          replace (ret_pc (Z_to_bv 64 0x1b80c)) with (Z_to_bv 64 0x1b80c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
          assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
          { eapply (rw_cells_transport ssegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; (keep_hyps sp f1 Fp B s S lo k LO FPLO; lia)]. }
          assert (BUF2 : rw_cells ssegs m2 B [CB (Z.to_nat (f_bufsize f1)) bufbytes]).
          { eapply (rw_cells_transport ssegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo k LO SEPB FIT'; lia)]. }
          assert (SRC2 : bytes_at ssegs m2 S (to_bytes s)).
          { eapply (bytes_at_transport ssegs _ m1 m2); [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps sp f1 Fp B s S k Hk L0 lo LO SS1 SS2; lia)]. }
          assert (MU12 : munch fx_W m m2).
          { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; clear FPLO SEPS SEPB; intros; lia. }
          pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
          zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. unfold zlength in Hn. rewrite ?length_firstn in Hn. clear FPLO SEPS SEPB. rewrite ?Z.mod_small in Hn by lia. lia. }
          zs. zs. zs.
          assert (FC2' : rw_cells ssegs m2 Fp (fcells flags RP RE closefn (B + f_bufsize f1) (B + zlength (f_wbuf (f_after_write f1))) B readfn
                           (wfn_of (f_after_write f1)) seekfn B (f_bufsize f1) prev next (f_fd f1) mode1 (lbf_of (f_after_write f1)) tail)).
          { rewrite wfn_after_write, wbuf_after_write. unfold zlength; cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC2. }
          rewrite ?zbv_mod_sub.
          eapply evt_ms_eq; [eapply at_tail with (i := zlength s - k) (f2 := f_after_write f1) | first [ms_eq | match goal with |- ?g => idtac "MSEQ-LEFT:" g; fail 2 end] ];
            fastfirst (first [ noevar_assumption | exact FR2 | exact FC2' | exact BUF2 | reflexivity | split; [exact GOT2 | exact GUARD2] | exact ST2 | exact MI2 | exact MU12
                  | eapply wmono_trans; [exact WM1 | exact WM2] | exact SRC2 | apply fx_inv_after_write; exact INV01
                  | rewrite ?wbuf_after_write; unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps f1 Fp B s k Hk FIT'; lia)
                  | match goal with |- ?g => idtac "ATTAIL-LEFT:" g; fail 2 end
                  ]).
        + unfold zlength in *; lia.
        + unfold zlength in *; (keep_hyps sp f1 Fp B s lo Hz; lia).
        + unfold zlength. rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros [].
    Qed.
    End Sz30.
    Lemma cont_lbf : ltac:(let t := eval cbv delta [cont_lbf__stmt] in cont_lbf__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_lbf__body "vvvvvvvvvvvvvvv"). Qed.
  End AtM1.
End Cont.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {St : Type}.

  Lemma implM_bind_unr : forall {A B} (k : A -> M St B) (s : St) Q ms, implM ssegs (mbind munr k) s Q ms.
  Proof using Type. pin_using tt. intros. apply implM_unr. Qed.

  Lemma fx_inv_refl : forall f, f_wactive f = true -> fx_inv f f.
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. repeat split; auto. Qed.
  Lemma fx_inv_towrite : forall f, f_wactive f = false -> fx_inv f (set_w true [] (set_rbuf [] f)).
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. cbn. repeat split; auto. Qed.

  Lemma towrite_specZ : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte) (Fp : Z),
    rw_cells ssegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv ssegs m -> 0 <= Fp < 2^64 ->
    evt ssegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1b914) fc None m (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros until Fp. intros FC FL B0 BHI BS0 MI HFp.
    pose proof (towrite_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail) as T.
    rewrite !unsigned_lit in T by lia. apply T; assumption.
  Qed.

  Definition fwritex_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at ssegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITEX_DEPTH -> 0x55000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv ssegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S < 2^64 -> S + zlength s <= 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      implM ssegs (fwritex f s) st
        (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail s lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITEX) fc None m (seg_rom ssegs)).
  Section Sz35.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary : ltac2:(SecDiet.SzSec.tyM 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fwritex_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITEX, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl (fx_W sp f Fp B lo) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold fx_W in MU.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUp.
    change (bytes_at ssegs m S (to_bytes s)) with (boxed (bytes_at ssegs m S (to_bytes s))) in SRC.
    change (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof WBL as WBL'. unfold zlength in WBL', BSRC.
    unfold fwritex. unfold ensure_w.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      apply implM_retb. cbv beta.
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implM_prefix.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evt_done.
      unfold boxed in BUF, SRC.
      assert (BUF1 : rw_cells ssegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport ssegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      assert (SRC1 : bytes_at ssegs m0 S (to_bytes s)).
      { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport ssegs _ m m0); [exact SRC | exact MUp | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
      clear BUF SRC.
      lazymatch goal with |- implM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit.
      all: lazymatch goal with |- implM _ _ _ _ _ => destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf | eapply cont_fit_plain] | _ => idtac end.
        all: try exact FR.
        all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbv iota in FC; exact FC).
        all: try exact BUF1. all: try exact BUFP.
        all: fastfirst (first [ noevar_assumption | exact WACT | apply fx_inv_refl; exact WACT | reflexivity | exact CH | split; [exact GOT | exact GUARD]
                   | exact ST | exact MI | exact MU | exact WM | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF
                   | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                   | unfold zlength in *; lia | unfold FWRITEX_DEPTH; lia
                   | match goal with |- ?g => idtac "FWX-LEFT:" g; fail 2 end ]).
    - (* [comment removed for export] *)
      unfold towrite. destruct (f_nowr f) eqn:NOWR; [apply implM_bind_unr|].
      apply implM_retb. cbv beta.
      specialize (WB0 eq_refl).
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implM_prefix.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. exact (Hw eq_refl). }
      zs. zs.
      unfold boxed in BUF.
      assert (BUF1 : rw_cells ssegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport ssegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      clear BUF MUp. unfold got_ssp, ssp_guard in *.
      call towrite_specZ.
      all: lazymatch goal with |- evt _ _ _ => idtac | _ => fastfirst (first [ noevar_assumption |exact FC | exact FL8 | exact MI | lia]) end.
      rename POST into FC1. unfold file_cells in FC1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      assert (SRC1 : bytes_at ssegs m1 S (to_bytes s)).
      { unfold boxed in SRC. destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport ssegs _ m m1); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; unfold zlength in *; lia]. }
      zs. if_true. zs. zs.
      apply evt_done.
      lazymatch goal with |- implM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit with (f1 := set_w true [] (set_rbuf [] f)).
      all: lazymatch goal with |- implM _ _ _ _ _ => change (f_lbf_nl (set_w true [] (set_rbuf [] f))) with (f_lbf_nl f); destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf with (f1 := set_w true [] (set_rbuf [] f)) | eapply cont_fit_plain with (f1 := set_w true [] (set_rbuf [] f))] | _ => idtac end.
      all: try exact FR.
      all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbn [f_wbuf set_w set_rbuf f_stdoutw f_lbf_nl f_fd f_bufsize]; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC1).
      all: try exact BUF1.
      all: fastfirst (first [ noevar_assumption | reflexivity | apply fx_inv_towrite; exact WACT | exact CH | split; assumption
                 | exact MU | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF | assumption
                 | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                 | cbn [f_wbuf set_w set_rbuf]; unfold zlength in *; cbn [length Z.of_nat]; lia | unfold FWRITEX_DEPTH; lia
                 ]).
  Qed.
  End Sz35.
  Theorem fwritex_spec : ltac:(let t := eval cbv delta [fwritex_spec__stmt] in fwritex_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary. ltac2:(SecDiet.SzSec.closeP 'fwritex_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITEX : Z := 0x1bee4.
Definition FWX_TAIL : Z := 0x1bfdc.
Definition FWRITEX_DEPTH : Z := 208.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.add _ (zlength (f_wbuf _))) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (zlength _) => fail   (* [comment removed for export] *)
  | |- inr64 (zlength (firstn (Z.to_nat (Z.sub (zlength _) _)) _)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.sub (Z.add _ (f_bufsize _)) (Z.modulo (Z.add _ (zlength (f_wbuf _))) (18446744073709551616)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = y mod 2^64.
Proof. intros y. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sx32_neg : forall w : word, 2147483648 <= bv_unsigned w mod 4294967296 -> 9223372036854775808 <= bv_unsigned (sx32 w).
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hz. Qed.

(* [comment removed for export] *)
Lemma zbv_mod_sub : forall a k, (Z_to_bv 64 (a mod 18446744073709551616 - k) : word) = Z_to_bv 64 (a - k).
Proof.
  intros a k. rewrite <- (Z_to_bv_mod64 (a mod 18446744073709551616 - k)), <- (Z_to_bv_mod64 (a - k)).
  change (2^64) with 18446744073709551616. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.
Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.
Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.
Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.
Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.
Definition split_at_znth__stmt : Prop := forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Section Sz10.
Variables cs i : ltac2:(SecDiet.SzSec.tyM 'split_at_znth__stmt "vv" @cs).
#[using="Type"] Lemma split_at_znth__body : ltac2:(SecDiet.SzSec.bodyP 'split_at_znth__stmt "vv").
Proof.
  intros Hi.
 unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed.
End Sz10.
Lemma split_at_znth : ltac:(let t := eval cbv delta [split_at_znth__stmt] in split_at_znth__stmt in exact t).
Proof. intros cs i. ltac2:(SecDiet.SzSec.closeP 'split_at_znth__body "vv"). Qed.
Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite firstn_map. reflexivity. Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(Dst, Dst + N)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at usegs m' Src src.
Definition memcpy_callw__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src) -> (0 <= N < 2^64) -> (0 <= Src < 2^64) -> (0 <= Dst < 2^64) -> mem_inv usegs m ->
  evt usegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz13.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_callw__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.
End Sz13.
Lemma memcpy_callw : ltac:(let t := eval cbv delta [memcpy_callw__stmt] in memcpy_callw__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src N src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_callw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' Fp (file_cells flags rpos rend closefn wend (wpos + l) wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail)
    /\ rw_cells usegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at usegs m' S src.

Definition fwx_tail__stmt : Prop := forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells usegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail) ->
  rw_cells usegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at usegs m S src -> Z.of_nat (length src) = l ->
  stk usegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (l = 0 \/ S + l <= lo \/ bv_unsigned sp <= S) -> (l = 0 \/ S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  evt usegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bfdc) fc None m (seg_rom usegs)).
Section Sz14.
Variables x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo : ltac2:(SecDiet.SzSec.tyM 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
#[using="Type"] Lemma fwx_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  unfold file_cells in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB usegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  call memcpy_callw.
  1:{ exact SRC. }
  1:{ rewrite Nat2Z.id. reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
  rewrite !Nat2Z.id in *.
  destruct SEPS3 as [L0 | SEPS3].
  all: do 4 step.
  all: do 9 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells usegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  all: cbn [app] in DST'; rewrite !LEN in *.
  all: unfold fwx_ret_post, file_cells; sys_finish.
  all: lazymatch goal with |- bytes_at _ _ _ ?bs => destruct bs; [apply bytes_at_nil; lia | exfalso; cbn [length] in LEN; lia] end.
Qed.
End Sz14.
Lemma fwx_tail : ltac:(let t := eval cbv delta [fwx_tail__stmt] in fwx_tail__stmt in exact t).
Proof. intros x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo. ltac2:(SecDiet.SzSec.closeP 'fwx_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Scan.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (Fp wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis SRC : bytes_at usegs m S (to_bytes bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.
  Hypothesis FPR : 0 <= Fp < 2^64.

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf78) fc None m (seg_rom usegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf90) fc None m (seg_rom usegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bfb4) fc None m (seg_rom usegs)).

  Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evt usegs POST (scan_st k a3).
  Proof using BYT FD L1 LEN LHI NF SRC. pin_using (fun (BYT FD L1 LEN LHI NF SRC : unit) => tt).
    induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_to_bytes in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes usegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read usegs m S (to_bytes bs) (l - 1 - k) 1 SRC) by (rewrite ?length_to_bytes; lia).
      f_equal. unfold to_bytes. rewrite skipn_map, firstn_map. unfold znth.
      destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
      destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
      - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
      - cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
    pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
    assert (CR : 0 <= znth bs (l - 1 - k) < 256).
    { unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
    pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
    replace (l - 1 - k + 1) with (l - k) in SPL by lia.
    step.
    replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
    step.
    unfold zxb. rewrite (unsigned_lit8 _ CR).
    step. if_cases Hnl; zify_cond Hnl.
    - (* [comment removed for export] *) apply FD; [lia|].
      rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
      unfold zlength. rewrite length_firstn. lia.
    - step. step. step.
      if_cases Hend; zify_cond Hend.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
        apply (IH (k + 1)).
        { clear - Hn. lia. }
        { clear - Hk Hend. lia. }
        { replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
          rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
          replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
          cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
        replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
        apply NF.
        rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
        rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
        intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells usegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at usegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Section RetB.
  Context {St : Type}.
  Lemma implM_retb : forall {A B} (a : A) (f : A -> M St B) (s : St) Q ms,
    implM usegs (f a) s Q ms -> implM usegs (mbind (mret a) f) s Q ms.
  Proof using Type. pin_using tt. intros A B a f s Q ms H. exact H. Qed.
End RetB.

Lemma evt_ms_eq : forall P ms ms', evt usegs P ms' -> ms = ms' -> evt usegs P ms.
Proof. intros P ms ms' H ->. exact H. Qed.
Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; rewrite ?length_firstn, ?length_skipn; cbn [length Z.of_nat]; lia]).

(* [comment removed for export] *)
Definition fx_inv (f f' : file_st) : Prop :=
  f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
  /\ f_wactive f' = true /\ f_rbuf f' = (if f_wactive f then f_rbuf f else [])
  /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

Lemma wfn_after_write : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.
Lemma wbuf_after_write : forall f, f_wbuf (f_after_write f) = [].
Proof. intros f. reflexivity. Qed.
Lemma fx_inv_after_write : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (f_after_write f1).
Proof.
  unfold fx_inv, f_after_write. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct (f_stdoutw f1) eqn:E; cbn; rewrite ?E; repeat split; auto; intros HH; discriminate HH.
Qed.
Lemma fx_inv_set_w : forall f0 f1 w, fx_inv f0 f1 -> fx_inv f0 (set_w true w f1).
Proof.
  unfold fx_inv. intros f0 f1 w (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn. repeat split; auto.
Qed.
Lemma lbf_of_cases : forall f, (f_lbf_nl f = true /\ lbf_of f = 10) \/ (f_lbf_nl f = false /\ lbf_of f = 4294967295).
Proof. intros f. unfold lbf_of. destruct (f_lbf_nl f); [left|right]; split; reflexivity. Qed.

(* [comment removed for export] *)
Definition buf_split__stmt : Prop := forall m B n (wbz : list Z) (bufbytes : list byte),
  rw_cells usegs m B [CB n bufbytes] -> firstn (length wbz) bufbytes = to_bytes wbz -> (length wbz <= n)%nat ->
  rw_cells usegs m B [CB (length (to_bytes wbz)) (to_bytes wbz)]
  /\ rw_cells usegs m (B + zlength wbz) [CB (n - length wbz) (skipn (length wbz) bufbytes)].
Section Sz24.
Variables m B n wbz bufbytes : ltac2:(SecDiet.SzSec.tyM 'buf_split__stmt "vvvvv" @m).
#[using="Type"] Lemma buf_split__body : ltac2:(SecDiet.SzSec.bodyP 'buf_split__stmt "vvvvv").
Proof.
  intros BUF BUFP LE.
  assert (LBB : length bufbytes = n) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  apply (rw_cells_split_CB usegs _ _ [] n bufbytes [] [length wbz; n - length wbz]%nat) in BUF; [| cbn; lia].
  cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
  rewrite length_to_bytes. unfold zlength. split; [exact BUFa | exact BUFb].
Qed.
End Sz24.
Lemma buf_split : ltac:(let t := eval cbv delta [buf_split__stmt] in buf_split__stmt in exact t).
Proof. intros m B n wbz bufbytes. ltac2:(SecDiet.SzSec.closeP 'buf_split__body "vvvvv"). Qed.

(* [comment removed for export] *)
Definition buf_join__stmt : Prop := forall m B n (pre src rest : list byte),
  rw_cells usegs m B [CB (length pre) pre] ->
  rw_cells usegs m (B + Z.of_nat (length pre)) [CB (length src) src; CB (n - length pre - length src) rest] ->
  (length pre + length src <= n)%nat ->
  exists bb, rw_cells usegs m B [CB n bb] /\ firstn (length pre + length src) bb = pre ++ src.
Section Sz25.
Variables m B n pre src rest : ltac2:(SecDiet.SzSec.tyM 'buf_join__stmt "vvvvvv" @m).
#[using="Type"] Lemma buf_join__body : ltac2:(SecDiet.SzSec.bodyP 'buf_join__stmt "vvvvvv").
Proof.
  intros Ha Hb LE.
  pose proof (rw_cells_bound _ _ _ _ Hb) as BB.
  assert (LR : length rest = (n - length pre - length src)%nat) by (destruct Hb as [[WF _] _]; cbn in WF; exact (proj1 (proj2 WF))).
  assert (J : rw_cells usegs m B ([] ++ ([CB (length pre) pre] ++ [CB (length src) src; CB (n - length pre - length src)%nat rest]) ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact Ha|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hb. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite !app_nil_r in J.
  exists (pre ++ src ++ rest). split.
  - replace n with (length pre + (length src + (n - length pre - length src + 0)))%nat at 1 by lia. exact J.
  - rewrite app_assoc, firstn_app, length_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. rewrite length_app. lia.
Qed.
End Sz25.
Lemma buf_join : ltac:(let t := eval cbv delta [buf_join__stmt] in buf_join__stmt in exact t).
Proof. intros m B n pre src rest. ltac2:(SecDiet.SzSec.closeP 'buf_join__body "vvvvvv"). Qed.

Section Cont.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 f1 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
            (s : list Z) (S lo : Z) (canary : word) (m : mem).
  #[local] Notation wb := (f_wbuf f1) (only parsing).
  #[local] Notation bs := (f_bufsize f1) (only parsing).
  #[local] Notation l := (zlength s) (only parsing).
  #[local] Notation RP := (if f_wactive f0 then rpos else 0) (only parsing).
  #[local] Notation RE := (if f_wactive f0 then rend else 0) (only parsing).

  Definition fx_W : list (Z * Z) := [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + f_bufsize f0)].

  (* [comment removed for export] *)
  Definition fwritex_post : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch fx_W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags RP RE closefn (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells usegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Hypothesis ACT : f_wactive f1 = true.
  Hypothesis INV01 : fx_inv f0 f1.
  Hypothesis EBS : f_bufsize f1 = f_bufsize f0.
  Hypothesis EFD : f_fd f1 = f_fd f0.
  Hypothesis CH : if f_chan f1 then (f_fd f1 = 1 \/ f_fd f1 = 2) else (3 <= f_fd f1 < 2^31).
  Hypothesis LO : lo <= bv_unsigned sp - FWRITEX_DEPTH.
  Hypothesis GLO : 0x56000 <= lo.
  Hypothesis SP63 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis B0 : 0 < B.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis BS0 : 0 <= bs.
  Hypothesis WBL : zlength wb <= bs.
  Hypothesis S0 : 0 <= S < 2^64.
  Hypothesis S64 : S + l <= 2^64.
  Hypothesis Shi : l = 0 \/ S + l <= 2^47.   (* [comment removed for export] *)
  Hypothesis LENW : zlength wb + l <= 2^26.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) s.
  Hypothesis SEPS : l = 0 \/ ((S + l <= lo \/ bv_unsigned sp <= S) /\ (S + l <= Fp \/ Fp + 232 <= S) /\ (S + l <= B \/ B + bs <= S)).
  Hypothesis SEPB : (B + bs <= lo \/ bv_unsigned sp <= B) /\ (B + bs <= Fp \/ Fp + 232 <= B).
  Hypothesis FL64 : Z.land (bv_unsigned flags) F_SVB = 0.

  (* [comment removed for export] *)
  Definition at40c (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) a0 (Z_to_bv 64 (B + bs)) a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 S) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf18) fc None m1 (seg_rom usegs).

  (* [comment removed for export] *)
  Definition at_tail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word) (j8 : list byte) (mode2 : word) (bufbytes2 : list byte) (m2 : mem) (f2 : file_st) (i : Z),
    rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m2 Fp (fcells flags RP RE closefn (B + bs) (B + zlength (f_wbuf f2)) B readfn (wfn_of f2) seekfn B bs prev next (f_fd f1) mode2 (lbf_of f2) tail) ->
    rw_cells usegs m2 B [CB (Z.to_nat bs) bufbytes2] -> firstn (length (f_wbuf f2)) bufbytes2 = to_bytes (f_wbuf f2) ->
    ssp_cells m2 canary -> stk usegs m2 lo (bv_unsigned sp + -64) -> mem_inv usegs m2 -> munch fx_W m m2 -> wmono usegs m m2 ->
    bytes_at usegs m2 S (to_bytes s) ->
    fx_inv f0 f2 -> 0 <= i <= l -> zlength (f_wbuf f2) + (l - i) <= bs ->
    evt usegs (fwritex_post (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2) st)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 (l - i)) (Z_to_bv 64 (B + zlength (f_wbuf f2)))
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (S + i)) (Z_to_bv 64 i) x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bfdc) fc None m2 (seg_rom usegs)).
  Section Sz26.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i : ltac2:(SecDiet.SzSec.tyM 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma at_tail__body : ltac2:(SecDiet.SzSec.bodyP 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL : unit) => tt).
 intros FR2 FC2 BUF2 BUFP2 SSP2 ST2 MI2 MU2 WM2 SRC2 INV2 IR FIT.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP2 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC2) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC2) as BSRC. rewrite length_to_bytes in BSRC.
    assert (BS2 : f_bufsize f2 = f_bufsize f1) by (destruct INV01 as (_&_&E1&_); destruct INV2 as (_&_&E2&_); congruence).
    pose proof FIT as FIT'. unfold zlength in FIT', WBL, IR, BSRC |- .
    destruct (buf_split m2 B (Z.to_nat (f_bufsize f1)) (f_wbuf f2) bufbytes2 BUF2 BUFP2 ltac:(lia)) as [BUFa BUFb].
    (* [comment removed for export] *)
    assert (XS : exists S', (Z_to_bv 64 (S + i) : word) = Z_to_bv 64 S' /\ 0 <= S' < 2^64
              /\ bytes_at usegs m2 S' (to_bytes (skipn (Z.to_nat i) s))
              /\ (S' = S + i \/ (S' = 0 /\ i = Z.of_nat (length s)))).
    { destruct (Z.eq_dec (S + i) (2^64)) as [WRAP|NOWRAP].
      - exists 0. split; [rewrite WRAP; rewrite <- (Z_to_bv_mod64 (2^64)); reflexivity|]. split; [lia|].
        split; [| right; lia]. replace (skipn (Z.to_nat i) s) with (@nil Z) by (symmetry; apply skipn_all2; lia).
        apply bytes_at_nil. lia.
      - exists (S + i). split; [reflexivity|]. split; [lia|]. split; [| left; reflexivity].
        rewrite to_bytes_skipn. replace (S + i) with (S + Z.of_nat (Z.to_nat i)) by lia. apply bytes_at_skipn; [exact SRC2 | rewrite length_to_bytes; lia]. }
    destruct XS as (S' & ES' & HS' & SRCi & S'c). rewrite ES'.
    unfold fcells in FC2.
    eapply evt_mono.
    { eapply fwx_tail with (lo := lo) (m0 := m2) (i := i) (src := to_bytes (skipn (Z.to_nat i) s)) (S := S') (l := Z.of_nat (length s) - i)
         (cap := (Z.to_nat (f_bufsize f1) - length (f_wbuf f2))%nat) (junk := skipn (length (f_wbuf f2)) bufbytes2) (wpos := B + zlength (f_wbuf f2));
        fastfirst (first [ noevar_assumption | exact FR2 | exact FC2 | unfold zlength; exact BUFb | exact SRCi | exact ST2 | exact MI2 | apply wmono_refl | apply munch_refl
              | rewrite ?length_to_bytes, ?length_skipn; unfold zlength in *; (keep_hyps f1 Fp s f2 i FIT' IR sp lo LO GLO SP63 B B0 BShi SEPB S S' SEPS S'c LENW HS'; lia)
              | destruct SEPB as [SB1 SB2]; unfold zlength in *; fail
              | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps f1 Fp B s f2 i S' IR L0 sp lo; lia)
              ]). }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3).
    lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
    rewrite length_to_bytes, length_skipn in DST3.
    unfold zlength in MU3, FC3, DST3, BUFa.
    assert (GOT3 : rw_cells usegs m3 142816 [C8 (Z_to_bv 64 345288)]).
    { eapply (rw_cells_transport usegs _ m2 m3); [exact GOT | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP1 BSEP1 FIT'; lia)]. }
    assert (GUARD3 : rw_cells usegs m3 345288 [C8 canary]).
    { eapply (rw_cells_transport usegs _ m2 m3); [exact GUARD | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP2 BSEP2 FIT'; lia)]. }
    assert (BUFa3 : rw_cells usegs m3 B [CB (length (to_bytes (f_wbuf f2))) (to_bytes (f_wbuf f2))]).
    { eapply (rw_cells_transport usegs _ m2 m3); [exact BUFa | exact MU3 | exact WM3 | cbn; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo f2 i SEPB IR FIT'; lia)]. }
    rewrite length_to_bytes in BUFa3.
    destruct (buf_join m3 B (Z.to_nat (f_bufsize f1)) (to_bytes (f_wbuf f2)) (to_bytes (skipn (Z.to_nat i) s))
                (skipn (length s - Z.to_nat i) (skipn (length (f_wbuf f2)) bufbytes2))) as [bb [BUF3 BUFP3]].
    { rewrite length_to_bytes. exact BUFa3. }
    { rewrite !length_to_bytes, length_skipn. exact DST3. }
    { rewrite !length_to_bytes, length_skipn. lia. }
    replace (i + (Z.of_nat (length s) - i)) with (Z.of_nat (length s)) by lia.
    unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_set_w; exact INV2|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [apply (munch_trans _ m m2 m3); [exact MU2 | eapply munch_weaken; [| exact MU3]; unfold sub_fp, fx_W; cbn [outside]; intros; (keep_hyps sp f0 f1 Fp B s lo f2 i x14 EBS FIT' H; lia)]|].
    split; [eapply wmono_trans; [exact WM2 | exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split.
    { cbn [f_wbuf set_w]. change (wfn_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (wfn_of f2).
      change (lbf_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (lbf_of f2).
      unfold fcells, zlength. rewrite length_app, length_skipn.
      replace (B + Z.of_nat (length (f_wbuf f2) + (length s - Z.to_nat i))) with (B + Z.of_nat (length (f_wbuf f2)) + (Z.of_nat (length s) - i)) by lia.
      exact FC3. }
    split; [exact BUF3|].
    split; [cbn [f_wbuf set_w]; rewrite to_bytes_app, length_app, <- (length_to_bytes (f_wbuf f2)), <- (length_to_bytes (skipn _ s)); exact BUFP3|].
    split; [cbn [f_wbuf set_w]; unfold zlength; rewrite length_app, length_skipn; lia|].
    split; [exact GOT3 | exact GUARD3].
  Qed.
  End Sz26.
  Lemma at_tail : ltac:(let t := eval cbv delta [at_tail__stmt] in at_tail__stmt in exact t).
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i. ltac2:(SecDiet.SzSec.closeP 'at_tail__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Section AtM1.
    Variables (j8 : list byte) (mode1 : word) (bufbytes : list byte) (m1 : mem).
    Hypothesis FR1 : rw_cells usegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FC1 : rw_cells usegs m1 Fp (fcells flags RP RE closefn (B + bs) (B + zlength wb) B readfn (wfn_of f1) seekfn B bs prev next (f_fd f1) mode1 (lbf_of f1) tail).
    Hypothesis BUF1 : rw_cells usegs m1 B [CB (Z.to_nat bs) bufbytes].
    Hypothesis BUFP : firstn (length wb) bufbytes = to_bytes wb.
    Hypothesis SSP1 : ssp_cells m1 canary.
    Hypothesis ST1 : stk usegs m1 lo (bv_unsigned sp + -64).
    Hypothesis MI1 : mem_inv usegs m1.
    Hypothesis MU1 : munch fx_W m m1.
    Hypothesis WM1 : wmono usegs m m1.
    Hypothesis SRC1 : bytes_at usegs m1 S (to_bytes s).

    Lemma wb_at : bytes_at usegs m1 B (to_bytes wb).
    Proof using BUF1 BUFP. pin_using (fun (BUF1 BUFP : unit) => tt). eapply CB_prefix_bytes_at; [exact BUF1|]. rewrite length_to_bytes. exact BUFP. Qed.

    (* [comment removed for export] *)
    Definition cont_nofit__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      bs - zlength wb < l ->
      implM usegs (file_writefn f1 s) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz28.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_nofit__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_nofit__body : ltac2:(SecDiet.SzSec.bodyP 'cont_nofit__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 : unit) => tt).
 intros NOFIT. unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fx_W in MU1.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
      unfold zlength in *.
      apply implM_prefix.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
      do 13 zs.
      rewrite (ret_pc_even (wfn_of f1)) by lia.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evt_done.
      eapply implM_post_evt.
      { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
          (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail).
        all: fastfirst (first [ noevar_assumption | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRC1 | exact wb_at | exact FL64
                   | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; (keep_hyps f1 Fp B s BS0 Hr; lia)]]
                   | unfold zlength in *; (keep_hyps f1 Fp B s B0 BShi WBL sp S lo Shi Hr LENW SEPS SEPB; lia) | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp s lo LO; lia)
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                   | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [left; destruct s; [reflexivity | exfalso; unfold zlength in L0; cbn [length] in L0; (keep_hyps f1 Fp z l L0; lia)] | right; unfold zlength in *; split; fail]
                   | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia) ]). }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2.
      pose proof (rw_cells_transport usegs _ m1 m2 _ _ BUF1 MU2 WM2 ltac:(destruct SEPB as [SB1 SB2]; cbn; (keep_hyps sp f1 Fp B s lo LO BS0 SEPB; lia))) as BUF2.
      apply evt_done. unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_after_write; exact INV01|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { apply (munch_trans _ m m1 m2).
        * exact MU1.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W, FWRITEX_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [rewrite wfn_after_write, wbuf_after_write; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC2|].
      split; [exact BUF2|]. split; [reflexivity|]. split; [rewrite wbuf_after_write; unfold zlength in *; cbn; lia | exact SSP2].
    Qed.
    End Sz28.
    Lemma cont_nofit : ltac:(let t := eval cbv delta [cont_nofit__stmt] in cont_nofit__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_nofit__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_fit_plain__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = false ->
      implM usegs (mret (set_w true (wb ++ s) f1)) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz29.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_fit_plain__body : ltac2:(SecDiet.SzSec.bodyP 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 : unit) => tt).
 intros FIT LBF. unfold at40c. apply implM_ret.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 4294967295) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. zs. zs.
      pose proof (sx32_neg (Z_to_bv 64 4294967295) ltac:(vm_compute; discriminate)) as NEG.
      if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      change (skipn (Z.to_nat 0) s) with s in |- *.
      replace s with (skipn (Z.to_nat 0) s) at 1 by reflexivity.
      replace (Z_to_bv 64 (zlength s) : word) with (Z_to_bv 64 (zlength s - 0) : word) by (f_equal; lia).
      replace (Z_to_bv 64 S : word) with (Z_to_bv 64 (S + 0) : word) by (f_equal; lia).
      eapply at_tail; fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01 | unfold zlength in *; lia ]).
    Qed.
    End Sz29.
    Lemma cont_fit_plain : ltac:(let t := eval cbv delta [cont_fit_plain__stmt] in cont_fit_plain__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_fit_plain__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_lbf__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = true ->
      implM usegs (f2 <- (if 0 <? after_last_nl s then file_writefn f1 (firstn (Z.to_nat (after_last_nl s)) s) else mret f1) ;;
                   mret (set_w true (f_wbuf f2 ++ skipn (Z.to_nat (after_last_nl s)) s) f2))
            st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz30.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_lbf__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_lbf__body : ltac2:(SecDiet.SzSec.bodyP 'cont_lbf__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 : unit) => tt).
 intros FIT LBF. unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 10) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      pose proof (after_last_nl_range s) as IR. unfold zlength in IR.
      apply implM_prefix.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. rewrite (sx32_small 10) by lia. zs. zs.
      if_cases Hl; zify_cond Hl. 1:{ exfalso. lia. }
      zs. if_cases Hz; zify_cond Hz.
      - (* [comment removed for export] *)
        assert (NL0 : after_last_nl s = 0) by (unfold zlength in *; rewrite ?Z.mod_small in Hz by lia; lia).
        rewrite NL0. cbn [Z.ltb Z.to_nat].
        apply evt_done. apply implM_retb. apply implM_ret.
        eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
          fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
      - (* [comment removed for export] *)
        zs. zs. zs. zs.
        eapply evt_ms_eq; [ eapply scan_loop with (k := 0) (n := Z.to_nat (zlength s)) (bs := s) | ms_eq ].
        + exact SRC1.
        + reflexivity.
        + exact BYT.
        + unfold zlength in *; lia.
        + unfold zlength in *; lia.
        + (* [comment removed for export] *)
          intros a3' NL0. zs. zs.
          apply evt_done. rewrite NL0. cbn [Z.ltb Z.to_nat]. apply implM_retb. apply implM_ret.
          change (skipn 0 s) with (skipn (Z.to_nat 0) s).
          eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
            fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                  | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
        + (* [comment removed for export] *)
          intros k a3' Hk Hi.
          assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
          zs. zs. zs. zs. zs. zs.
          rewrite (ret_pc_even (wfn_of f1)) by lia.
          apply evt_done. rewrite Hi. replace (0 <? zlength s - k) with true by (symmetry; apply Z.ltb_lt; lia).
          assert (SRCp : bytes_at usegs m1 S (to_bytes (firstn (Z.to_nat (zlength s - k)) s))).
          { rewrite to_bytes_firstn. rewrite <- (firstn_skipn (Z.to_nat (zlength s - k)) (to_bytes s)) in SRC1.
            exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC1)). }
          eapply implM_bind.
          { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := firstn (Z.to_nat (zlength s - k)) s) (S := S) (lo := lo) (canary := canary)
              (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
              (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
              (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail);
              rewrite ?unsigned_lit by lia.
            all: fastfirst (first [ noevar_assumption | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRCp | exact wb_at | exact FL64
                       | f_equal; unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk sp SP63 S lo FPLO B0 BShi FIT' Shi LENW SEPS SEPB; lia)
                       | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk; lia)]]
                       | unfold zlength in *; rewrite ?length_firstn; fail | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp B s lo LO; lia)
                       | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                       | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [exfalso; unfold zlength in *; (keep_hyps f1 Fp B s k Hk L0; lia) | right; unfold zlength in *; rewrite ?length_firstn; split; fail]
                       | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia)
                       ]). }
          cbv beta. intros f2 st2 ms2 (-> & -> & PO). destruct_exs PO.
          destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
          lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
          unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
          apply implM_ret.
          replace (ret_pc (Z_to_bv 64 0x1bfcc)) with (Z_to_bv 64 0x1bfcc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
          assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
          { eapply (rw_cells_transport usegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; (keep_hyps sp f1 Fp B s S lo k LO FPLO; lia)]. }
          assert (BUF2 : rw_cells usegs m2 B [CB (Z.to_nat (f_bufsize f1)) bufbytes]).
          { eapply (rw_cells_transport usegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo k LO SEPB FIT'; lia)]. }
          assert (SRC2 : bytes_at usegs m2 S (to_bytes s)).
          { eapply (bytes_at_transport usegs _ m1 m2); [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps sp f1 Fp B s S k Hk L0 lo LO SS1 SS2; lia)]. }
          assert (MU12 : munch fx_W m m2).
          { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; clear FPLO SEPS SEPB; intros; lia. }
          pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
          zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. unfold zlength in Hn. rewrite ?length_firstn in Hn. clear FPLO SEPS SEPB. rewrite ?Z.mod_small in Hn by lia. lia. }
          zs. zs. zs.
          assert (FC2' : rw_cells usegs m2 Fp (fcells flags RP RE closefn (B + f_bufsize f1) (B + zlength (f_wbuf (f_after_write f1))) B readfn
                           (wfn_of (f_after_write f1)) seekfn B (f_bufsize f1) prev next (f_fd f1) mode1 (lbf_of (f_after_write f1)) tail)).
          { rewrite wfn_after_write, wbuf_after_write. unfold zlength; cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC2. }
          rewrite ?zbv_mod_sub.
          eapply evt_ms_eq; [eapply at_tail with (i := zlength s - k) (f2 := f_after_write f1) | ms_eq];
            fastfirst (first [ noevar_assumption | exact FR2 | exact FC2' | exact BUF2 | reflexivity | split; [exact GOT2 | exact GUARD2] | exact ST2 | exact MI2 | exact MU12
                  | eapply wmono_trans; [exact WM1 | exact WM2] | exact SRC2 | apply fx_inv_after_write; exact INV01
                  | rewrite ?wbuf_after_write; unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps f1 Fp B s k Hk FIT'; lia)
                  ]).
        + unfold zlength in *; lia.
        + unfold zlength in *; (keep_hyps sp f1 Fp B s lo Hz; lia).
        + unfold zlength. rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros [].
    Qed.
    End Sz30.
    Lemma cont_lbf : ltac:(let t := eval cbv delta [cont_lbf__stmt] in cont_lbf__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_lbf__body "vvvvvvvvvvvvvvv"). Qed.
  End AtM1.
End Cont.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {St : Type}.

  Lemma implM_bind_unr : forall {A B} (k : A -> M St B) (s : St) Q ms, implM usegs (mbind munr k) s Q ms.
  Proof using Type. pin_using tt. intros. apply implM_unr. Qed.

  Lemma fx_inv_refl : forall f, f_wactive f = true -> fx_inv f f.
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. repeat split; auto. Qed.
  Lemma fx_inv_towrite : forall f, f_wactive f = false -> fx_inv f (set_w true [] (set_rbuf [] f)).
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. cbn. repeat split; auto. Qed.

  Lemma towrite_specZ : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte) (Fp : Z),
    rw_cells usegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv usegs m -> 0 <= Fp < 2^64 ->
    evt usegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1c0d4) fc None m (seg_rom usegs)).
  Proof using Type. pin_using tt.
    intros until Fp. intros FC FL B0 BHI BS0 MI HFp.
    pose proof (towrite_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail) as T.
    rewrite !unsigned_lit in T by lia. apply T; assumption.
  Qed.

  Definition fwritex_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at usegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITEX_DEPTH -> 0x56000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv usegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S < 2^64 -> S + zlength s <= 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      implM usegs (fwritex f s) st
        (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail s lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITEX) fc None m (seg_rom usegs)).
  Section Sz35.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary : ltac2:(SecDiet.SzSec.tyM 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fwritex_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC BUF BUFP WB0 SRC BYT -> -> -> CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITEX, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl (fx_W sp f Fp B lo) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold fx_W in MU.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUp.
    change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
    change (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof WBL as WBL'. unfold zlength in WBL', BSRC.
    unfold fwritex. unfold ensure_w.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      apply implM_retb. cbv beta.
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implM_prefix.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evt_done.
      unfold boxed in BUF, SRC.
      assert (BUF1 : rw_cells usegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport usegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      assert (SRC1 : bytes_at usegs m0 S (to_bytes s)).
      { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport usegs _ m m0); [exact SRC | exact MUp | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
      clear BUF SRC.
      lazymatch goal with |- implM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit.
      all: lazymatch goal with |- implM _ _ _ _ _ => destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf | eapply cont_fit_plain] | _ => idtac end.
        all: try exact FR.
        all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbv iota in FC; exact FC).
        all: try exact BUF1. all: try exact BUFP.
        all: fastfirst (first [ noevar_assumption | exact WACT | apply fx_inv_refl; exact WACT | reflexivity | exact CH | split; [exact GOT | exact GUARD]
                   | exact ST | exact MI | exact MU | exact WM | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF
                   | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                   | unfold zlength in *; lia | unfold FWRITEX_DEPTH; lia ]).
    - (* [comment removed for export] *)
      unfold towrite. destruct (f_nowr f) eqn:NOWR; [apply implM_bind_unr|].
      apply implM_retb. cbv beta.
      specialize (WB0 eq_refl).
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implM_prefix.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. exact (Hw eq_refl). }
      zs. zs.
      unfold boxed in BUF.
      assert (BUF1 : rw_cells usegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport usegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      clear BUF MUp. unfold got_ssp, ssp_guard in *.
      call towrite_specZ.
      all: lazymatch goal with |- evt _ _ _ => idtac | _ => fastfirst (first [ noevar_assumption |exact FC | exact FL8 | exact MI | lia]) end.
      rename POST into FC1. unfold file_cells in FC1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      assert (SRC1 : bytes_at usegs m1 S (to_bytes s)).
      { unfold boxed in SRC. destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport usegs _ m m1); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; unfold zlength in *; lia]. }
      zs. if_true. zs. zs.
      apply evt_done.
      lazymatch goal with |- implM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit with (f1 := set_w true [] (set_rbuf [] f)).
      all: lazymatch goal with |- implM _ _ _ _ _ => change (f_lbf_nl (set_w true [] (set_rbuf [] f))) with (f_lbf_nl f); destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf with (f1 := set_w true [] (set_rbuf [] f)) | eapply cont_fit_plain with (f1 := set_w true [] (set_rbuf [] f))] | _ => idtac end.
      all: try exact FR.
      all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbn [f_wbuf set_w set_rbuf f_stdoutw f_lbf_nl f_fd f_bufsize]; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC1).
      all: try exact BUF1.
      all: fastfirst (first [ noevar_assumption | reflexivity | apply fx_inv_towrite; exact WACT | exact CH | split; assumption
                 | exact MU | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF | assumption
                 | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                 | cbn [f_wbuf set_w set_rbuf]; unfold zlength in *; cbn [length Z.of_nat]; lia | unfold FWRITEX_DEPTH; lia
                 ]).
  Qed.
  End Sz35.
  Theorem fwritex_spec : ltac:(let t := eval cbv delta [fwritex_spec__stmt] in fwritex_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary. ltac2:(SecDiet.SzSec.closeP 'fwritex_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.
End TwB.
End F_fwritex.

(* [comment removed for export] *)
Module F_fwrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITE : Z := 0x1b85c.
Definition FWRITE_DEPTH : Z := 272.   (* [comment removed for export] *)

Lemma lock_word_neg : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295)).
Proof. vm_compute. discriminate. Qed.

Lemma fwrite_retval : forall size nmemb, 0 <= size < 2^64 -> 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (size <? 1) + -1) mod 18446744073709551616) nmemb = (if size =? 0 then 0 else nmemb).
Proof.
  intros size nmemb Hs Hn. destruct (Z.eqb_spec size 0).
  - subst. reflexivity.
  - replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f0 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
      (r : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch (fx_W sp f0 Fp B lo) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags (if f_wactive f0 then rpos else 0) (if f_wactive f0 then rend else 0) closefn
                                 (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells ssegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Definition fwrite_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S size nmemb lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at ssegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 nmemb -> a3 = Z_to_bv 64 Fp ->
      0 <= size < 2^64 -> 0 <= nmemb < 2^64 -> size * nmemb = zlength s ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_DEPTH -> 0x55000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv ssegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S -> S + zlength s < 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      implM ssegs (fwrite_file f s) st
        (fwrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail
                     (if size =? 0 then 0 else nmemb) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom ssegs)).
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary : ltac2:(SecDiet.SzSec.tyM 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fwrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> -> SZ NM SN CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITE, FWRITE_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    change (bytes_at ssegs m S (to_bytes s)) with (boxed (bytes_at ssegs m S (to_bytes s))) in SRC.
    change (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof FC as FC0. lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    unfold fcells, file_cells in FC.
    unfold fwrite_file.
    apply implM_prefix.
    carve_frame 64%nat ST.
    do 11 zs. zs. zs. zs.
    if_cases Hk; zify_cond Hk. 2:{ exfalso. pose proof lock_word_neg. lia. }
    zs. zs. zs.
    apply evt_done.
    unfold boxed in BUF, SRC, FC0.
    assert (BUF1 : rw_cells ssegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
    { eapply (rw_cells_transport ssegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    assert (SRC1 : bytes_at ssegs m0 S (to_bytes s)).
    { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
      - unfold boxed in SRC. pose proof (bytes_at_bound _ _ _ _ SRC) as BSx. destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
      - eapply (bytes_at_transport ssegs _ m m0); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
    assert (FC1 : rw_cells ssegs m0 Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport ssegs _ m m0); [exact FC0 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold fcells; rewrite file_cells_size; lia]. }
    clear BUF SRC FC0 FC.
    eapply implM_post_evt.
    { eapply (fwritex_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (readfn := readfn)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode) (tail := tail) (bufbytes := bufbytes);
        rewrite ?unsigned_lit by lia.
      all: fastfirst (first [ noevar_assumption | reflexivity | exact FC1 | exact BUF1 | exact BUFP | exact WB0 | exact SRC1 | exact BYT | exact CH | exact ST | exact MI
                 | split; [exact GOT | exact GUARD] | exact FL64 | exact FL8
                 | f_equal; lia
                 | unfold FWRITEX_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                 | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [left; exact L0 | right; unfold zlength in *; repeat split; lia]
                 | destruct SEPB as [SB1 SB2]; split; lia
                 | lia
                 ]). }
    cbv beta. intros f' st' ms' (-> & INV & PO). destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & BUF2 & BUFP2 & WBL2 & [GOT2 GUARD2]).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold fx_W in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x1b8e4)) with (Z_to_bv 64 0x1b8e4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport ssegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    clear FR.
    zs. zs. if_cases He; zify_cond He. 2:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in He by lia. lia. }
    zs. zs. zs.
    rewrite fwrite_retval by lia.
    zs. do 9 zs.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold fwrite_post. split; [reflexivity|]. split; [exact INV|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (munch_trans _ m m0 m2).
      * eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]; intros; lia.
      * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact FC2|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact WBL2|]. split; [exact GOT2 | exact GUARD2].
  Qed.
  End Sz3.
  Theorem fwrite_spec : ltac:(let t := eval cbv delta [fwrite_spec__stmt] in fwrite_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary. ltac2:(SecDiet.SzSec.closeP 'fwrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fwrite.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITE : Z := 0x1c01c.
Definition FWRITE_DEPTH : Z := 272.   (* [comment removed for export] *)

Lemma lock_word_neg : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295)).
Proof. vm_compute. discriminate. Qed.

Lemma fwrite_retval : forall size nmemb, 0 <= size < 2^64 -> 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (size <? 1) + -1) mod 18446744073709551616) nmemb = (if size =? 0 then 0 else nmemb).
Proof.
  intros size nmemb Hs Hn. destruct (Z.eqb_spec size 0).
  - subst. reflexivity.
  - replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f0 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
      (r : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (fx_W sp f0 Fp B lo) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags (if f_wactive f0 then rpos else 0) (if f_wactive f0 then rend else 0) closefn
                                 (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells usegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Definition fwrite_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S size nmemb lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at usegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 nmemb -> a3 = Z_to_bv 64 Fp ->
      0 <= size < 2^64 -> 0 <= nmemb < 2^64 -> size * nmemb = zlength s ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_DEPTH -> 0x56000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv usegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S -> S + zlength s < 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      implM usegs (fwrite_file f s) st
        (fwrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail
                     (if size =? 0 then 0 else nmemb) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom usegs)).
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary : ltac2:(SecDiet.SzSec.tyM 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fwrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC BUF BUFP WB0 SRC BYT -> -> -> -> SZ NM SN CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITE, FWRITE_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
    change (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof FC as FC0. lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    unfold fcells, file_cells in FC.
    unfold fwrite_file.
    apply implM_prefix.
    carve_frame 64%nat ST.
    do 11 zs. zs. zs. zs.
    if_cases Hk; zify_cond Hk. 2:{ exfalso. pose proof lock_word_neg. lia. }
    zs. zs. zs.
    apply evt_done.
    unfold boxed in BUF, SRC, FC0.
    assert (BUF1 : rw_cells usegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
    { eapply (rw_cells_transport usegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    assert (SRC1 : bytes_at usegs m0 S (to_bytes s)).
    { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
      - unfold boxed in SRC. pose proof (bytes_at_bound _ _ _ _ SRC) as BSx. destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
      - eapply (bytes_at_transport usegs _ m m0); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
    assert (FC1 : rw_cells usegs m0 Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport usegs _ m m0); [exact FC0 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold fcells; rewrite file_cells_size; lia]. }
    clear BUF SRC FC0 FC.
    eapply implM_post_evt.
    { eapply (fwritex_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (readfn := readfn)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode) (tail := tail) (bufbytes := bufbytes);
        rewrite ?unsigned_lit by lia.
      all: fastfirst (first [ noevar_assumption | reflexivity | exact FC1 | exact BUF1 | exact BUFP | exact WB0 | exact SRC1 | exact BYT | exact CH | exact ST | exact MI
                 | split; [exact GOT | exact GUARD] | exact FL64 | exact FL8
                 | f_equal; lia
                 | unfold FWRITEX_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                 | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [left; exact L0 | right; unfold zlength in *; repeat split; lia]
                 | destruct SEPB as [SB1 SB2]; split; lia
                 | lia
                 ]). }
    cbv beta. intros f' st' ms' (-> & INV & PO). destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & BUF2 & BUFP2 & WBL2 & [GOT2 GUARD2]).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold fx_W in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x1c0a4)) with (Z_to_bv 64 0x1c0a4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport usegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    clear FR.
    zs. zs. if_cases He; zify_cond He. 2:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in He by lia. lia. }
    zs. zs. zs.
    rewrite fwrite_retval by lia.
    zs. do 9 zs.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold fwrite_post. split; [reflexivity|]. split; [exact INV|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (munch_trans _ m m0 m2).
      * eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]; intros; lia.
      * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact FC2|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact WBL2|]. split; [exact GOT2 | exact GUARD2].
  Qed.
  End Sz3.
  Theorem fwrite_spec : ltac:(let t := eval cbv delta [fwrite_spec__stmt] in fwrite_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary. ltac2:(SecDiet.SzSec.closeP 'fwrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fwrite.
End TwB.
End F_fwrite.

(* [comment removed for export] *)
Module F_fread.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.add (Z.b2z (Z.ltb _ _)) (-1)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (Z.opp (1)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD : Z := 0x1b5e8.
Definition FREAD_LOOP : Z := 0x1b688.
Definition FREAD_DEPTH : Z := 224.   (* [comment removed for export] *)

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
  Context {St : Type}.

  Lemma implM_retb : forall {A B} (a : A) (k : A -> M St B) (s : St) Q ms,
    implM ssegs (k a) s Q ms -> implM ssegs (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B a k s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Definition fr_inv (f0 f : file_st) : Prop :=
    f_fd f = f_fd f0 /\ f_chan f = f_chan f0 /\ f_bufsize f = f_bufsize f0 /\ f_nord f = f_nord f0 /\ f_nowr f = f_nowr f0
    /\ f_wactive f = false /\ f_wbuf f = [].

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Definition fr_W : list (Z * Z) := [(bv_unsigned sp - FREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + n)].

  Definition fread_post : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fr_inv f0 (snd r) /\ Z.of_nat (length (fst r)) <= n /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (rp' : Z) (bufbytes' rest' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch fr_W m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 F_STDIO_READ (wfn_of (snd r)) seekfn B bs prev next (f_fd f0) mode' (lbf_of (snd r)) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells ssegs m' B [CB (Z.to_nat bs) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + bs
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells ssegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat n - length (fst r)) rest']
      /\ ssp_cells m' canary.

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x55000 <= lo.
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
  Lemma fread_loop_spec : forall fuel (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fcur : file_st) (flags1 mode1 : word) (rp1 : Z)
      (bufbytes1 rest : list byte) (acc : list Z) (off l : Z) (m1 : mem),
    rw_cells ssegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ssegs m1 Fp (fcells flags1 rp1 rp1 closefn 0 0 0 F_STDIO_READ (wfn_of fcur) seekfn B bs prev next (f_fd f0) mode1 (lbf_of fcur) tail) ->
    flags_ok fcur flags1 -> fr_inv f0 fcur -> f_rbuf fcur = [] -> 0 <= rp1 < 2^63 ->
    rw_cells ssegs m1 B [CB (Z.to_nat bs) bufbytes1] ->
    rw_cells ssegs m1 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest] -> off = zlength acc -> off + l = n -> 1 <= l ->
    Forall (fun z => 0 <= z < 256) acc ->
    ssp_cells m1 canary -> stk ssegs m1 lo (bv_unsigned sp + -64) -> mem_inv ssegs m1 ->
    munch fr_W m m1 -> wmono ssegs m m1 ->
    implM ssegs (fread_loop fuel fcur B (D + off) l acc) st fread_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 (D + off)) (Z_to_bv 64 l) (Z_to_bv 64 1) (Z_to_bv 64 n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREAD_LOOP) fc None m1 (seg_rom ssegs)).
  Proof using B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 : unit) => tt).
    induction fuel as [|fuel IH]; intros until m1; intros FR1 FC1 FL1 INV1 RB1 RP1 BUF1 DST1 OFF OL L1 FACC SSP1 ST1 MI1 MU1 WM1.
    { cbn [fread_loop]. apply implM_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_LOOP, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    destruct INV1 as (Ifd & Ich & Ibs & Ind & Inw & Iwa & Iwb).
    pose proof (rw_cells_bound _ _ _ _ DST1) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
    assert (LACC : length (to_bytes acc) = length acc) by apply length_to_bytes.
    unfold zlength in OFF.
    cbn [fread_loop]. replace (l <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    eapply implM_bind.
    { pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fr_W, FREAD_DEPTH in MU1.
      apply implM_prefix. zs. zs.
      apply evt_done.
      eapply (toread_spec (St:=St)) with (f := fcur) (Fp := Fp) (flags := flags1) (rpos := rp1) (rend := rp1) (closefn := closefn) (readfn := F_STDIO_READ)
        (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode1) (tail := tail) (bufbytes := bufbytes1) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; rewrite ?Iwa, ?Ibs, ?Ifd, ?Iwb, ?Ich.
      all: [> (noevar_assumption) | (exact (proj1 FL1)) | (exact (proj1 (proj2 (proj2 FL1)))) | (exact (proj1 (proj2 (proj2 (proj2 (proj2 FL1)))))) | (noevar_assumption) | (reflexivity) | (reflexivity) | (noevar_assumption) | (reflexivity) | (rewrite NCH; exact FD) | (noevar_assumption) | (unfold TOREAD_DEPTH; lia) | (noevar_assumption) | (unfold TOREAD_DEPTH; lia) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (noevar_assumption) | (noevar_assumption) | (unfold TOREAD_DEPTH; lia) | (unfold zlength; cbn [length Z.of_nat]; lia) | (unfold TOREAD_DEPTH; lia) | (unfold TOREAD_DEPTH; lia) ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [fst snd] in He, TRI. destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold tr_W, TOREAD_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x1b690)) with (Z_to_bv 64 0x1b690 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof TRI as TRI'. destruct TRI as (Tfd & Tch & Tbs & Tnd & Tnw & Teof & Twa & Twb & Trb & _).
    assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport ssegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BUF2 : rw_cells ssegs m2 B [CB (Z.to_nat (f_bufsize f0)) bufbytes1]).
    { eapply (rw_cells_transport ssegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (DST2 : rw_cells ssegs m2 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest]).
    { eapply (rw_cells_transport ssegs _ m1 m2); [exact DST1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (MU12 : munch fr_W m m2).
    { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fr_W, FREAD_DEPTH; cbn [outside]; intros; lia. }
    assert (WM12 : wmono ssegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    assert (FL2 : flags_ok f2 flags1) by (unfold flags_ok in *; rewrite ?Tch, Tnd, Tnw, Teof; first [exact FL1 | rewrite <- ?Tch; exact FL1]).
    clear FR1 BUF1 DST1 MU2 WM2 MI1 ST1.
    pose proof FC2 as FC. unfold fcells, file_cells in FC.
    destruct SSP2 as [GOT2 GUARD2].
    cbn [fst snd] in *. subst e.
    apply implM_prefix.
    destruct (f_eof fcur) eqn:EOF.
    - (* [comment removed for export] *)
      cbn [Z.b2z Z.opp]. zs. if_cases Hx; zify_cond Hx. 2:{ exfalso. vm_compute in Hx. lia. }
      apply evt_done. apply implM_retb. apply implM_ret.
      zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
      zs. zs. rewrite divu_one. do 10 zs.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. cbn [fst snd].
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
      apply evt_done. cbv beta.
      (* [comment removed for export] *)
      pose proof DST2 as DSTa. apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in DSTa. destruct DSTa as [DSTa DSTb].
      cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r, ?LACC in DSTb.
      replace (D + Z.of_nat (length acc)) with (D + off) in DSTb by lia.
      eapply implM_bind.
      { eapply (stdio_read_spec (St:=St)) with (f := f2) (Fp := Fp) (flags := flags1) (rp := B + f_bufsize fcur) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := _) (tail := tail) (bufbytes := bufbytes1) (D := D + off) (len := l) (djunk := rest)
          (lo := lo) (canary := canary);
          rewrite ?unsigned_lit by lia; rewrite ?Tfd, ?Tch, ?Tbs, ?Ifd, ?Ich, ?Ibs.
        all: [> (unfold fcells, file_cells; rewrite <- ?Ibs, <- ?Ifd; exact FC) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (reflexivity) | (reflexivity) | (reflexivity) | (noevar_assumption) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (split; [exact GOT2 | exact GUARD2]) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (noevar_assumption) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) ]. }
      cbv beta. intros [bsr f3] st3 ms3 (-> & RDI & BL & RBE & GF3 & GRB3 & PO). cbn [fst snd] in RDI, BL, RBE, PO |- *. destruct_exs PO.
      destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & FL3 & BUF3 & RREL3 & RP3 & RP3' & DST3 & SSP3).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      unfold rd_W, STDIO_READ_DEPTH in MU3. rewrite !unsigned_lit in MU3, ST3 by lia.
      replace (ret_pc (Z_to_bv 64 0x1b6a8)) with (Z_to_bv 64 0x1b6a8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RDI as (Rfd & Rch & Rbs & Rnd & Rnw & Rwa & Rwb & Rsw & Rlbf & Reof).
      rewrite <- (wfn_of_rd f2 f3 Rsw), <- (lbf_of_rd f2 f3 Rlbf) in FC3. rewrite Tbs, Tfd in FC3. rewrite Tbs in BUF3, RREL3.
      rewrite ?Ibs, ?Ifd in FC3. rewrite ?Ibs in BUF3. rewrite ?Ibs in RREL3.
      assert (FR3 : rw_cells ssegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport ssegs _ m2 m3); [exact FR2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (DSTa3 : rw_cells ssegs m3 D [CB (length acc) (to_bytes acc)]).
      { eapply (rw_cells_transport ssegs _ m2 m3); [exact DSTa | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (MU13 : munch fr_W m m3).
      { apply (munch_trans _ m m2 m3); [exact MU12|]. eapply munch_weaken; [| exact MU3].
        unfold fr_W, FREAD_DEPTH. intros a. cbn [outside fst snd]. clear - Tbs Ibs OFF OL L1 SPHI LO. intros Ha. lia. }
      assert (WM13 : wmono ssegs m m3) by (eapply wmono_trans; [exact WM12 | exact WM3]).
      destruct SSP3 as [GOT3 GUARD3].
      assert (FRI3 : fr_inv f0 f3) by (unfold fr_inv; repeat split; congruence).
      pose proof (bytes_at_bound _ _ _ _ (rw_cells_bytes_at _ _ _ _ DST3)) as BB3. cbn [cells_bytes cbytes] in BB3.
      rewrite ?length_app, ?length_to_bytes, ?length_skipn in BB3.
      (* [comment removed for export] *)
      assert (DJ : rw_cells ssegs m3 D [CB (length (acc ++ bsr)) (to_bytes (acc ++ bsr)); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]).
      { pose proof (proj2 (rw_cells_app ssegs m3 D [CB (length acc) (to_bytes acc)] [CB (length bsr) (to_bytes bsr); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)])) as J.
        cbn [cells_size csize Nat.add] in J. rewrite ?Nat.add_0_r in J. replace (D + Z.of_nat (length acc)) with (D + off) in J by lia.
        specialize (J (conj DSTa3 DST3)).
        apply (rw_cells_merge ssegs m3 D [] [CB (length acc) (to_bytes acc); CB (length bsr) (to_bytes bsr)] [CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]) in J.
        cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J.
        rewrite length_app, to_bytes_app'. exact J. }
      clear DSTa DST3 FC DST2 BUF2 MU3 WM3.
      pose proof FC3 as FC. unfold fcells, file_cells in FC.
      apply implM_prefix. zs.
      destruct bsr as [|c0 bsr'].
      + (* [comment removed for export] *)
        if_cases Hz; zify_cond Hz. 2:{ exfalso. unfold zlength in Hz. cbn [length Z.of_nat] in Hz. rewrite ?Z.mod_small in Hz by lia. lia. }
        zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
        zs. zs. rewrite divu_one. do 10 zs.
        release_frame FR3 ST3 (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
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
          apply evt_done.
          assert (RB3 : f_rbuf f3 = []) by (apply RBE; unfold zlength in *; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia).
          rewrite RB3 in FC3. unfold zlength in FC3. cbn [length Z.of_nat] in FC3. rewrite Z.add_0_r in FC3.
          replace (D + off + Z.of_nat (S (length bsr'))) with (D + (off + Z.of_nat (S (length bsr')))) by lia.
          eapply implM_at_eq; [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f3 x29 x14 x30 x31 (skipn (S (length bsr')) rest) (acc ++ c0 :: bsr') (off + Z.of_nat (S (length bsr'))) (l - Z.of_nat (S (length bsr'))) m3) | cbv delta [mkR]; reflexivity];
            fastfirst (first [ noevar_assumption | exact FR3 | exact FC3 | exact FL3 | exact FRI3 | exact RB3 | exact BUF3 | split; [exact GOT3 | exact GUARD3] | exact ST3 | exact MI3 | exact MU13 | exact WM13 | solve [frange]
                  | replace (Z.to_nat (l - Z.of_nat (S (length bsr')))) with (Z.to_nat l - S (length bsr'))%nat by lia; exact DJ
                  | unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia
                  ]).
        * (* [comment removed for export] *)
          zs. zs. zs. rewrite retval_size1 by lia. zs. if_true. do 10 zs.
          release_frame FR3 ST3 (bv_unsigned sp).
          apply evt_done.
          destruct fuel as [|fuel']; [apply implM_unr|].
          cbn [fread_loop]. replace (l - Z.of_nat (S (length bsr')) <=? 0) with true by (symmetry; apply Z.leb_le; lia).
          apply implM_ret. apply evt_done.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD : Z := 0x1bda8.
Definition FREAD_LOOP : Z := 0x1be48.
Definition FREAD_DEPTH : Z := 224.   (* [comment removed for export] *)

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
  Context {St : Type}.

  Lemma implM_retb : forall {A B} (a : A) (k : A -> M St B) (s : St) Q ms,
    implM usegs (k a) s Q ms -> implM usegs (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B a k s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Definition fr_inv (f0 f : file_st) : Prop :=
    f_fd f = f_fd f0 /\ f_chan f = f_chan f0 /\ f_bufsize f = f_bufsize f0 /\ f_nord f = f_nord f0 /\ f_nowr f = f_nowr f0
    /\ f_wactive f = false /\ f_wbuf f = [].

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Definition fr_W : list (Z * Z) := [(bv_unsigned sp - FREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + n)].

  Definition fread_post : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fr_inv f0 (snd r) /\ Z.of_nat (length (fst r)) <= n /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (rp' : Z) (bufbytes' rest' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch fr_W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 F_STDIO_READ (wfn_of (snd r)) seekfn B bs prev next (f_fd f0) mode' (lbf_of (snd r)) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells usegs m' B [CB (Z.to_nat bs) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + bs
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells usegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat n - length (fst r)) rest']
      /\ ssp_cells m' canary.

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x56000 <= lo.
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
  Lemma fread_loop_spec : forall fuel (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fcur : file_st) (flags1 mode1 : word) (rp1 : Z)
      (bufbytes1 rest : list byte) (acc : list Z) (off l : Z) (m1 : mem),
    rw_cells usegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m1 Fp (fcells flags1 rp1 rp1 closefn 0 0 0 F_STDIO_READ (wfn_of fcur) seekfn B bs prev next (f_fd f0) mode1 (lbf_of fcur) tail) ->
    flags_ok fcur flags1 -> fr_inv f0 fcur -> f_rbuf fcur = [] -> 0 <= rp1 < 2^63 ->
    rw_cells usegs m1 B [CB (Z.to_nat bs) bufbytes1] ->
    rw_cells usegs m1 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest] -> off = zlength acc -> off + l = n -> 1 <= l ->
    Forall (fun z => 0 <= z < 256) acc ->
    ssp_cells m1 canary -> stk usegs m1 lo (bv_unsigned sp + -64) -> mem_inv usegs m1 ->
    munch fr_W m m1 -> wmono usegs m m1 ->
    implM usegs (fread_loop fuel fcur B (D + off) l acc) st fread_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 (D + off)) (Z_to_bv 64 l) (Z_to_bv 64 1) (Z_to_bv 64 n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREAD_LOOP) fc None m1 (seg_rom usegs)).
  Proof using B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 : unit) => tt).
    induction fuel as [|fuel IH]; intros until m1; intros FR1 FC1 FL1 INV1 RB1 RP1 BUF1 DST1 OFF OL L1 FACC SSP1 ST1 MI1 MU1 WM1.
    { cbn [fread_loop]. apply implM_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_LOOP, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    destruct INV1 as (Ifd & Ich & Ibs & Ind & Inw & Iwa & Iwb).
    pose proof (rw_cells_bound _ _ _ _ DST1) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
    assert (LACC : length (to_bytes acc) = length acc) by apply length_to_bytes.
    unfold zlength in OFF.
    cbn [fread_loop]. replace (l <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    eapply implM_bind.
    { pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fr_W, FREAD_DEPTH in MU1.
      apply implM_prefix. zs. zs.
      apply evt_done.
      eapply (toread_spec (St:=St)) with (f := fcur) (Fp := Fp) (flags := flags1) (rpos := rp1) (rend := rp1) (closefn := closefn) (readfn := F_STDIO_READ)
        (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode1) (tail := tail) (bufbytes := bufbytes1) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; rewrite ?Iwa, ?Ibs, ?Ifd, ?Iwb, ?Ich.
      all: [> (noevar_assumption) | (exact (proj1 FL1)) | (exact (proj1 (proj2 (proj2 FL1)))) | (exact (proj1 (proj2 (proj2 (proj2 (proj2 FL1)))))) | (noevar_assumption) | (reflexivity) | (reflexivity) | (noevar_assumption) | (reflexivity) | (rewrite NCH; exact FD) | (noevar_assumption) | (unfold TOREAD_DEPTH; lia) | (noevar_assumption) | (unfold TOREAD_DEPTH; lia) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (noevar_assumption) | (noevar_assumption) | (unfold TOREAD_DEPTH; lia) | (unfold zlength; cbn [length Z.of_nat]; lia) | (unfold TOREAD_DEPTH; lia) | (unfold TOREAD_DEPTH; lia) ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [fst snd] in He, TRI. destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold tr_W, TOREAD_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x1be50)) with (Z_to_bv 64 0x1be50 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof TRI as TRI'. destruct TRI as (Tfd & Tch & Tbs & Tnd & Tnw & Teof & Twa & Twb & Trb & _).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport usegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BUF2 : rw_cells usegs m2 B [CB (Z.to_nat (f_bufsize f0)) bufbytes1]).
    { eapply (rw_cells_transport usegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (DST2 : rw_cells usegs m2 D [CB (length acc) (to_bytes acc); CB (Z.to_nat l) rest]).
    { eapply (rw_cells_transport usegs _ m1 m2); [exact DST1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (MU12 : munch fr_W m m2).
    { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fr_W, FREAD_DEPTH; cbn [outside]; intros; lia. }
    assert (WM12 : wmono usegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    assert (FL2 : flags_ok f2 flags1) by (unfold flags_ok in *; rewrite ?Tch, Tnd, Tnw, Teof; first [exact FL1 | rewrite <- ?Tch; exact FL1]).
    clear FR1 BUF1 DST1 MU2 WM2 MI1 ST1.
    pose proof FC2 as FC. unfold fcells, file_cells in FC.
    destruct SSP2 as [GOT2 GUARD2].
    cbn [fst snd] in *. subst e.
    apply implM_prefix.
    destruct (f_eof fcur) eqn:EOF.
    - (* [comment removed for export] *)
      cbn [Z.b2z Z.opp]. zs. if_cases Hx; zify_cond Hx. 2:{ exfalso. vm_compute in Hx. lia. }
      apply evt_done. apply implM_retb. apply implM_ret.
      zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
      zs. zs. rewrite divu_one. do 10 zs.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. cbn [fst snd].
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
      apply evt_done. cbv beta.
      (* [comment removed for export] *)
      pose proof DST2 as DSTa. apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in DSTa. destruct DSTa as [DSTa DSTb].
      cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r, ?LACC in DSTb.
      replace (D + Z.of_nat (length acc)) with (D + off) in DSTb by lia.
      eapply implM_bind.
      { eapply (stdio_read_spec (St:=St)) with (f := f2) (Fp := Fp) (flags := flags1) (rp := B + f_bufsize fcur) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := _) (tail := tail) (bufbytes := bufbytes1) (D := D + off) (len := l) (djunk := rest)
          (lo := lo) (canary := canary);
          rewrite ?unsigned_lit by lia; rewrite ?Tfd, ?Tch, ?Tbs, ?Ifd, ?Ich, ?Ibs.
        all: [> (unfold fcells, file_cells; rewrite <- ?Ibs, <- ?Ifd; exact FC) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (reflexivity) | (reflexivity) | (reflexivity) | (noevar_assumption) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (split; [exact GOT2 | exact GUARD2]) | (noevar_assumption) | (noevar_assumption) | (noevar_assumption) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (unfold got_ssp, ssp_guard; lia) | (noevar_assumption) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) | (noevar_assumption) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) | (unfold STDIO_READ_DEPTH; lia) ]. }
      cbv beta. intros [bsr f3] st3 ms3 (-> & RDI & BL & RBE & GF3 & GRB3 & PO). cbn [fst snd] in RDI, BL, RBE, PO |- *. destruct_exs PO.
      destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & FL3 & BUF3 & RREL3 & RP3 & RP3' & DST3 & SSP3).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      unfold rd_W, STDIO_READ_DEPTH in MU3. rewrite !unsigned_lit in MU3, ST3 by lia.
      replace (ret_pc (Z_to_bv 64 0x1be68)) with (Z_to_bv 64 0x1be68 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RDI as (Rfd & Rch & Rbs & Rnd & Rnw & Rwa & Rwb & Rsw & Rlbf & Reof).
      rewrite <- (wfn_of_rd f2 f3 Rsw), <- (lbf_of_rd f2 f3 Rlbf) in FC3. rewrite Tbs, Tfd in FC3. rewrite Tbs in BUF3, RREL3.
      rewrite ?Ibs, ?Ifd in FC3. rewrite ?Ibs in BUF3. rewrite ?Ibs in RREL3.
      assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport usegs _ m2 m3); [exact FR2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (DSTa3 : rw_cells usegs m3 D [CB (length acc) (to_bytes acc)]).
      { eapply (rw_cells_transport usegs _ m2 m3); [exact DSTa | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (MU13 : munch fr_W m m3).
      { apply (munch_trans _ m m2 m3); [exact MU12|]. eapply munch_weaken; [| exact MU3].
        unfold fr_W, FREAD_DEPTH. intros a. cbn [outside fst snd]. clear - Tbs Ibs OFF OL L1 SPHI LO. intros Ha. lia. }
      assert (WM13 : wmono usegs m m3) by (eapply wmono_trans; [exact WM12 | exact WM3]).
      destruct SSP3 as [GOT3 GUARD3].
      assert (FRI3 : fr_inv f0 f3) by (unfold fr_inv; repeat split; congruence).
      pose proof (bytes_at_bound _ _ _ _ (rw_cells_bytes_at _ _ _ _ DST3)) as BB3. cbn [cells_bytes cbytes] in BB3.
      rewrite ?length_app, ?length_to_bytes, ?length_skipn in BB3.
      (* [comment removed for export] *)
      assert (DJ : rw_cells usegs m3 D [CB (length (acc ++ bsr)) (to_bytes (acc ++ bsr)); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]).
      { pose proof (proj2 (rw_cells_app usegs m3 D [CB (length acc) (to_bytes acc)] [CB (length bsr) (to_bytes bsr); CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)])) as J.
        cbn [cells_size csize Nat.add] in J. rewrite ?Nat.add_0_r in J. replace (D + Z.of_nat (length acc)) with (D + off) in J by lia.
        specialize (J (conj DSTa3 DST3)).
        apply (rw_cells_merge usegs m3 D [] [CB (length acc) (to_bytes acc); CB (length bsr) (to_bytes bsr)] [CB (Z.to_nat l - length bsr) (skipn (length bsr) rest)]) in J.
        cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J.
        rewrite length_app, to_bytes_app'. exact J. }
      clear DSTa DST3 FC DST2 BUF2 MU3 WM3.
      pose proof FC3 as FC. unfold fcells, file_cells in FC.
      apply implM_prefix. zs.
      destruct bsr as [|c0 bsr'].
      + (* [comment removed for export] *)
        if_cases Hz; zify_cond Hz. 2:{ exfalso. unfold zlength in Hz. cbn [length Z.of_nat] in Hz. rewrite ?Z.mod_small in Hz by lia. lia. }
        zs. if_cases Hy; zify_cond Hy. 2:{ exfalso. lia. }
        zs. zs. rewrite divu_one. do 10 zs.
        release_frame FR3 ST3 (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
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
          apply evt_done.
          assert (RB3 : f_rbuf f3 = []) by (apply RBE; unfold zlength in *; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia).
          rewrite RB3 in FC3. unfold zlength in FC3. cbn [length Z.of_nat] in FC3. rewrite Z.add_0_r in FC3.
          replace (D + off + Z.of_nat (S (length bsr'))) with (D + (off + Z.of_nat (S (length bsr')))) by lia.
          eapply implM_at_eq; [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f3 x29 x14 x30 x31 (skipn (S (length bsr')) rest) (acc ++ c0 :: bsr') (off + Z.of_nat (S (length bsr'))) (l - Z.of_nat (S (length bsr'))) m3) | cbv delta [mkR]; reflexivity];
            fastfirst (first [ noevar_assumption | exact FR3 | exact FC3 | exact FL3 | exact FRI3 | exact RB3 | exact BUF3 | split; [exact GOT3 | exact GUARD3] | exact ST3 | exact MI3 | exact MU13 | exact WM13 | solve [frange]
                  | replace (Z.to_nat (l - Z.of_nat (S (length bsr')))) with (Z.to_nat l - S (length bsr'))%nat by lia; exact DJ
                  | unfold zlength in *; rewrite ?length_app; cbn [length] in *; rewrite ?Z.mod_small in Hl by lia; lia
                  ]).
        * (* [comment removed for export] *)
          zs. zs. zs. rewrite retval_size1 by lia. zs. if_true. do 10 zs.
          release_frame FR3 ST3 (bv_unsigned sp).
          apply evt_done.
          destruct fuel as [|fuel']; [apply implM_unr|].
          cbn [fread_loop]. replace (l - Z.of_nat (S (length bsr')) <=? 0) with true by (symmetry; apply Z.leb_le; lia).
          apply implM_ret. apply evt_done.
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
Module F_fread_misc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD' : Z := 0x1b5e8.

Lemma retval_size1' : forall nmemb, 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) nmemb = nmemb.
Proof.
  intros nmemb Hn. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rw_cells_nil0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells ssegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. repeat split; reflexivity.
  - cbn. apply bytes_at_nil. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Definition memcpy_call0__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src : Z),
  (0 <= Src < 2^64) -> (0 <= Dst < 2^64) -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ssegs)
               /\ munch [] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src : ltac2:(SecDiet.SzSec.tyM 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_call0__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros HS HD MI.
  eapply evt_mono.
  { eapply (memcpy_callw ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src 0 [] []);
      [apply bytes_at_nil; lia | reflexivity | apply rw_cells_nil0; lia | lia | lia | exact HS | exact HD | exact MI]. }
  cbv beta. intros ms' PO. unfold memcpy_postv in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & _).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [| split; [exact WM| exact MI']].
  intros xw _. apply MU. cbn. lia.
Qed.
End Sz3.
Lemma memcpy_call0 : ltac:(let t := eval cbv delta [memcpy_call0__stmt] in memcpy_call0__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src. ltac2:(SecDiet.SzSec.closeP 'memcpy_call0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Section FreadMisc.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis LO : lo <= bv_unsigned sp - 224.
  Hypothesis GLO : 0x55000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fread_zero_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp wend wpos wbase wfn fd lbf D Dm : Z),
      rw_cells ssegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode lbf tail) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      0 <= wend < 2^64 -> 0 <= wpos < 2^64 -> 0 <= wbase < 2^64 -> 0 <= wfn < 2^64 -> 0 <= fd < 2^64 -> 0 <= lbf < 2^64 ->
      0 <= B -> B + bs < 2^64 -> 0 <= bs ->
      0 <= D < 2^64 ->
      stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
      implM ssegs (fread_file f0 B Dm 0) st
        (fun r st' ms' => st' = st /\ r = ([], set_rbuf (f_rbuf f0) f0) /\
           exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
             ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom ssegs)
             /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
             /\ stk ssegs m' lo (bv_unsigned sp)
             /\ rw_cells ssegs m' Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom ssegs)).
  Section Sz4.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm : ltac2:(SecDiet.SzSec.tyM 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_zero_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO Fp0 LO SP47. pin_using (fun (FPLO Fp0 LO SP47 : unit) => tt).
    intros FC RP0 RPHI W1 W2 W3 W4 W5 W6 B0 BHI BS0 HD ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fcells, file_cells in FC.
    (* [comment removed for export] *)
    unfold fread_file. rewrite Z.min_r by (unfold zlength; lia). cbn [Z.to_nat firstn skipn fread_loop Z.sub Z.leb].
    rewrite Z.add_0_r.
    apply implM_ret.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    assert (CASES : f_rbuf f0 = [] \/ f_rbuf f0 <> []) by (destruct (f_rbuf f0); [left; reflexivity | right; discriminate]).
    destruct CASES as [RB | RB].
    - (* [comment removed for export] *)
      rewrite RB in *. unfold zlength in *. cbn [length Z.of_nat] in *. rewrite Z.add_0_r in FC |- *.
      if_true.
      zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
      zs. zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      unfold fcells, file_cells. cbn [length Z.of_nat]. rewrite ?Z.add_0_r. exact FC.
    - (* [comment removed for export] *)
      assert (NB1 : 1 <= zlength (f_rbuf f0)) by (destruct (f_rbuf f0); [exfalso; exact (RB eq_refl) | unfold zlength; cbn; lia]).
      unfold zlength in *.
      if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. rewrite ?Z.mul_1_r. zs.
      replace (rp + Z.of_nat (length (f_rbuf f0)) - rp) with (Z.of_nat (length (f_rbuf f0))) by lia.
      if_cases Hc; zify_cond Hc. 1:{ exfalso. rewrite ?Z.mod_small in Hc by lia. lia. }
      zs. zs. zs. zs.
      call memcpy_call0.
      1:{ lia. } 1:{ exact HD. } 1:{ exact MI. }
      zs. zs. zs. rewrite ?Z.add_0_r. zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
      zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv _ _ |- _ => exact H end|]. split; [exact ST|].
      unfold fcells, file_cells. exact FC.
  Qed.
  End Sz4.
  Theorem fread_zero_spec : ltac:(let t := eval cbv delta [fread_zero_spec__stmt] in fread_zero_spec__stmt in exact t).
  Proof using FPLO Fp0 LO SP47. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm. ltac2:(SecDiet.SzSec.closeP 'fread_zero_spec__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis B0' : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.

  Definition fread_nord_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp D n : Z) (bufbytes : list byte),
      rw_cells ssegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn
                             (if f_wactive f0 then B + f_bufsize f0 else 0) (if f_wactive f0 then B + zlength (f_wbuf f0) else 0) (if f_wactive f0 then B else 0)
                             F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f0 then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f0 then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells ssegs m B [CB (Z.to_nat bs) bufbytes] -> firstn (length (f_wbuf f0)) bufbytes = to_bytes (f_wbuf f0) ->
      (f_wactive f0 = false -> f_wbuf f0 = []) -> zlength (f_wbuf f0) <= bs ->
      f_rbuf f0 = [] -> f_nord f0 = true ->
      0 <= rp -> rp < 2^63 ->
      0 < n < 2^63 ->
      stk ssegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv ssegs m ->
      implM ssegs (fread_file f0 B D n) st (fun _ _ _ => False)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom ssegs)).
  Section Sz5.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes : ltac2:(SecDiet.SzSec.tyM 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_nord_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47. pin_using (fun (B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 : unit) => tt).
    intros FC FLN FLE FL64 BUF BUFP WB0 WBL RB NORD RP0 RPHI HN ST SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    assert (WFR : 0 <= wfn_of f0 < 2^64) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f0); cbn; lia).
    assert (LBR : 0 <= lbf_of f0 < 2^64) by (unfold lbf_of; destruct (f_lbf_nl f0); cbn; lia).
    pose proof WBL as WBL'. unfold zlength in WBL'.
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    change (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes]) with (boxed (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes])) in BUF.
    lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    (* [comment removed for export] *)
    unfold fread_file. rewrite RB. unfold zlength at 1 2 3. cbn [length Z.of_nat Z.to_nat firstn skipn]. rewrite Z.min_l by lia.
    rewrite Z.add_0_r, Z.sub_0_r.
    replace (S (Z.to_nat n)) with (S (Z.to_nat n)) by reflexivity. cbn [fread_loop].
    replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite RB in FC. unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
    apply implM_prefix.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    if_true.
    zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 2:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
    zs. zs.
    apply evt_done.
    unfold boxed in BUF, FC0.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (BUF1 : rw_cells ssegs m1 B [CB (Z.to_nat (f_bufsize f0)) bufbytes]).
    { eapply (rw_cells_transport ssegs _ m m1); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    eapply implM_bind.
    { eapply (toread_spec (St:=St)) with (f := set_rbuf [] f0) (Fp := Fp) (flags := flags) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := canary);
        cbn [f_wactive f_bufsize f_wbuf f_fd f_nord f_eof f_chan f_rbuf set_rbuf f_stdoutw f_lbf_nl wfn_of lbf_of];
        rewrite ?unsigned_lit by lia.
      all: first [ reflexivity | exact FLN | exact FLE | exact FL64 | exact BUF1 | exact BUFP | exact WB0 | exact MI
                 | rewrite NCH; exact FD
                 | unfold ssp_cells, got_ssp, ssp_guard; split; assumption
                 | unfold TOREAD_DEPTH; lia
                 | lia
                 | match goal with |- rw_cells _ _ Fp _ => unfold fcells, file_cells; cbn [wfn_of lbf_of] in FC |- *; exact FC end
                 | assumption
                 | match goal with |- ?g => idtac "NORDLEFT:" g end ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [f_nord set_rbuf] in NRDf. rewrite NORD in NRDf. discriminate NRDf.
  Qed.
  End Sz5.
  Theorem fread_nord_spec : ltac:(let t := eval cbv delta [fread_nord_spec__stmt] in fread_nord_spec__stmt in exact t).
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes. ltac2:(SecDiet.SzSec.closeP 'fread_nord_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End FreadMisc.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD' : Z := 0x1bda8.

Lemma retval_size1' : forall nmemb, 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) nmemb = nmemb.
Proof.
  intros nmemb Hn. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rw_cells_nil0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells usegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. repeat split; reflexivity.
  - cbn. apply bytes_at_nil. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Definition memcpy_call0__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src : Z),
  (0 <= Src < 2^64) -> (0 <= Dst < 2^64) -> mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src : ltac2:(SecDiet.SzSec.tyM 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_call0__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros HS HD MI.
  eapply evt_mono.
  { eapply (memcpy_callw ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src 0 [] []);
      [apply bytes_at_nil; lia | reflexivity | apply rw_cells_nil0; lia | lia | lia | exact HS | exact HD | exact MI]. }
  cbv beta. intros ms' PO. unfold memcpy_postv in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & _).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [| split; [exact WM| exact MI']].
  intros xw _. apply MU. cbn. lia.
Qed.
End Sz3.
Lemma memcpy_call0 : ltac:(let t := eval cbv delta [memcpy_call0__stmt] in memcpy_call0__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src. ltac2:(SecDiet.SzSec.closeP 'memcpy_call0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Section FreadMisc.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis LO : lo <= bv_unsigned sp - 224.
  Hypothesis GLO : 0x56000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fread_zero_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp wend wpos wbase wfn fd lbf D Dm : Z),
      rw_cells usegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode lbf tail) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      0 <= wend < 2^64 -> 0 <= wpos < 2^64 -> 0 <= wbase < 2^64 -> 0 <= wfn < 2^64 -> 0 <= fd < 2^64 -> 0 <= lbf < 2^64 ->
      0 <= B -> B + bs < 2^64 -> 0 <= bs ->
      0 <= D < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
      implM usegs (fread_file f0 B Dm 0) st
        (fun r st' ms' => st' = st /\ r = ([], set_rbuf (f_rbuf f0) f0) /\
           exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
             ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom usegs)
             /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
             /\ stk usegs m' lo (bv_unsigned sp)
             /\ rw_cells usegs m' Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom usegs)).
  Section Sz4.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm : ltac2:(SecDiet.SzSec.tyM 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_zero_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO Fp0 LO SP47. pin_using (fun (FPLO Fp0 LO SP47 : unit) => tt).
 intros FC RP0 RPHI W1 W2 W3 W4 W5 W6 B0 BHI BS0 HD ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fcells, file_cells in FC.
    (* [comment removed for export] *)
    unfold fread_file. rewrite Z.min_r by (unfold zlength; lia). cbn [Z.to_nat firstn skipn fread_loop Z.sub Z.leb].
    rewrite Z.add_0_r.
    apply implM_ret.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    assert (CASES : f_rbuf f0 = [] \/ f_rbuf f0 <> []) by (destruct (f_rbuf f0); [left; reflexivity | right; discriminate]).
    destruct CASES as [RB | RB].
    - (* [comment removed for export] *)
      rewrite RB in *. unfold zlength in *. cbn [length Z.of_nat] in *. rewrite Z.add_0_r in FC |- *.
      if_true.
      zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
      zs. zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      unfold fcells, file_cells. cbn [length Z.of_nat]. rewrite ?Z.add_0_r. exact FC.
    - (* [comment removed for export] *)
      assert (NB1 : 1 <= zlength (f_rbuf f0)) by (destruct (f_rbuf f0); [exfalso; exact (RB eq_refl) | unfold zlength; cbn; lia]).
      unfold zlength in *.
      if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. rewrite ?Z.mul_1_r. zs.
      replace (rp + Z.of_nat (length (f_rbuf f0)) - rp) with (Z.of_nat (length (f_rbuf f0))) by lia.
      if_cases Hc; zify_cond Hc. 1:{ exfalso. rewrite ?Z.mod_small in Hc by lia. lia. }
      zs. zs. zs. zs.
      call memcpy_call0.
      1:{ lia. } 1:{ exact HD. } 1:{ exact MI. }
      zs. zs. zs. rewrite ?Z.add_0_r. zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
      zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv _ _ |- _ => exact H end|]. split; [exact ST|].
      unfold fcells, file_cells. exact FC.
  Qed.
  End Sz4.
  Theorem fread_zero_spec : ltac:(let t := eval cbv delta [fread_zero_spec__stmt] in fread_zero_spec__stmt in exact t).
  Proof using FPLO Fp0 LO SP47. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm. ltac2:(SecDiet.SzSec.closeP 'fread_zero_spec__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis B0' : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.

  Definition fread_nord_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp D n : Z) (bufbytes : list byte),
      rw_cells usegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn
                             (if f_wactive f0 then B + f_bufsize f0 else 0) (if f_wactive f0 then B + zlength (f_wbuf f0) else 0) (if f_wactive f0 then B else 0)
                             F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f0 then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f0 then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells usegs m B [CB (Z.to_nat bs) bufbytes] -> firstn (length (f_wbuf f0)) bufbytes = to_bytes (f_wbuf f0) ->
      (f_wactive f0 = false -> f_wbuf f0 = []) -> zlength (f_wbuf f0) <= bs ->
      f_rbuf f0 = [] -> f_nord f0 = true ->
      0 <= rp -> rp < 2^63 ->
      0 < n < 2^63 ->
      stk usegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (fread_file f0 B D n) st (fun _ _ _ => False)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom usegs)).
  Section Sz5.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes : ltac2:(SecDiet.SzSec.tyM 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_nord_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47. pin_using (fun (B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 : unit) => tt).
 intros FC FLN FLE FL64 BUF BUFP WB0 WBL RB NORD RP0 RPHI HN ST SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    assert (WFR : 0 <= wfn_of f0 < 2^64) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f0); cbn; lia).
    assert (LBR : 0 <= lbf_of f0 < 2^64) by (unfold lbf_of; destruct (f_lbf_nl f0); cbn; lia).
    pose proof WBL as WBL'. unfold zlength in WBL'.
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    change (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes]) with (boxed (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes])) in BUF.
    lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    (* [comment removed for export] *)
    unfold fread_file. rewrite RB. unfold zlength at 1 2 3. cbn [length Z.of_nat Z.to_nat firstn skipn]. rewrite Z.min_l by lia.
    rewrite Z.add_0_r, Z.sub_0_r.
    replace (S (Z.to_nat n)) with (S (Z.to_nat n)) by reflexivity. cbn [fread_loop].
    replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite RB in FC. unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
    apply implM_prefix.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    if_true.
    zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 2:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
    zs. zs.
    apply evt_done.
    unfold boxed in BUF, FC0.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (BUF1 : rw_cells usegs m1 B [CB (Z.to_nat (f_bufsize f0)) bufbytes]).
    { eapply (rw_cells_transport usegs _ m m1); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    eapply implM_bind.
    { eapply (toread_spec (St:=St)) with (f := set_rbuf [] f0) (Fp := Fp) (flags := flags) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := canary);
        cbn [f_wactive f_bufsize f_wbuf f_fd f_nord f_eof f_chan f_rbuf set_rbuf f_stdoutw f_lbf_nl wfn_of lbf_of];
        rewrite ?unsigned_lit by lia.
      all: first [ reflexivity | exact FLN | exact FLE | exact FL64 | exact BUF1 | exact BUFP | exact WB0 | exact MI
                 | rewrite NCH; exact FD
                 | unfold ssp_cells, got_ssp, ssp_guard; split; assumption
                 | unfold TOREAD_DEPTH; lia
                 | lia
                 | match goal with |- rw_cells _ _ Fp _ => unfold fcells, file_cells; cbn [wfn_of lbf_of] in FC |- *; exact FC end
                 | assumption
                 | match goal with |- ?g => idtac "NORDLEFT:" g end ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [f_nord set_rbuf] in NRDf. rewrite NORD in NRDf. discriminate NRDf.
  Qed.
  End Sz5.
  Theorem fread_nord_spec : ltac:(let t := eval cbv delta [fread_nord_spec__stmt] in fread_nord_spec__stmt in exact t).
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes. ltac2:(SecDiet.SzSec.closeP 'fread_nord_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End FreadMisc.
End TwB.
End F_fread_misc.

(* [comment removed for export] *)
Module F_fread_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rw_cells_CB0' : forall m A n bs, rw_cells ssegs m A [CB n bs] -> rw_cells ssegs m A [CB n bs; CB 0 []].
Proof.
  intros m A n bs [[W B] R]. split; [split|].
  - cbn in *. repeat split; try reflexivity. exact (proj1 W).
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact B.
  - cbn [cells_size csize Nat.add] in *. rewrite Nat.add_0_r in *. exact R.
Qed.

Section FreadMain.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x55000 <= lo.
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
  Definition fread_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp : Z) (bufbytes djunk : list byte),
      rw_cells ssegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      flags_ok f0 flags ->
      rw_cells ssegs m B [CB (Z.to_nat bs) bufbytes] ->
      (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs /\ firstn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes) = to_bytes (f_rbuf f0)) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      rw_cells ssegs m D [CB (Z.to_nat n) djunk] ->
      f_wactive f0 = false -> f_wbuf f0 = [] -> Forall (fun z => 0 <= z < 256) (f_rbuf f0) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Fp ->
      stk ssegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv ssegs m ->
      implM ssegs (fread_file f0 B D n) st (fread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD) fc None m (seg_rom ssegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk : ltac2:(SecDiet.SzSec.tyM 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 : unit) => tt).
    intros FC FL BUF RREL RP0 RPHI DST WACT WB0 RBR -> -> -> -> ST SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (fr_W sp f0 Fp B D n) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold fr_W, FREAD_DEPTH in MU.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    unfold fread_file. cbv zeta.
    apply implM_prefix.
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
        apply evt_done.
        replace (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B D n []) with (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B (D + 0) n [] : M St (list Z * file_st)) by (rewrite Z.add_0_r; reflexivity).
        eapply implM_at_eq; [eapply (fread_loop_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf [] f0) flags _ rp bufbytes djunk [] 0 n)
                            | cbv delta [mkR]; rewrite Z.add_0_r; reflexivity];
          first [ exact FR | exact FC | exact FL | exact BUF | apply rw_cells_CB0; exact DST | exact ST | exact MI | exact MU | exact WM | solve [frange]
                | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                | unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]
                | reflexivity | rewrite ?Z.mod_small in Hn by lia; lia
                | match goal with |- ?g => idtac "FL0:" g end ].
      + (* [comment removed for export] *)
        zs. zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. cbn [fread_loop]. change (n <=? 0) with (n <=? 0).
        replace (n <=? 0) with true by (symmetry; apply Z.leb_le; rewrite ?Z.mod_small in Hn by lia; lia).
        apply implM_ret. apply evt_done.
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
      assert (SRCB : bytes_at ssegs m0 rp (to_bytes (f_rbuf f0))).
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
        apply (rw_cells_split_CB ssegs _ _ [] (Z.to_nat n) djunk [] [length (f_rbuf f0); Z.to_nat n - length (f_rbuf f0)]%nat) in DST0; [| cbn; lia].
        cbn [mk_CB_cells app] in DST0.
        apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
        cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r in DSTb.
        clear DST. zs.
        call memcpy_callw.
        1:{ exact SRCB. }
        1:{ rewrite length_to_bytes, Nat2Z.id. reflexivity. }
        1:{ rewrite Nat2Z.id. exact DSTa. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        rewrite !Nat2Z.id in *.
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 1:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        apply evt_done.
        lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
        rewrite firstn_all.
        lazymatch goal with DB : rw_cells ssegs mA (D + Z.of_nat (length (f_rbuf f0))) _ |- _ => rename DB into DSTb' | _ => idtac "noDSTb" end.
        assert (DJ : rw_cells ssegs mA D [CB (length (f_rbuf f0)) (to_bytes (f_rbuf f0)); CB (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) (firstn (Z.to_nat n - length (f_rbuf f0)) (skipn (length (f_rbuf f0)) djunk))]).
        { apply (proj2 (rw_cells_app ssegs mA D [_] [_])). cbn [cells_size csize Nat.add]. rewrite ?Nat.add_0_r. split; [exact PC|].
          replace (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) with (Z.to_nat n - length (f_rbuf f0))%nat by lia. exact DSTb'. }
        eapply (fread_loop_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf (skipn (length (f_rbuf f0)) (f_rbuf f0)) f0) flags _ (rp + Z.of_nat (length (f_rbuf f0))) bufbytes);
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
        assert (SRCn : bytes_at ssegs m0 rp (firstn (Z.to_nat n) (to_bytes (f_rbuf f0)))).
        { rewrite <- (firstn_skipn (Z.to_nat n) (to_bytes (f_rbuf f0))) in SRCB. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRCB)). }
        clear SRCB. zs.
        call memcpy_callw.
        1:{ exact SRCn. }
        1:{ rewrite length_firstn, length_to_bytes. lia. }
        1:{ exact DST. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. cbn [fread_loop].
        replace (n - n <=? 0) with true by (symmetry; apply Z.leb_le; lia).
        apply implM_ret. apply evt_done.
        unfold fread_post. cbn [fst snd f_rbuf set_rbuf].
        split; [reflexivity|]. split; [unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]|].
        split; [rewrite length_firstn; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (zlength (firstn (Z.to_nat n) (f_rbuf f0))) with n by (unfold zlength; rewrite length_firstn; lia).
        lazymatch goal with H : mem_inv ssegs mZ |- _ => rename H into MIZ end.
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
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk. ltac2:(SecDiet.SzSec.closeP 'fread_spec__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End FreadMain.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rw_cells_CB0' : forall m A n bs, rw_cells usegs m A [CB n bs] -> rw_cells usegs m A [CB n bs; CB 0 []].
Proof.
  intros m A n bs [[W B] R]. split; [split|].
  - cbn in *. repeat split; try reflexivity. exact (proj1 W).
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact B.
  - cbn [cells_size csize Nat.add] in *. rewrite Nat.add_0_r in *. exact R.
Qed.

Section FreadMain.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_DEPTH.
  Hypothesis GLO : 0x56000 <= lo.
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
  Definition fread_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp : Z) (bufbytes djunk : list byte),
      rw_cells usegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      flags_ok f0 flags ->
      rw_cells usegs m B [CB (Z.to_nat bs) bufbytes] ->
      (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs /\ firstn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes) = to_bytes (f_rbuf f0)) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      rw_cells usegs m D [CB (Z.to_nat n) djunk] ->
      f_wactive f0 = false -> f_wbuf f0 = [] -> Forall (fun z => 0 <= z < 256) (f_rbuf f0) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Fp ->
      stk usegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (fread_file f0 B D n) st (fread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD) fc None m (seg_rom usegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk : ltac2:(SecDiet.SzSec.tyM 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_spec__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 : unit) => tt).
 intros FC FL BUF RREL RP0 RPHI DST WACT WB0 RBR -> -> -> -> ST SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD, FREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (fr_W sp f0 Fp B D n) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold fr_W, FREAD_DEPTH in MU.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    unfold fread_file. cbv zeta.
    apply implM_prefix.
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
        apply evt_done.
        replace (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B D n []) with (fread_loop (S (Z.to_nat n)) (set_rbuf [] f0) B (D + 0) n [] : M St (list Z * file_st)) by (rewrite Z.add_0_r; reflexivity).
        eapply implM_at_eq; [eapply (fread_loop_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf [] f0) flags _ rp bufbytes djunk [] 0 n)
                            | cbv delta [mkR]; rewrite Z.add_0_r; reflexivity];
          first [ exact FR | exact FC | exact FL | exact BUF | apply rw_cells_CB0; exact DST | exact ST | exact MI | exact MU | exact WM | solve [frange]
                | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                | unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]
                | reflexivity | rewrite ?Z.mod_small in Hn by lia; lia
                | match goal with |- ?g => idtac "FL0:" g end ].
      + (* [comment removed for export] *)
        zs. zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. cbn [fread_loop]. change (n <=? 0) with (n <=? 0).
        replace (n <=? 0) with true by (symmetry; apply Z.leb_le; rewrite ?Z.mod_small in Hn by lia; lia).
        apply implM_ret. apply evt_done.
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
      assert (SRCB : bytes_at usegs m0 rp (to_bytes (f_rbuf f0))).
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
        apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat n) djunk [] [length (f_rbuf f0); Z.to_nat n - length (f_rbuf f0)]%nat) in DST0; [| cbn; lia].
        cbn [mk_CB_cells app] in DST0.
        apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
        cbn [cells_size csize Nat.add] in DSTb. rewrite ?Nat.add_0_r in DSTb.
        clear DST. zs.
        call memcpy_callw.
        1:{ exact SRCB. }
        1:{ rewrite length_to_bytes, Nat2Z.id. reflexivity. }
        1:{ rewrite Nat2Z.id. exact DSTa. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        rewrite !Nat2Z.id in *.
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 1:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        apply evt_done.
        lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
        rewrite firstn_all.
        lazymatch goal with DB : rw_cells usegs mA (D + Z.of_nat (length (f_rbuf f0))) _ |- _ => rename DB into DSTb' | _ => idtac "noDSTb" end.
        assert (DJ : rw_cells usegs mA D [CB (length (f_rbuf f0)) (to_bytes (f_rbuf f0)); CB (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) (firstn (Z.to_nat n - length (f_rbuf f0)) (skipn (length (f_rbuf f0)) djunk))]).
        { apply (proj2 (rw_cells_app usegs mA D [_] [_])). cbn [cells_size csize Nat.add]. rewrite ?Nat.add_0_r. split; [exact PC|].
          replace (Z.to_nat (n - Z.of_nat (length (f_rbuf f0)))) with (Z.to_nat n - length (f_rbuf f0))%nat by lia. exact DSTb'. }
        eapply (fread_loop_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m NCH FD BS NB LO GLO SP47 Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D47 SB1 SB2 SD1 SD2 SD3 (S (Z.to_nat n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_rbuf (skipn (length (f_rbuf f0)) (f_rbuf f0)) f0) flags _ (rp + Z.of_nat (length (f_rbuf f0))) bufbytes);
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
        assert (SRCn : bytes_at usegs m0 rp (firstn (Z.to_nat n) (to_bytes (f_rbuf f0)))).
        { rewrite <- (firstn_skipn (Z.to_nat n) (to_bytes (f_rbuf f0))) in SRCB. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRCB)). }
        clear SRCB. zs.
        call memcpy_callw.
        1:{ exact SRCn. }
        1:{ rewrite length_firstn, length_to_bytes. lia. }
        1:{ exact DST. }
        1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
        zs. zs. zs. try clear POST; (zs). zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
        zs. zs. zs. rewrite ?retval_size1 by lia. zs. if_true. do 10 zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. cbn [fread_loop].
        replace (n - n <=? 0) with true by (symmetry; apply Z.leb_le; lia).
        apply implM_ret. apply evt_done.
        unfold fread_post. cbn [fst snd f_rbuf set_rbuf].
        split; [reflexivity|]. split; [unfold fr_inv; cbn; repeat split; first [reflexivity | assumption]|].
        split; [rewrite length_firstn; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        replace (zlength (firstn (Z.to_nat n) (f_rbuf f0))) with n by (unfold zlength; rewrite length_firstn; lia).
        lazymatch goal with H : mem_inv usegs mZ |- _ => rename H into MIZ end.
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
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk. ltac2:(SecDiet.SzSec.closeP 'fread_spec__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End FreadMain.
End TwB.
End F_fread_top.

(* [comment removed for export] *)
Module Stdio_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_STDERR_USED : Z := 0x23748.
Definition A_STDIN_USED : Z := 0x23838.
Definition A_STDOUT_USED : Z := 0x23928.
(* [comment removed for export] *)
Definition stdio_static (a : Z) : Prop := (0x23660 <= a < 0x23930) \/ (0x54148 <= a < 0x54970).

(* [comment removed for export] *)
Definition stdin_cells : list cell :=
  file_cells (Z_to_bv 64 9) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ 0 F_STDIO_SEEK A_STDIN_BUF 1024 0 0 0 (Z_to_bv 64 0) 0 (repeat (Z_to_bv 8 0) 80).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FILE_R (m : mem) (f : file_st) (Fp BA closefn readfn seekfn prev next : Z) : Prop :=
  exists (flags mode : word) (rp : Z) (tail bufbytes : list byte),
     rw_cells ssegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
          (if f_wactive f then BA + f_bufsize f else 0) (if f_wactive f then BA + zlength (f_wbuf f) else 0) (if f_wactive f then BA else 0)
          readfn (wfn_of f) seekfn BA (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
  /\ flags_ok f flags
  /\ rw_cells ssegs m BA [CB (Z.to_nat (f_bufsize f)) bufbytes]
  /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
  /\ (f_wactive f = false -> f_wbuf f = [])
  /\ zlength (f_wbuf f) <= f_bufsize f
  /\ (f_rbuf f <> [] -> BA <= rp /\ rp + zlength (f_rbuf f) <= BA + f_bufsize f
                       /\ firstn (length (f_rbuf f)) (skipn (Z.to_nat (rp - BA)) bufbytes) = to_bytes (f_rbuf f))
  /\ 0 <= rp /\ rp + zlength (f_rbuf f) < 2^63
  /\ firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition heap_file_inv (f : file_st) : Prop :=
  f_chan f = false /\ 3 <= f_fd f < 2^31 /\ f_bufsize f = BUFSIZ
  /\ f_nord f = negb (f_nowr f) /\ (f_nowr f = true -> f_wactive f = false /\ f_wbuf f = []) /\ (f_nord f = true -> f_rbuf f = [])
  /\ Forall (fun z => 0 <= z < 256) (f_rbuf f).
Definition stdout_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 1 /\ f_bufsize f = BUFSIZ /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ (f_stdoutw f = true -> f_lbf_nl f = true).
Definition stderr_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 2 /\ f_bufsize f = 0 /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ f_stdoutw f = false /\ f_lbf_nl f = false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithPtr.
  Context {hptr : Type}.
  Notation cblk := (hptr * Z * Z)%type.
  Definition hd_addr (FB : list cblk) : Z := match FB with [] => 0 | (_, A, _) :: _ => A end.

  (* [comment removed for export] *)
  Fixpoint files_R (m : mem) (prev : Z) (fs : list (hptr * file_st)) (FB : list cblk) : Prop :=
    match fs, FB with
    | [], [] => True
    | (q, f) :: fs', (q', A, n) :: FB' =>
        q' = q /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
        /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK prev (hd_addr FB')
        /\ heap_file_inv f
        /\ files_R m A fs' FB'
    | _, _ => False
    end.

  Definition STDIOR (l : @libc_st hptr) (FB : list cblk) (m : mem) : Prop :=
       FILE_R m (lc_stdout l) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stdout_inv (lc_stdout l)
    /\ FILE_R m (lc_stderr l) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stderr_inv (lc_stderr l)
    /\ rw_cells ssegs m A_STDIN stdin_cells
    /\ rw_cells ssegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]
    /\ rw_cells ssegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]
    /\ rw_cells ssegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]
    /\ rw_cells ssegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)]
    /\ rw_cells ssegs m A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]
    /\ files_R m 0 (lc_files l) FB
    /\ List.NoDup (map fst (lc_files l)).

  (* [comment removed for export] *)
  Definition stdio_init_stmt : Prop :=
    forall m,
      rw_cells ssegs m A_STDOUT (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells ssegs m A_STDERR (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells ssegs m A_STDIN stdin_cells ->
      (exists bb, rw_cells ssegs m A_STDOUT_BUF [CB 1024 bb]) -> rw_cells ssegs m A_STDERR_BUF [CB 0 []] ->
      rw_cells ssegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] -> rw_cells ssegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] ->
      rw_cells ssegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
      rw_cells ssegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m A_OFL_HEAD [C8 (Z_to_bv 64 0)] ->
      STDIOR libc_init [] m.

  (* [comment removed for export] *)
  Definition stdio_frame_stmt : Prop :=
    forall l FB m m' W,
      STDIOR l FB m -> munch W m m' -> wmono ssegs m m' ->
      Forall (fun iv => (snd iv <= 0x23660 \/ 0x23930 <= fst iv) /\ (snd iv <= 0x54148 \/ 0x54970 <= fst iv)) W ->
      Forall (fun iv => Forall (fun b => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W ->
      STDIOR l FB m'.
End WithPtr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition client_buf (FB : list (Z * Z)) (lo sp S len : Z) : Prop :=
  0 <= S /\ S + len < 2^63 /\ (S + len <= lo \/ sp <= S)
  /\ (S + len <= 0x23660 \/ 0x23930 <= S) /\ (S + len <= 0x54148 \/ 0x54970 <= S)
  /\ (S + len <= 0x22620 \/ 0x22628 <= S) /\ (S + len <= 0x53d08 \/ 0x53d10 <= S)
  /\ Forall (fun b => S + len <= fst b \/ fst b + snd b <= S) FB.

Section Stmts.
  Context {St hptr : Type} (get_lc : St -> @libc_st hptr) (set_lc : @libc_st hptr -> St -> St).
  Context (ptr_eqb : hptr -> hptr -> bool) (hmalloc : Z -> M St (option hptr)) (hfree : hptr -> M St unit) (buf_addr : St -> hptr -> Z).
  Hypothesis get_set : forall s l, get_lc (set_lc l s) = l.
  Hypothesis set_get : forall s, set_lc (get_lc s) s = s.
  Hypothesis set_set : forall s l l', set_lc l' (set_lc l s) = set_lc l' s.
  Hypothesis ptr_eqb_spec : forall p q, ptr_eqb p q = true <-> p = q.
  Notation cblk := (hptr * Z * Z)%type.
  Definition blk_ivs (FB : list cblk) : list (Z * Z) := map (fun b => (snd (fst b), snd b)) FB.

  (* [comment removed for export] *)
  Definition blocks_below (FB : list cblk) (lo : Z) : Prop :=
    Forall (fun b => 0x55000 <= snd (fst b) /\ snd (fst b) + snd b <= lo /\ snd (fst b) mod 16 = 0) FB.

  (* [comment removed for export] *)
  Definition stdio_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (FB : list cblk) (W : list (Z * Z)) (lo : Z) (canary : word) (m : mem)
      (RV : Z -> Prop) {A} (rv : A -> Z) : A -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rv r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ RV (rv r)
      /\ munch W m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ STDIOR (get_lc st') FB m'
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition FWRITE_STACK : Z := 272.
  Definition fwrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (q : hptr) (A : Z) (f : file_st)
           (s : list byte) (S lo : Z) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      In (q, A, FILE_ALLOC) FB -> files_lookup ptr_eqb (lc_files (get_lc st)) q = Some f -> f_nowr f = false ->
      bytes_at ssegs m S s -> client_buf (blk_ivs FB) lo (bv_unsigned sp) S (Z.of_nat (length s)) -> Z.of_nat (length s) < 2^25 ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (Z.of_nat (length s)) -> a3 = Z_to_bv 64 A ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_STACK -> 0x55000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv ssegs m ->
      implM ssegs (fwrite get_lc set_lc ptr_eqb q (of_bytes s)) st
        (stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (A, A + FILE_ALLOC)] lo canary m
                    (fun r => r = Z.of_nat (length s)) (fun r => r))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition efwrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (s : list byte) (S lo : Z) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      bytes_at ssegs m S s -> client_buf (blk_ivs FB) lo (bv_unsigned sp) S (Z.of_nat (length s)) -> (1 <= length s)%nat -> Z.of_nat (length s) < 2^25 ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (Z.of_nat (length s)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 A_STDERR ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_STACK -> 0x55000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv ssegs m ->
      implM ssegs (efwrite get_lc set_lc (of_bytes s)) st
        (stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (0x23660, 0x23930); (0x54148, 0x54970)] lo canary m
                    (fun r => r = 1) (fun _ => 1))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition FREAD_STACK : Z := 400.
  Definition fread_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (q : hptr) (A : Z) (f : file_st)
           (D n lo : Z) (junk : list byte) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      In (q, A, FILE_ALLOC) FB -> files_lookup ptr_eqb (lc_files (get_lc st)) q = Some f -> f_nord f = false ->
      buf_addr st q = A + FILE_BUF_OFF ->
      rw_cells ssegs m D [CB (Z.to_nat n) junk] -> client_buf (blk_ivs FB) lo (bv_unsigned sp) D n -> 0 <= n < 2^25 ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 A ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FREAD_STACK -> 0x55000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv ssegs m ->
      implM ssegs (fread get_lc set_lc ptr_eqb buf_addr q D n) st
        (fun r st' ms' =>
           stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (A, A + FILE_ALLOC); (D, D + n)] lo canary m
                      (fun k => 0 <= k <= n) (fun r => zlength r) r st' ms'
           /\ rw_cells ssegs (ms_mem ms') D [CB (length r) (to_bytes r); CB (Z.to_nat n - length r) (skipn (length r) junk)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FPRINTF : Z := 0x1b584.
  Definition FPRINTF_STACK : Z := 8192.
  Definition fprintf_shape (ARGS : machine_state -> Prop) (ps : list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (q : hptr) (A : Z) (f : file_st) (lo : Z) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      In (q, A, FILE_ALLOC) FB -> files_lookup ptr_eqb (lc_files (get_lc st)) q = Some f -> f_nowr f = false ->
      a0 = Z_to_bv 64 A ->
      ARGS (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FPRINTF) fc None m (seg_rom ssegs)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FPRINTF_STACK -> 0x55000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv ssegs m ->
      implM ssegs (fprintf get_lc set_lc ptr_eqb q ps) st
        (stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (A, A + FILE_ALLOC)] lo canary m
                    (fun _ => True) (fun _ => 0))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF) fc None m (seg_rom ssegs)).
End Stmts.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_STDERR_USED : Z := 0x23f08.
Definition A_STDIN_USED : Z := 0x23ff8.
Definition A_STDOUT_USED : Z := 0x240e8.
(* [comment removed for export] *)
Definition stdio_static (a : Z) : Prop := (0x23e20 <= a < 0x240f0) \/ (0x54908 <= a < 0x55130).

(* [comment removed for export] *)
Definition stdin_cells : list cell :=
  file_cells (Z_to_bv 64 9) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ 0 F_STDIO_SEEK A_STDIN_BUF 1024 0 0 0 (Z_to_bv 64 0) 0 (repeat (Z_to_bv 8 0) 80).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FILE_R (m : mem) (f : file_st) (Fp BA closefn readfn seekfn prev next : Z) : Prop :=
  exists (flags mode : word) (rp : Z) (tail bufbytes : list byte),
     rw_cells usegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
          (if f_wactive f then BA + f_bufsize f else 0) (if f_wactive f then BA + zlength (f_wbuf f) else 0) (if f_wactive f then BA else 0)
          readfn (wfn_of f) seekfn BA (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
  /\ flags_ok f flags
  /\ rw_cells usegs m BA [CB (Z.to_nat (f_bufsize f)) bufbytes]
  /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
  /\ (f_wactive f = false -> f_wbuf f = [])
  /\ zlength (f_wbuf f) <= f_bufsize f
  /\ (f_rbuf f <> [] -> BA <= rp /\ rp + zlength (f_rbuf f) <= BA + f_bufsize f
                       /\ firstn (length (f_rbuf f)) (skipn (Z.to_nat (rp - BA)) bufbytes) = to_bytes (f_rbuf f))
  /\ 0 <= rp /\ rp + zlength (f_rbuf f) < 2^63
  /\ firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition heap_file_inv (f : file_st) : Prop :=
  f_chan f = false /\ 3 <= f_fd f < 2^31 /\ f_bufsize f = BUFSIZ
  /\ f_nord f = negb (f_nowr f) /\ (f_nowr f = true -> f_wactive f = false /\ f_wbuf f = []) /\ (f_nord f = true -> f_rbuf f = [])
  /\ Forall (fun z => 0 <= z < 256) (f_rbuf f).
Definition stdout_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 1 /\ f_bufsize f = BUFSIZ /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ (f_stdoutw f = true -> f_lbf_nl f = true).
Definition stderr_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 2 /\ f_bufsize f = 0 /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ f_stdoutw f = false /\ f_lbf_nl f = false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithPtr.
  Context {hptr : Type}.
  Notation cblk := (hptr * Z * Z)%type.
  Definition hd_addr (FB : list cblk) : Z := match FB with [] => 0 | (_, A, _) :: _ => A end.

  (* [comment removed for export] *)
  Fixpoint files_R (m : mem) (prev : Z) (fs : list (hptr * file_st)) (FB : list cblk) : Prop :=
    match fs, FB with
    | [], [] => True
    | (q, f) :: fs', (q', A, n) :: FB' =>
        q' = q /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
        /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK prev (hd_addr FB')
        /\ heap_file_inv f
        /\ files_R m A fs' FB'
    | _, _ => False
    end.

  Definition STDIOR (l : @libc_st hptr) (FB : list cblk) (m : mem) : Prop :=
       FILE_R m (lc_stdout l) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stdout_inv (lc_stdout l)
    /\ FILE_R m (lc_stderr l) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stderr_inv (lc_stderr l)
    /\ rw_cells usegs m A_STDIN stdin_cells
    /\ rw_cells usegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]
    /\ rw_cells usegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]
    /\ rw_cells usegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]
    /\ rw_cells usegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs m A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]
    /\ files_R m 0 (lc_files l) FB
    /\ List.NoDup (map fst (lc_files l)).

  (* [comment removed for export] *)
  Definition stdio_init_stmt : Prop :=
    forall m,
      rw_cells usegs m A_STDOUT (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells usegs m A_STDERR (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells usegs m A_STDIN stdin_cells ->
      (exists bb, rw_cells usegs m A_STDOUT_BUF [CB 1024 bb]) -> rw_cells usegs m A_STDERR_BUF [CB 0 []] ->
      rw_cells usegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] -> rw_cells usegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] ->
      rw_cells usegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
      rw_cells usegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells usegs m A_OFL_HEAD [C8 (Z_to_bv 64 0)] ->
      STDIOR libc_init [] m.

  (* [comment removed for export] *)
  Definition stdio_frame_stmt : Prop :=
    forall l FB m m' W,
      STDIOR l FB m -> munch W m m' -> wmono usegs m m' ->
      Forall (fun iv => (snd iv <= 0x23e20 \/ 0x240f0 <= fst iv) /\ (snd iv <= 0x54908 \/ 0x55130 <= fst iv)) W ->
      Forall (fun iv => Forall (fun b => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W ->
      STDIOR l FB m'.
End WithPtr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition client_buf (FB : list (Z * Z)) (lo sp S len : Z) : Prop :=
  0 <= S /\ S + len < 2^63 /\ (S + len <= lo \/ sp <= S)
  /\ (S + len <= 0x23e20 \/ 0x240f0 <= S) /\ (S + len <= 0x54908 \/ 0x55130 <= S)
  /\ (S + len <= 0x22de0 \/ 0x22de8 <= S) /\ (S + len <= 0x544c8 \/ 0x544d0 <= S)
  /\ Forall (fun b => S + len <= fst b \/ fst b + snd b <= S) FB.

Section Stmts.
  Context {St hptr : Type} (get_lc : St -> @libc_st hptr) (set_lc : @libc_st hptr -> St -> St).
  Context (ptr_eqb : hptr -> hptr -> bool) (hmalloc : Z -> M St (option hptr)) (hfree : hptr -> M St unit) (buf_addr : St -> hptr -> Z).
  Hypothesis get_set : forall s l, get_lc (set_lc l s) = l.
  Hypothesis set_get : forall s, set_lc (get_lc s) s = s.
  Hypothesis set_set : forall s l l', set_lc l' (set_lc l s) = set_lc l' s.
  Hypothesis ptr_eqb_spec : forall p q, ptr_eqb p q = true <-> p = q.
  Notation cblk := (hptr * Z * Z)%type.
  Definition blk_ivs (FB : list cblk) : list (Z * Z) := map (fun b => (snd (fst b), snd b)) FB.

  (* [comment removed for export] *)
  Definition blocks_below (FB : list cblk) (lo : Z) : Prop :=
    Forall (fun b => 0x56000 <= snd (fst b) /\ snd (fst b) + snd b <= lo /\ snd (fst b) mod 16 = 0) FB.

  (* [comment removed for export] *)
  Definition stdio_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (FB : list cblk) (W : list (Z * Z)) (lo : Z) (canary : word) (m : mem)
      (RV : Z -> Prop) {A} (rv : A -> Z) : A -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rv r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ RV (rv r)
      /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ STDIOR (get_lc st') FB m'
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition FWRITE_STACK : Z := 272.
  Definition fwrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (q : hptr) (A : Z) (f : file_st)
           (s : list byte) (S lo : Z) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      In (q, A, FILE_ALLOC) FB -> files_lookup ptr_eqb (lc_files (get_lc st)) q = Some f -> f_nowr f = false ->
      bytes_at usegs m S s -> client_buf (blk_ivs FB) lo (bv_unsigned sp) S (Z.of_nat (length s)) -> Z.of_nat (length s) < 2^25 ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (Z.of_nat (length s)) -> a3 = Z_to_bv 64 A ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_STACK -> 0x56000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (fwrite get_lc set_lc ptr_eqb q (of_bytes s)) st
        (stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (A, A + FILE_ALLOC)] lo canary m
                    (fun r => r = Z.of_nat (length s)) (fun r => r))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition efwrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (s : list byte) (S lo : Z) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      bytes_at usegs m S s -> client_buf (blk_ivs FB) lo (bv_unsigned sp) S (Z.of_nat (length s)) -> (1 <= length s)%nat -> Z.of_nat (length s) < 2^25 ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (Z.of_nat (length s)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 A_STDERR ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_STACK -> 0x56000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (efwrite get_lc set_lc (of_bytes s)) st
        (stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (0x23e20, 0x240f0); (0x54908, 0x55130)] lo canary m
                    (fun r => r = 1) (fun _ => 1))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition FREAD_STACK : Z := 400.
  Definition fread_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (q : hptr) (A : Z) (f : file_st)
           (D n lo : Z) (junk : list byte) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      In (q, A, FILE_ALLOC) FB -> files_lookup ptr_eqb (lc_files (get_lc st)) q = Some f -> f_nord f = false ->
      buf_addr st q = A + FILE_BUF_OFF ->
      rw_cells usegs m D [CB (Z.to_nat n) junk] -> client_buf (blk_ivs FB) lo (bv_unsigned sp) D n -> 0 <= n < 2^25 ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 A ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FREAD_STACK -> 0x56000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (fread get_lc set_lc ptr_eqb buf_addr q D n) st
        (fun r st' ms' =>
           stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (A, A + FILE_ALLOC); (D, D + n)] lo canary m
                      (fun k => 0 <= k <= n) (fun r => zlength r) r st' ms'
           /\ rw_cells usegs (ms_mem ms') D [CB (length r) (to_bytes r); CB (Z.to_nat n - length r) (skipn (length r) junk)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FPRINTF : Z := 0x1bd44.
  Definition FPRINTF_STACK : Z := 8192.
  Definition fprintf_shape (ARGS : machine_state -> Prop) (ps : list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (FB : list cblk) (q : hptr) (A : Z) (f : file_st) (lo : Z) (canary : word),
      STDIOR (get_lc st) FB m -> blocks_below FB lo ->
      In (q, A, FILE_ALLOC) FB -> files_lookup ptr_eqb (lc_files (get_lc st)) q = Some f -> f_nowr f = false ->
      a0 = Z_to_bv 64 A ->
      ARGS (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FPRINTF) fc None m (seg_rom usegs)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FPRINTF_STACK -> 0x56000 <= lo -> bv_unsigned sp < 2^63 ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (fprintf get_lc set_lc ptr_eqb q ps) st
        (stdio_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FB [(lo, bv_unsigned sp); (A, A + FILE_ALLOC)] lo canary m
                    (fun _ => True) (fun _ => 0))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF) fc None m (seg_rom usegs)).
End Stmts.
End TwB.
End Stdio_iface.

(* [comment removed for export] *)
Module F_stdio_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

Definition STDIO_EXIT_ENTRY : Z := 0x1ae7c.
Definition EXIT_LOOP : Z := 0x1afbc.      (* [comment removed for export] *)
Definition EXIT_NEXT : Z := 0x1afb4.      (* [comment removed for export] *)
Definition EXIT_SYNC : Z := 0x1afec.      (* [comment removed for export] *)
Definition EXIT_DEPTH : Z := 144.         (* [comment removed for export] *)

Section Exit.
  Context {St : Type}.

  Definition ex_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - EXIT_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition exit_body_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (Fp next : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EXIT_NEXT) fc None m' (seg_rom ssegs)
      /\ munch (ex_W sp Fp) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' (Fp + 112) [C8 (Z_to_bv 64 next)]
      /\ ssp_cells m' canary.

  Section Body.
    Variables (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - EXIT_DEPTH.
    Hypothesis GLO : 0x55000 <= lo.
    Hypothesis Fp0 : 0 < Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.

    Lemma fcells_next_cell : forall mm flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
      rw_cells ssegs mm Fp (fcells flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl) ->
      rw_cells ssegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)].
    Proof using Type. pin_using tt.
      intros. unfold fcells, file_cells in H.
      do 15 (apply (proj1 (rw_cells_app ssegs mm _ [_] _)) in H as [_ H]).
      apply (proj1 (rw_cells_app ssegs mm _ [_] _)) in H as [H _]. cbn [cells_size csize Nat.add] in H.
      match type of H with rw_cells _ _ ?a _ => replace a with (Fp + 112) in H by lia end. exact H.
    Qed.

    (* [comment removed for export] *)
    Definition exit_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells ssegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> f_fd f1 = f_fd f ->
      ssp_cells m1 canary -> stk ssegs m1 lo (bv_unsigned sp) -> mem_inv ssegs m1 ->
      munch (ex_W sp Fp) m m1 -> wmono ssegs m m1 ->
      implM ssegs (sync_read_pos f1) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_SYNC) fc None m1 (seg_rom ssegs)).
    Section Sz2.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_sync__body : ltac2:(SecDiet.SzSec.bodyP 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD Fp0. pin_using (fun (FD Fp0 : unit) => tt).
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
        rewrite RB. apply implM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        apply evt_done. unfold exit_body_post. split; [reflexivity|].
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
        apply implM_prefix.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. unfold F_STDIO_SEEK in *. zs.
        apply evt_done. rewrite FD1.
        eapply implM_bind.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x1b00c)) with (Z_to_bv 64 0x1b00c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply implM_ret. zs.
        apply evt_done. unfold exit_body_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [exact NXC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz2.
    Lemma exit_sync : ltac:(let t := eval cbv delta [exit_sync__stmt] in exit_sync__stmt in exact t).
    Proof using FD Fp0. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'exit_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition exit_body__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rp : Z) (mode : word) (bufbytes : list byte),
      rw_cells ssegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk ssegs m lo (bv_unsigned sp) -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv ssegs m ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      implM ssegs (close_file f) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_LOOP) fc None m (seg_rom ssegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes : ltac2:(SecDiet.SzSec.tyM 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_body__body : ltac2:(SecDiet.SzSec.bodyP 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI CH ST SP47 SSP MI B0 BShi BS0 WBL BSZ SEPB.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_LOOP, EXIT_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof (munch_refl (ex_W sp Fp) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
      pose proof WBL as WBL'. unfold zlength in WBL'.
      assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
      unfold close_file.
      assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
      destruct CASES as [WBN | WBN].
      - (* [comment removed for export] *)
        rewrite WBN. apply implM_retb.
        unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
        apply implM_prefix.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
        apply evt_done.
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
        change (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
        apply implM_prefix.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs. zs. zs.
        assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
        zs. rewrite (ret_pc_even (wfn_of f)) by lia.
        apply evt_done.
        unfold boxed in BUF.
        assert (BUFB : bytes_at ssegs m B (to_bytes (f_wbuf f))).
        { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
        eapply implM_bind.
        { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
            (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
            (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
            rewrite ?unsigned_lit by lia.
          all: first [ reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
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
        replace (ret_pc (Z_to_bv 64 0x1afec)) with (Z_to_bv 64 0x1afec : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes. ltac2:(SecDiet.SzSec.closeP 'exit_body__body "vvvvvvvvvvvvvvvvvvv"). Qed.
  End Body.

  (* [comment removed for export] *)
  Definition exit_next__stmt : Prop := forall (sp gp tp : word) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp nx : Z) (mm : mem),
    rw_cells ssegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)] -> 0 <= Fp -> Fp + 232 < 2^64 -> 0 <= nx < 2^64 -> mem_inv ssegs mm ->
    evt ssegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 nx) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (if nx =? 0 then 0x1ae94 else EXIT_LOOP)) fc None mm (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_NEXT) fc None mm (seg_rom ssegs)).
  Section Sz4.
  Variables sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm : ltac2:(SecDiet.SzSec.tyM 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
  Lemma exit_next__body : ltac2:(SecDiet.SzSec.bodyP 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros NX Fp0 FPHI NXR MI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    unfold EXIT_NEXT, EXIT_LOOP. zs. zs. if_cases K; zify_cond K.
    - replace (nx =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. cbv delta [mkR]. reflexivity.
    - replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz4.
  Lemma exit_next : ltac:(let t := eval cbv delta [exit_next__stmt] in exit_next__stmt in exact t).
  Proof using Type. intros sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm. ltac2:(SecDiet.SzSec.closeP 'exit_next__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_entry__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (hd lo : Z) (m : mem),
    rw_cells ssegs m A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> rw_cells ssegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x55000 <= lo -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (x1 a0' a1' a2' a3' : word) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 hd) s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 (if hd =? 0 then 0x1ae94 else EXIT_LOOP)) fc None m1 (seg_rom ssegs)
        /\ rw_cells ssegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STDIO_EXIT_ENTRY) fc None m (seg_rom ssegs)).
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m : ltac2:(SecDiet.SzSec.tyM 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma exit_entry__body : ltac2:(SecDiet.SzSec.bodyP 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros OH HDR NL ST LO GLO MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold STDIO_EXIT_ENTRY, EXIT_LOOP, A_OFL_HEAD in *. unfold NEED_LOCKS in NL.
    carve_frame 16%nat ST. zs. zs. zs.
    zs. (* [comment removed for export] *)
    carve_frame 16%nat ST; rename FR0 into FRL || idtac.
    all: match goal with |- evt _ _ ?ms => idtac "EN1:" ms end.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs.
    all: match goal with |- evt _ _ ?ms => idtac "EN2:" ms end.
    match goal with H : rw_cells ssegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H ST (bv_unsigned sp + -16) end. zs.
    zs. (* [comment removed for export] *)
    zs. if_cases K; zify_cond K.
    all: match goal with |- evt _ _ ?ms => idtac "EN3:" ms end.
    - replace (hd =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
    - replace (hd =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; repeat f_equal; rewrite ?Z.mod_small in K by lia; try lia; reflexivity|].
      split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma exit_entry : ltac:(let t := eval cbv delta [exit_entry__stmt] in exit_entry__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m. ltac2:(SecDiet.SzSec.closeP 'exit_entry__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdin__stmt : Prop := forall (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    rw_cells ssegs mm A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] -> rw_cells ssegs mm A_STDIN stdin_cells -> mem_inv ssegs mm ->
    evt ssegs (fun ms' => exists (a0' a1' : word), ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 A_STDIN) s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 110320) fc None mm (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ae94) fc None mm (seg_rom ssegs)).
  Section Sz6.
  Variables sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm : ltac2:(SecDiet.SzSec.tyM 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
  Lemma exit_stdin__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US SIN MI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDIN_USED, A_STDIN in *. unfold stdin_cells, file_cells, A_STDIN_BUF, F_STDIO_CLOSE, F_STDIO_READ, F_STDIO_SEEK in SIN.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    apply evt_done. eexists _, _. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz6.
  Lemma exit_stdin : ltac:(let t := eval cbv delta [exit_stdin__stmt] in exit_stdin__stmt in exact t).
  Proof using Type. intros sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm. ltac2:(SecDiet.SzSec.closeP 'exit_stdin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stderr__stmt : Prop := forall (ra sp gp tp : word) (x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (mm : mem) (f : file_st) (flags mode : word) (rp : Z) (tail : list byte) (lo : Z),
    rw_cells ssegs mm A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] ->
    rw_cells ssegs mm A_STDERR (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                                 (if f_wactive f then A_STDERR_BUF + f_bufsize f else 0) (if f_wactive f then A_STDERR_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDERR_BUF else 0)
                                 0 (wfn_of f) F_STDIO_SEEK A_STDERR_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    f_wbuf f = [] -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    rw_cells ssegs mm (bv_unsigned sp + -16) [C8 s0'; C8 ra] -> stk ssegs mm lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 16 -> mem_inv ssegs mm ->
    evt ssegs (fun ms' => exists (a0' a1' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom ssegs)
        /\ stk ssegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1af4c) fc None mm (seg_rom ssegs)).
  Section Sz7.
  Variables ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo : ltac2:(SecDiet.SzSec.tyM 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma exit_stderr__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US FC WBN RBN RP FR ST LO MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDERR_USED, A_STDERR, A_STDERR_BUF in *. unfold fcells, file_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC.
    rewrite WBN, RBN in FC. change (zlength []) with 0 in FC. rewrite !Z.add_0_r in FC.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. destruct (f_wactive f); reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz7.
  Lemma exit_stderr : ltac:(let t := eval cbv delta [exit_stderr__stmt] in exit_stderr__stmt in exact t).
  Proof using Type. intros ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo. ltac2:(SecDiet.SzSec.closeP 'exit_stderr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdout__stmt : Prop := forall (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (st : St) (f : file_st) (flags mode : word) (rp : Z) (tail bufbytes : list byte) (lo : Z) (canary : word),
    rw_cells ssegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
    rw_cells ssegs m A_STDOUT (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                             (if f_wactive f then A_STDOUT_BUF + f_bufsize f else 0) (if f_wactive f then A_STDOUT_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDOUT_BUF else 0)
                             0 (wfn_of f) F_STDIO_SEEK A_STDOUT_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    Z.land (bv_unsigned flags) F_SVB = 0 ->
    rw_cells ssegs m A_STDOUT_BUF [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_bufsize f = BUFSIZ -> zlength (f_wbuf f) <= f_bufsize f ->
    stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - EXIT_DEPTH -> 0x55000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (close_file f) st
      (fun _ st' ms' => st' = st /\
         exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
         ms' = MS (mkR x1' sp gp tp t0' t1' t2' (Z_to_bv 64 A_STDOUT) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1af4c) fc None m' (seg_rom ssegs)
         /\ munch (ex_W sp A_STDOUT) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
         /\ stk ssegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary)
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 110320) fc None m (seg_rom ssegs)).
  Section Sz8.
  Variables sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
  Lemma exit_stdout__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros US FC FL64 BUF BUFP WB0 RBN RP CHN FD12 BS WBL ST LO GLO SP47 SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_DEPTH in *.
    unfold A_STDOUT_USED, A_STDOUT, A_STDOUT_BUF, BUFSIZ in *.
    pose proof (munch_refl (ex_W sp 145472) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    rewrite RBN in FC. change (zlength (@nil Z)) with 0 in FC. rewrite Z.add_0_r in FC.
    unfold close_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb. unfold sync_read_pos. rewrite RBN. apply implM_ret.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      apply evt_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
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
      change (rw_cells ssegs m 345456 [CB (Z.to_nat 1024) bufbytes]) with (boxed (rw_cells ssegs m 345456 [CB (Z.to_nat 1024) bufbytes])) in BUF.
      apply implM_prefix.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evt_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at ssegs m 345456 (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat 1024) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
      eapply implM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := 145472) (flags := flags) (rpos := rp) (rend := rp) (closefn := F_STDIO_CLOSE) (wend := 345456 + 1024) (readfn := 0)
          (seekfn := F_STDIO_SEEK) (B := 345456) (bufsize := 1024) (prev := 0) (next := 0) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: first [ reflexivity | rewrite BS; exact FC | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | rewrite CHN; exact FD12
                   | left; reflexivity
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   | match goal with |- ?g => idtac "WFo side:" g end ]. }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x1af2c)) with (Z_to_bv 64 0x1af2c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold sync_read_pos. rewrite rbuf_after_write', RBN. apply implM_ret.
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      all: match goal with |- evt _ _ ?ms => idtac "SO:" ms end.
      apply evt_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, ex_W, EXIT_DEPTH; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2| exact SSP2].
  Qed.
  End Sz8.
  Theorem exit_stdout : ltac:(let t := eval cbv delta [exit_stdout__stmt] in exit_stdout__stmt in exact t).
  Proof using Type. intros sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'exit_stdout__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Exit.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

Definition STDIO_EXIT_ENTRY : Z := 0x1b63c.
Definition EXIT_LOOP : Z := 0x1b77c.      (* [comment removed for export] *)
Definition EXIT_NEXT : Z := 0x1b774.      (* [comment removed for export] *)
Definition EXIT_SYNC : Z := 0x1b7ac.      (* [comment removed for export] *)
Definition EXIT_DEPTH : Z := 144.         (* [comment removed for export] *)

Section Exit.
  Context {St : Type}.

  Definition ex_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - EXIT_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition exit_body_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (Fp next : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EXIT_NEXT) fc None m' (seg_rom usegs)
      /\ munch (ex_W sp Fp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (Fp + 112) [C8 (Z_to_bv 64 next)]
      /\ ssp_cells m' canary.

  Section Body.
    Variables (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - EXIT_DEPTH.
    Hypothesis GLO : 0x56000 <= lo.
    Hypothesis Fp0 : 0 < Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.

    Lemma fcells_next_cell : forall mm flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
      rw_cells usegs mm Fp (fcells flags' rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl) ->
      rw_cells usegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)].
    Proof using Type. pin_using tt.
      intros. unfold fcells, file_cells in H.
      do 15 (apply (proj1 (rw_cells_app usegs mm _ [_] _)) in H as [_ H]).
      apply (proj1 (rw_cells_app usegs mm _ [_] _)) in H as [H _]. cbn [cells_size csize Nat.add] in H.
      match type of H with rw_cells _ _ ?a _ => replace a with (Fp + 112) in H by lia end. exact H.
    Qed.

    (* [comment removed for export] *)
    Definition exit_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells usegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> f_fd f1 = f_fd f ->
      ssp_cells m1 canary -> stk usegs m1 lo (bv_unsigned sp) -> mem_inv usegs m1 ->
      munch (ex_W sp Fp) m m1 -> wmono usegs m m1 ->
      implM usegs (sync_read_pos f1) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_SYNC) fc None m1 (seg_rom usegs)).
    Section Sz2.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_sync__body : ltac2:(SecDiet.SzSec.bodyP 'exit_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD Fp0. pin_using (fun (FD Fp0 : unit) => tt).
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
        rewrite RB. apply implM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        apply evt_done. unfold exit_body_post. split; [reflexivity|].
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
        apply implM_prefix.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. unfold F_STDIO_SEEK in *. zs.
        apply evt_done. rewrite FD1.
        eapply implM_bind.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x1b7cc)) with (Z_to_bv 64 0x1b7cc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply implM_ret. zs.
        apply evt_done. unfold exit_body_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [exact NXC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz2.
    Lemma exit_sync : ltac:(let t := eval cbv delta [exit_sync__stmt] in exit_sync__stmt in exact t).
    Proof using FD Fp0. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'exit_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition exit_body__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rp : Z) (mode : word) (bufbytes : list byte),
      rw_cells usegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk usegs m lo (bv_unsigned sp) -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv usegs m ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      implM usegs (close_file f) st
        (exit_body_post sp gp tp (Z_to_bv 64 Fp) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st Fp next lo canary m)
        (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_LOOP) fc None m (seg_rom usegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes : ltac2:(SecDiet.SzSec.tyM 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
    Lemma exit_body__body : ltac2:(SecDiet.SzSec.bodyP 'exit_body__stmt "vvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
 intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI CH ST SP47 SSP MI B0 BShi BS0 WBL BSZ SEPB.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_LOOP, EXIT_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof (munch_refl (ex_W sp Fp) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
      pose proof WBL as WBL'. unfold zlength in WBL'.
      assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
      unfold close_file.
      assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
      destruct CASES as [WBN | WBN].
      - (* [comment removed for export] *)
        rewrite WBN. apply implM_retb.
        unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
        apply implM_prefix.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
        apply evt_done.
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
        change (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
        apply implM_prefix.
        zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
        zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs. zs. zs.
        assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
        zs. rewrite (ret_pc_even (wfn_of f)) by lia.
        apply evt_done.
        unfold boxed in BUF.
        assert (BUFB : bytes_at usegs m B (to_bytes (f_wbuf f))).
        { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
        eapply implM_bind.
        { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
            (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
            (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
            rewrite ?unsigned_lit by lia.
          all: first [ reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
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
        replace (ret_pc (Z_to_bv 64 0x1b7ac)) with (Z_to_bv 64 0x1b7ac : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rp mode bufbytes. ltac2:(SecDiet.SzSec.closeP 'exit_body__body "vvvvvvvvvvvvvvvvvvv"). Qed.
  End Body.

  (* [comment removed for export] *)
  Definition exit_next__stmt : Prop := forall (sp gp tp : word) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp nx : Z) (mm : mem),
    rw_cells usegs mm (Fp + 112) [C8 (Z_to_bv 64 nx)] -> 0 <= Fp -> Fp + 232 < 2^64 -> 0 <= nx < 2^64 -> mem_inv usegs mm ->
    evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 nx) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (if nx =? 0 then 0x1b654 else EXIT_LOOP)) fc None mm (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_NEXT) fc None mm (seg_rom usegs)).
  Section Sz4.
  Variables sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm : ltac2:(SecDiet.SzSec.tyM 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
  Lemma exit_next__body : ltac2:(SecDiet.SzSec.bodyP 'exit_next__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros NX Fp0 FPHI NXR MI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    unfold EXIT_NEXT, EXIT_LOOP. zs. zs. if_cases K; zify_cond K.
    - replace (nx =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. cbv delta [mkR]. reflexivity.
    - replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz4.
  Lemma exit_next : ltac:(let t := eval cbv delta [exit_next__stmt] in exit_next__stmt in exact t).
  Proof using Type. intros sp gp tp x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Fp nx mm. ltac2:(SecDiet.SzSec.closeP 'exit_next__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_entry__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (hd lo : Z) (m : mem),
    rw_cells usegs m A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> rw_cells usegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x56000 <= lo -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (x1 a0' a1' a2' a3' : word) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 hd) s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 (if hd =? 0 then 0x1b654 else EXIT_LOOP)) fc None m1 (seg_rom usegs)
        /\ rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STDIO_EXIT_ENTRY) fc None m (seg_rom usegs)).
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m : ltac2:(SecDiet.SzSec.tyM 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma exit_entry__body : ltac2:(SecDiet.SzSec.bodyP 'exit_entry__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros OH HDR NL ST LO GLO MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold STDIO_EXIT_ENTRY, EXIT_LOOP, A_OFL_HEAD in *. unfold NEED_LOCKS in NL.
    carve_frame 16%nat ST. zs. zs. zs.
    zs. (* [comment removed for export] *)
    carve_frame 16%nat ST; rename FR0 into FRL || idtac.
    all: match goal with |- evt _ _ ?ms => idtac "EN1:" ms end.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs.
    all: match goal with |- evt _ _ ?ms => idtac "EN2:" ms end.
    match goal with H : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H ST (bv_unsigned sp + -16) end. zs.
    zs. (* [comment removed for export] *)
    zs. if_cases K; zify_cond K.
    all: match goal with |- evt _ _ ?ms => idtac "EN3:" ms end.
    - replace (hd =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
    - replace (hd =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?Z.mod_small in K by lia; lia).
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; repeat f_equal; rewrite ?Z.mod_small in K by lia; try lia; reflexivity|].
      split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma exit_entry : ltac:(let t := eval cbv delta [exit_entry__stmt] in exit_entry__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc hd lo m. ltac2:(SecDiet.SzSec.closeP 'exit_entry__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdin__stmt : Prop := forall (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    rw_cells usegs mm A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] -> rw_cells usegs mm A_STDIN stdin_cells -> mem_inv usegs mm ->
    evt usegs (fun ms' => exists (a0' a1' : word), ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 A_STDIN) s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x1b6b0) fc None mm (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b654) fc None mm (seg_rom usegs)).
  Section Sz6.
  Variables sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm : ltac2:(SecDiet.SzSec.tyM 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
  Lemma exit_stdin__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros US SIN MI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDIN_USED, A_STDIN in *. unfold stdin_cells, file_cells, A_STDIN_BUF, F_STDIO_CLOSE, F_STDIO_READ, F_STDIO_SEEK in SIN.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    apply evt_done. eexists _, _. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz6.
  Lemma exit_stdin : ltac:(let t := eval cbv delta [exit_stdin__stmt] in exit_stdin__stmt in exact t).
  Proof using Type. intros sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm. ltac2:(SecDiet.SzSec.closeP 'exit_stdin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stderr__stmt : Prop := forall (ra sp gp tp : word) (x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (mm : mem) (f : file_st) (flags mode : word) (rp : Z) (tail : list byte) (lo : Z),
    rw_cells usegs mm A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] ->
    rw_cells usegs mm A_STDERR (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                                 (if f_wactive f then A_STDERR_BUF + f_bufsize f else 0) (if f_wactive f then A_STDERR_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDERR_BUF else 0)
                                 0 (wfn_of f) F_STDIO_SEEK A_STDERR_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    f_wbuf f = [] -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    rw_cells usegs mm (bv_unsigned sp + -16) [C8 s0'; C8 ra] -> stk usegs mm lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 16 -> mem_inv usegs mm ->
    evt usegs (fun ms' => exists (a0' a1' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom usegs)
        /\ stk usegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b70c) fc None mm (seg_rom usegs)).
  Section Sz7.
  Variables ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo : ltac2:(SecDiet.SzSec.tyM 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma exit_stderr__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stderr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros US FC WBN RBN RP FR ST LO MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold A_STDERR_USED, A_STDERR, A_STDERR_BUF in *. unfold fcells, file_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC.
    rewrite WBN, RBN in FC. change (zlength []) with 0 in FC. rewrite !Z.add_0_r in FC.
    zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
    zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
    zs. zs. zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. apply Hw. destruct (f_wactive f); reflexivity. }
    zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
    zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz7.
  Lemma exit_stderr : ltac:(let t := eval cbv delta [exit_stderr__stmt] in exit_stderr__stmt in exact t).
  Proof using Type. intros ra sp gp tp x1 t0 t1 t2 s0 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm f flags mode rp tail lo. ltac2:(SecDiet.SzSec.closeP 'exit_stderr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_stdout__stmt : Prop := forall (sp gp tp : word) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (st : St) (f : file_st) (flags mode : word) (rp : Z) (tail bufbytes : list byte) (lo : Z) (canary : word),
    rw_cells usegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
    rw_cells usegs m A_STDOUT (fcells flags rp (rp + zlength (f_rbuf f)) F_STDIO_CLOSE
                             (if f_wactive f then A_STDOUT_BUF + f_bufsize f else 0) (if f_wactive f then A_STDOUT_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDOUT_BUF else 0)
                             0 (wfn_of f) F_STDIO_SEEK A_STDOUT_BUF (f_bufsize f) 0 0 (f_fd f) mode (lbf_of f) tail) ->
    Z.land (bv_unsigned flags) F_SVB = 0 ->
    rw_cells usegs m A_STDOUT_BUF [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] -> 0 <= rp < 2^63 ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_bufsize f = BUFSIZ -> zlength (f_wbuf f) <= f_bufsize f ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - EXIT_DEPTH -> 0x56000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (close_file f) st
      (fun _ st' ms' => st' = st /\
         exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
         ms' = MS (mkR x1' sp gp tp t0' t1' t2' (Z_to_bv 64 A_STDOUT) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1b70c) fc None m' (seg_rom usegs)
         /\ munch (ex_W sp A_STDOUT) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
         /\ stk usegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary)
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b6b0) fc None m (seg_rom usegs)).
  Section Sz8.
  Variables sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
  Lemma exit_stdout__body : ltac2:(SecDiet.SzSec.bodyP 'exit_stdout__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros US FC FL64 BUF BUFP WB0 RBN RP CHN FD12 BS WBL ST LO GLO SP47 SSP MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold EXIT_DEPTH in *.
    unfold A_STDOUT_USED, A_STDOUT, A_STDOUT_BUF, BUFSIZ in *.
    pose proof (munch_refl (ex_W sp 147456) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold ex_W, EXIT_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    rewrite RBN in FC. change (zlength (@nil Z)) with 0 in FC. rewrite Z.add_0_r in FC.
    unfold close_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb. unfold sync_read_pos. rewrite RBN. apply implM_ret.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hz; zify_cond Hz. 2:{ exfalso. destruct (f_wactive f); rewrite ?Z.mod_small in Hz by lia; lia. }
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      apply evt_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
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
      change (rw_cells usegs m 347440 [CB (Z.to_nat 1024) bufbytes]) with (boxed (rw_cells usegs m 347440 [CB (Z.to_nat 1024) bufbytes])) in BUF.
      apply implM_prefix.
      zs. zs. zs. if_cases K0; zify_cond K0. 1:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. cbn. lia. }
      zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evt_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at usegs m 347440 (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat 1024) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP]. exact BUF. }
      eapply implM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := 147456) (flags := flags) (rpos := rp) (rend := rp) (closefn := F_STDIO_CLOSE) (wend := 347440 + 1024) (readfn := 0)
          (seekfn := F_STDIO_SEEK) (B := 347440) (bufsize := 1024) (prev := 0) (next := 0) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: first [ reflexivity | rewrite BS; exact FC | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | rewrite CHN; exact FD12
                   | left; reflexivity
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   | match goal with |- ?g => idtac "WFo side:" g end ]. }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x1b6ec)) with (Z_to_bv 64 0x1b6ec : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold sync_read_pos. rewrite rbuf_after_write', RBN. apply implM_ret.
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. apply Hr. reflexivity. }
      all: match goal with |- evt _ _ ?ms => idtac "SO:" ms end.
      apply evt_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, ex_W, EXIT_DEPTH; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2| exact SSP2].
  Qed.
  End Sz8.
  Theorem exit_stdout : ltac:(let t := eval cbv delta [exit_stdout__stmt] in exit_stdout__stmt in exact t).
  Proof using Type. intros sp gp tp x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f flags mode rp tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'exit_stdout__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Exit.
End TwB.
End F_stdio_exit.

(* [comment removed for export] *)
Module Stdio_ifaceP.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Lemma disjoint_from_Forall : forall W a n,
  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn; [exact I|].
  apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [lia|]. apply IH. exact H2.
Qed.

Section Frame.
  Context {hptr : Type}.
  Notation cblk := (hptr * Z * Z)%type.

  Lemma FILE_R_transport : forall m m' W f Fp BA closefn readfn seekfn prev next,
    FILE_R m f Fp BA closefn readfn seekfn prev next ->
    munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv : Z * Z => Fp + 232 <= fst iv \/ snd iv <= Fp) W ->
    Forall (fun iv : Z * Z => BA + f_bufsize f <= fst iv \/ snd iv <= BA) W ->
    0 <= f_bufsize f ->
    FILE_R m' f Fp BA closefn readfn seekfn prev next.
  Proof using Type. pin_using tt.
    intros m m' W f Fp BA closefn readfn seekfn prev next FR MU WM D1 D2 BS.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. unfold fcells. rewrite file_cells_size.
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D2]. intros [lo hi]; cbn; lia.
  Qed.

  Lemma files_R_transport : forall fs (FB : list cblk) m m' W prev,
    files_R m prev fs FB -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv : Z * Z => Forall (fun b : cblk => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W ->
    files_R m' prev fs FB.
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros [|[[q' A] n] FB] m m' W prev H MU WM D; cbn in H |- *; try exact H.
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    assert (DW : Forall (fun iv : Z * Z => (snd iv <= A \/ A + FILE_ALLOC <= fst iv) /\
                                          Forall (fun b : cblk => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W).
    { eapply Forall_impl; [| exact D]. intros iv Hb. apply Forall_cons_iff in Hb. destruct Hb as [H1 H2]. cbn [fst snd] in H1. split; [exact H1 | exact H2]. }
    pose proof INV as INV'. destruct INV as (_ & _ & BS & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
    split.
    { eapply FILE_R_transport; [exact FR | exact MU | exact WM | | | rewrite BS; unfold BUFSIZ; lia].
      + eapply Forall_impl; [| exact DW]. intros [lo hi] [H1 _]; cbn in *. unfold FILE_ALLOC in *. lia.
      + eapply Forall_impl; [| exact DW]. intros [lo hi] [H1 _]; cbn in *. rewrite BS. unfold FILE_ALLOC, FILE_BUF_OFF, BUFSIZ in *. lia. }
    split; [exact INV'|].
    eapply IH; [exact REST | exact MU | exact WM |]. eapply Forall_impl; [| exact DW]. intros iv [_ H2]; exact H2.
  Qed.

  Theorem stdio_frame : @stdio_frame_stmt hptr.
  Proof using Type. pin_using tt.
    unfold stdio_frame_stmt. intros l FB m m' W SR MU WM DS DB.
    destruct SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    assert (DSF : forall a n, (0x23660 <= a /\ a + n <= 0x23930) \/ (0x54148 <= a /\ a + n <= 0x54970) ->
                  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W).
    { intros a n H. eapply Forall_impl; [| exact DS]. intros [lo hi] [K1 K2]; cbn in *; lia. }
    pose proof SOI as SOI'. pose proof SEI as SEI'.
    destruct SOI as (_ & _ & SObs & _). destruct SEI as (_ & _ & SEbs & _).
    unfold STDIOR. unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD.
    split. { eapply FILE_R_transport; [exact SO | exact MU | exact WM | apply DSF; lia | rewrite SObs; unfold BUFSIZ; apply DSF; lia | rewrite SObs; unfold BUFSIZ; lia]. }
    split; [exact SOI'|].
    split. { eapply FILE_R_transport; [exact SE | exact MU | exact WM | apply DSF; lia | rewrite SEbs; apply DSF; lia | rewrite SEbs; lia]. }
    split; [exact SEI'|].
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact U1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact U2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact U3 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact OL | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact OH | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split; [| exact ND].
    eapply files_R_transport; [exact FS | exact MU | exact WM | exact DB].
  Qed.

  (* [comment removed for export] *)
  Theorem stdio_init : @stdio_init_stmt hptr.
  Proof using Type. pin_using tt.
    unfold stdio_init_stmt. intros m SO SE SI [bb SOB] SEB U1 U2 U3 OL OH.
    unfold STDIOR, libc_init. cbn [lc_stdout lc_stderr lc_files hd_addr files_R map].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), bb.
      split; [unfold fcells; cbn; exact SO|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SOB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stdout_init]; unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stdout_inv; cbn; repeat split; reflexivity|].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), [].
      split; [unfold fcells; cbn; exact SE|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SEB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stderr_init]; unfold zlength; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stderr_inv; cbn; repeat split; reflexivity|].
    split; [exact SI|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact OL|]. split; [exact OH|].
    split; [exact I|]. constructor.
  Qed.
End Frame.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Lemma disjoint_from_Forall : forall W a n,
  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn; [exact I|].
  apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [lia|]. apply IH. exact H2.
Qed.

Section Frame.
  Context {hptr : Type}.
  Notation cblk := (hptr * Z * Z)%type.

  Lemma FILE_R_transport : forall m m' W f Fp BA closefn readfn seekfn prev next,
    FILE_R m f Fp BA closefn readfn seekfn prev next ->
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => Fp + 232 <= fst iv \/ snd iv <= Fp) W ->
    Forall (fun iv : Z * Z => BA + f_bufsize f <= fst iv \/ snd iv <= BA) W ->
    0 <= f_bufsize f ->
    FILE_R m' f Fp BA closefn readfn seekfn prev next.
  Proof using Type. pin_using tt.
    intros m m' W f Fp BA closefn readfn seekfn prev next FR MU WM D1 D2 BS.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. unfold fcells. rewrite file_cells_size.
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D2]. intros [lo hi]; cbn; lia.
  Qed.

  Lemma files_R_transport : forall fs (FB : list cblk) m m' W prev,
    files_R m prev fs FB -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => Forall (fun b : cblk => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W ->
    files_R m' prev fs FB.
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros [|[[q' A] n] FB] m m' W prev H MU WM D; cbn in H |- *; try exact H.
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    assert (DW : Forall (fun iv : Z * Z => (snd iv <= A \/ A + FILE_ALLOC <= fst iv) /\
                                          Forall (fun b : cblk => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W).
    { eapply Forall_impl; [| exact D]. intros iv Hb. apply Forall_cons_iff in Hb. destruct Hb as [H1 H2]. cbn [fst snd] in H1. split; [exact H1 | exact H2]. }
    pose proof INV as INV'. destruct INV as (_ & _ & BS & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
    split.
    { eapply FILE_R_transport; [exact FR | exact MU | exact WM | | | rewrite BS; unfold BUFSIZ; lia].
      + eapply Forall_impl; [| exact DW]. intros [lo hi] [H1 _]; cbn in *. unfold FILE_ALLOC in *. lia.
      + eapply Forall_impl; [| exact DW]. intros [lo hi] [H1 _]; cbn in *. rewrite BS. unfold FILE_ALLOC, FILE_BUF_OFF, BUFSIZ in *. lia. }
    split; [exact INV'|].
    eapply IH; [exact REST | exact MU | exact WM |]. eapply Forall_impl; [| exact DW]. intros iv [_ H2]; exact H2.
  Qed.

  Theorem stdio_frame : @stdio_frame_stmt hptr.
  Proof using Type. pin_using tt.
    unfold stdio_frame_stmt. intros l FB m m' W SR MU WM DS DB.
    destruct SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    assert (DSF : forall a n, (0x23e20 <= a /\ a + n <= 0x240f0) \/ (0x54908 <= a /\ a + n <= 0x55130) ->
                  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W).
    { intros a n H. eapply Forall_impl; [| exact DS]. intros [lo hi] [K1 K2]; cbn in *; lia. }
    pose proof SOI as SOI'. pose proof SEI as SEI'.
    destruct SOI as (_ & _ & SObs & _). destruct SEI as (_ & _ & SEbs & _).
    unfold STDIOR. unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD.
    split. { eapply FILE_R_transport; [exact SO | exact MU | exact WM | apply DSF; lia | rewrite SObs; unfold BUFSIZ; apply DSF; lia | rewrite SObs; unfold BUFSIZ; lia]. }
    split; [exact SOI'|].
    split. { eapply FILE_R_transport; [exact SE | exact MU | exact WM | apply DSF; lia | rewrite SEbs; apply DSF; lia | rewrite SEbs; lia]. }
    split; [exact SEI'|].
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact U1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact U2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact U3 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact OL | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split. { eapply rw_cells_transport; [exact OH | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall. apply DSF. lia. }
    split; [| exact ND].
    eapply files_R_transport; [exact FS | exact MU | exact WM | exact DB].
  Qed.

  (* [comment removed for export] *)
  Theorem stdio_init : @stdio_init_stmt hptr.
  Proof using Type. pin_using tt.
    unfold stdio_init_stmt. intros m SO SE SI [bb SOB] SEB U1 U2 U3 OL OH.
    unfold STDIOR, libc_init. cbn [lc_stdout lc_stderr lc_files hd_addr files_R map].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), bb.
      split; [unfold fcells; cbn; exact SO|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SOB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stdout_init]; unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stdout_inv; cbn; repeat split; reflexivity|].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), [].
      split; [unfold fcells; cbn; exact SE|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SEB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stderr_init]; unfold zlength; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stderr_inv; cbn; repeat split; reflexivity|].
    split; [exact SI|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact OL|]. split; [exact OH|].
    split; [exact I|]. constructor.
  Qed.
End Frame.
End TwB.
End Stdio_ifaceP.

(* [comment removed for export] *)
Module Vfprintf_leaf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Crawl.
  Context {St : Type}.
  Notation mleaf := (@mleaf St).

  Lemma mleaf_bind_inv : forall {A B} (m : @M St A) (f : A -> @M St B) s b s'',
    mleaf (mbind m f) s b s'' -> exists a s', mleaf m s a s' /\ mleaf (f a) s' b s''.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). intros. apply mleaf_bind. exact H. Qed.

  Lemma towrite_leaf : forall f st f' st', mleaf (towrite f) st f' st' -> f_nowr f = false /\ f' = set_w true [] (set_rbuf [] f) /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f st f' st' H. unfold towrite in H. destruct (f_nowr f) eqn:E.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma ensure_w_leaf : forall f st f' st', mleaf (ensure_w f) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. split; [apply fx_inv_refl; exact E| reflexivity].
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). split; [apply fx_inv_towrite; exact E| reflexivity].
  Qed.

  Lemma writev_loop_leaf : forall fuel f iovs rem st u st', mleaf (writev_loop fuel f iovs rem) st u st' -> st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction fuel as [|fuel IH]; intros f iovs rem st u st' H; cbn [writev_loop] in H.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (cnt & s1 & H1 & H2).
      destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct (cnt =? rem); [destruct (mleaf_ret _ _ _ _ H2) as [_ ->]; reflexivity | eapply IH; exact H2].
  Qed.

  Lemma stdio_write_leaf : forall f s st f' st', mleaf (stdio_write f s) st f' st' -> f' = set_w true [] f /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold stdio_write in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (u & s1 & H1 & H2).
    pose proof (writev_loop_leaf _ _ _ _ _ _ _ H1) as ->. destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. auto.
  Qed.

  Lemma file_writefn_leaf : forall f s st f' st', mleaf (file_writefn f s) st f' st' ->
    (f' = set_w true [] f \/ f' = set_w true [] (after_ioctl f)) /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold file_writefn in H. destruct (f_stdoutw f).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (r & s1 & H1 & H2). destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct r; [| exfalso; exact (mleaf_unr _ _ _ H2)].
      destruct (stdio_write_leaf _ _ _ _ _ H2) as [-> ->]. auto.
    - destruct (stdio_write_leaf _ _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma fx_inv_after_ioctl_w : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (set_w true [] (after_ioctl f1)).
  Proof using Type. pin_using tt.
    unfold fx_inv, after_ioctl. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn.
    repeat split; auto; intros HH; discriminate HH.
  Qed.

  Lemma fx_inv_trans : forall f0 f1 f2, fx_inv f0 f1 -> fx_inv f1 f2 -> fx_inv f0 f2.
  Proof using Type. pin_using tt.
    unfold fx_inv. intros f0 f1 f2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    rewrite B1, B2, B3, B4, B5, B6, B8, A7. repeat split; auto.
  Qed.

  Lemma file_writefn_leaf_fx : forall f0 f s st f' st', fx_inv f0 f -> mleaf (file_writefn f s) st f' st' -> fx_inv f0 f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f0 f s st f' st' FX H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] ->].
    - split; [apply fx_inv_set_w; exact FX| reflexivity].
    - split; [apply fx_inv_after_ioctl_w; exact FX| reflexivity].
  Qed.

  Lemma fwritex_leaf : forall f s st f' st', mleaf (fwritex f s) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (FX2 : fx_inv f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s); [exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H3)|].
          destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct FX2 as [FX2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. split; [apply fx_inv_set_w; exact FX2| reflexivity].
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. split; [apply fx_inv_set_w; exact FX| reflexivity].
  Qed.

  Lemma out_pieces_leaf : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> (f' = f \/ fx_inv f f') /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (fwritex_leaf _ _ _ _ _ H1) as [FX ->].
      destruct (IH _ _ _ _ H2) as [[-> | FX2] ->]; (split; [right | reflexivity]); [exact FX | exact (fx_inv_trans _ _ _ FX FX2)].
  Qed.

  (* [comment removed for export] *)
  Lemma vfprintf_leaf_buffered : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (out_pieces_leaf _ _ _ _ _ H2) as [[-> | FX2] ->]; split; auto. exact (fx_inv_trans _ _ _ FX FX2).
  Qed.

  (* [comment removed for export] *)
  Definition wl_rel (f f' : file_st) : Prop :=
    (f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f) \/ (f_stdoutw f' = false /\ f_lbf_nl f' = false).
  Lemma wl_rel_refl : forall f, wl_rel f f.
  Proof using Type. pin_using tt. intros f. left. auto. Qed.
  Lemma wl_rel_trans : forall f0 f1 f2, wl_rel f0 f1 -> wl_rel f1 f2 -> wl_rel f0 f2.
  Proof using Type. pin_using tt.
    unfold wl_rel. intros f0 f1 f2 [[A1 A2]|[A1 A2]] [[B1 B2]|[B1 B2]].
    - left. split; congruence. - right. auto. - right. split; congruence. - right. auto.
  Qed.
  Lemma wl_rel_set_w : forall f0 f1 a w, wl_rel f0 f1 -> wl_rel f0 (set_w a w f1).
  Proof using Type. pin_using tt. intros f0 f1 a w R. unfold wl_rel in *. cbn. exact R. Qed.
  Lemma file_writefn_leaf_wl : forall f0 f s st f' st', wl_rel f0 f -> mleaf (file_writefn f s) st f' st' -> wl_rel f0 f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f0 f s st f' st' R H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] _].
    - apply wl_rel_set_w. exact R.
    - unfold wl_rel. cbn. right. auto.
  Qed.
  Lemma ensure_w_leaf_wl : forall f st f' st', mleaf (ensure_w f) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). unfold wl_rel. cbn. left. auto.
  Qed.
  Lemma fwritex_leaf_wl : forall f s st f' st', mleaf (fwritex f s) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). pose proof (ensure_w_leaf_wl _ _ _ _ H1) as R1.
    destruct (ensure_w_leaf _ _ _ _ H1) as [_ ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (R2 : wl_rel f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s).
          - split; [exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H3)|]. exact (proj2 (file_writefn_leaf _ _ _ _ _ H3)).
          - destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct R2 as [R2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. apply wl_rel_set_w. exact R2.
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. apply wl_rel_set_w. exact R1.
  Qed.
  Lemma out_pieces_leaf_wl : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
      exact (wl_rel_trans _ _ _ (fwritex_leaf_wl _ _ _ _ _ H1) (IH _ _ _ _ H2)).
  Qed.
  Lemma vfprintf_leaf_buffered_wl : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
    exact (wl_rel_trans _ _ _ (ensure_w_leaf_wl _ _ _ _ H1) (out_pieces_leaf_wl _ _ _ _ _ H2)).
  Qed.

  (* [comment removed for export] *)
  Definition ubf_rel (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = 0 /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Lemma vfprintf_leaf_unbuffered : forall f ps st f' st', f_bufsize f = 0 ->
    mleaf (vfprintf f ps) st f' st' -> ubf_rel f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f ps st f' st' BS H. unfold vfprintf in H. rewrite BS in H. change (0 =? 0) with true in H. cbv iota in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (towrite_leaf _ _ _ _ H1) as (NW & -> & ->).
    destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
    destruct (mleaf_bind_inv _ _ _ _ _ H4) as (f3 & s3 & H5 & H6).
    destruct (mleaf_ret _ _ _ _ H6) as [-> ->].
    assert (FX1 : fx_inv f (set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) \/ True) by (right; exact I).
    set (g := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) in *.
    assert (G2 : f2 = g \/ fx_inv g f2) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [X _]; exact X).
    assert (S2 : s2 = st) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [_ X]; exact X). subst s2.
    destruct (file_writefn_leaf _ _ _ _ _ H5) as [F3 ->]. split; [| reflexivity].
    assert (K2 : f_fd f2 = f_fd f /\ f_chan f2 = f_chan f /\ f_nord f2 = f_nord f /\ f_nowr f2 = f_nowr f /\ f_eof f2 = f_eof f
                 /\ (f_stdoutw f2 = true -> f_stdoutw f = true) /\ (f_lbf_nl f2 = true -> f_lbf_nl f = true) /\ f_rbuf f2 = []).
    { destruct G2 as [-> | (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10)]; [subst g; cbn; repeat split; auto|].
      subst g. cbn in *. repeat split; auto. }
    destruct K2 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
    unfold ubf_rel. destruct F3 as [-> | ->]; cbn; repeat split; cbn; auto; try congruence; try (intros HH; discriminate HH).
  Qed.
End Crawl.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Crawl.
  Context {St : Type}.
  Notation mleaf := (@mleaf St).

  Lemma mleaf_bind_inv : forall {A B} (m : @M St A) (f : A -> @M St B) s b s'',
    mleaf (mbind m f) s b s'' -> exists a s', mleaf m s a s' /\ mleaf (f a) s' b s''.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). intros. apply mleaf_bind. exact H. Qed.

  Lemma towrite_leaf : forall f st f' st', mleaf (towrite f) st f' st' -> f_nowr f = false /\ f' = set_w true [] (set_rbuf [] f) /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f st f' st' H. unfold towrite in H. destruct (f_nowr f) eqn:E.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma ensure_w_leaf : forall f st f' st', mleaf (ensure_w f) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. split; [apply fx_inv_refl; exact E| reflexivity].
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). split; [apply fx_inv_towrite; exact E| reflexivity].
  Qed.

  Lemma writev_loop_leaf : forall fuel f iovs rem st u st', mleaf (writev_loop fuel f iovs rem) st u st' -> st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction fuel as [|fuel IH]; intros f iovs rem st u st' H; cbn [writev_loop] in H.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (cnt & s1 & H1 & H2).
      destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct (cnt =? rem); [destruct (mleaf_ret _ _ _ _ H2) as [_ ->]; reflexivity | eapply IH; exact H2].
  Qed.

  Lemma stdio_write_leaf : forall f s st f' st', mleaf (stdio_write f s) st f' st' -> f' = set_w true [] f /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold stdio_write in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (u & s1 & H1 & H2).
    pose proof (writev_loop_leaf _ _ _ _ _ _ _ H1) as ->. destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. auto.
  Qed.

  Lemma file_writefn_leaf : forall f s st f' st', mleaf (file_writefn f s) st f' st' ->
    (f' = set_w true [] f \/ f' = set_w true [] (after_ioctl f)) /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold file_writefn in H. destruct (f_stdoutw f).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (r & s1 & H1 & H2). destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct r; [| exfalso; exact (mleaf_unr _ _ _ H2)].
      destruct (stdio_write_leaf _ _ _ _ _ H2) as [-> ->]. auto.
    - destruct (stdio_write_leaf _ _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma fx_inv_after_ioctl_w : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (set_w true [] (after_ioctl f1)).
  Proof using Type. pin_using tt.
    unfold fx_inv, after_ioctl. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn.
    repeat split; auto; intros HH; discriminate HH.
  Qed.

  Lemma fx_inv_trans : forall f0 f1 f2, fx_inv f0 f1 -> fx_inv f1 f2 -> fx_inv f0 f2.
  Proof using Type. pin_using tt.
    unfold fx_inv. intros f0 f1 f2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    rewrite B1, B2, B3, B4, B5, B6, B8, A7. repeat split; auto.
  Qed.

  Lemma file_writefn_leaf_fx : forall f0 f s st f' st', fx_inv f0 f -> mleaf (file_writefn f s) st f' st' -> fx_inv f0 f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f0 f s st f' st' FX H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] ->].
    - split; [apply fx_inv_set_w; exact FX| reflexivity].
    - split; [apply fx_inv_after_ioctl_w; exact FX| reflexivity].
  Qed.

  Lemma fwritex_leaf : forall f s st f' st', mleaf (fwritex f s) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (FX2 : fx_inv f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s); [exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H3)|].
          destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct FX2 as [FX2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. split; [apply fx_inv_set_w; exact FX2| reflexivity].
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. split; [apply fx_inv_set_w; exact FX| reflexivity].
  Qed.

  Lemma out_pieces_leaf : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> (f' = f \/ fx_inv f f') /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (fwritex_leaf _ _ _ _ _ H1) as [FX ->].
      destruct (IH _ _ _ _ H2) as [[-> | FX2] ->]; (split; [right | reflexivity]); [exact FX | exact (fx_inv_trans _ _ _ FX FX2)].
  Qed.

  (* [comment removed for export] *)
  Lemma vfprintf_leaf_buffered : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (out_pieces_leaf _ _ _ _ _ H2) as [[-> | FX2] ->]; split; auto. exact (fx_inv_trans _ _ _ FX FX2).
  Qed.

  (* [comment removed for export] *)
  Definition wl_rel (f f' : file_st) : Prop :=
    (f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f) \/ (f_stdoutw f' = false /\ f_lbf_nl f' = false).
  Lemma wl_rel_refl : forall f, wl_rel f f.
  Proof using Type. pin_using tt. intros f. left. auto. Qed.
  Lemma wl_rel_trans : forall f0 f1 f2, wl_rel f0 f1 -> wl_rel f1 f2 -> wl_rel f0 f2.
  Proof using Type. pin_using tt.
    unfold wl_rel. intros f0 f1 f2 [[A1 A2]|[A1 A2]] [[B1 B2]|[B1 B2]].
    - left. split; congruence. - right. auto. - right. split; congruence. - right. auto.
  Qed.
  Lemma wl_rel_set_w : forall f0 f1 a w, wl_rel f0 f1 -> wl_rel f0 (set_w a w f1).
  Proof using Type. pin_using tt. intros f0 f1 a w R. unfold wl_rel in *. cbn. exact R. Qed.
  Lemma file_writefn_leaf_wl : forall f0 f s st f' st', wl_rel f0 f -> mleaf (file_writefn f s) st f' st' -> wl_rel f0 f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f0 f s st f' st' R H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] _].
    - apply wl_rel_set_w. exact R.
    - unfold wl_rel. cbn. right. auto.
  Qed.
  Lemma ensure_w_leaf_wl : forall f st f' st', mleaf (ensure_w f) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). unfold wl_rel. cbn. left. auto.
  Qed.
  Lemma fwritex_leaf_wl : forall f s st f' st', mleaf (fwritex f s) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). pose proof (ensure_w_leaf_wl _ _ _ _ H1) as R1.
    destruct (ensure_w_leaf _ _ _ _ H1) as [_ ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (R2 : wl_rel f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s).
          - split; [exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H3)|]. exact (proj2 (file_writefn_leaf _ _ _ _ _ H3)).
          - destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct R2 as [R2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. apply wl_rel_set_w. exact R2.
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. apply wl_rel_set_w. exact R1.
  Qed.
  Lemma out_pieces_leaf_wl : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
      exact (wl_rel_trans _ _ _ (fwritex_leaf_wl _ _ _ _ _ H1) (IH _ _ _ _ H2)).
  Qed.
  Lemma vfprintf_leaf_buffered_wl : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> wl_rel f f'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
    exact (wl_rel_trans _ _ _ (ensure_w_leaf_wl _ _ _ _ H1) (out_pieces_leaf_wl _ _ _ _ _ H2)).
  Qed.

  (* [comment removed for export] *)
  Definition ubf_rel (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = 0 /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Lemma vfprintf_leaf_unbuffered : forall f ps st f' st', f_bufsize f = 0 ->
    mleaf (vfprintf f ps) st f' st' -> ubf_rel f f' /\ st' = st.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros f ps st f' st' BS H. unfold vfprintf in H. rewrite BS in H. change (0 =? 0) with true in H. cbv iota in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (towrite_leaf _ _ _ _ H1) as (NW & -> & ->).
    destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
    destruct (mleaf_bind_inv _ _ _ _ _ H4) as (f3 & s3 & H5 & H6).
    destruct (mleaf_ret _ _ _ _ H6) as [-> ->].
    assert (FX1 : fx_inv f (set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) \/ True) by (right; exact I).
    set (g := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) in *.
    assert (G2 : f2 = g \/ fx_inv g f2) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [X _]; exact X).
    assert (S2 : s2 = st) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [_ X]; exact X). subst s2.
    destruct (file_writefn_leaf _ _ _ _ _ H5) as [F3 ->]. split; [| reflexivity].
    assert (K2 : f_fd f2 = f_fd f /\ f_chan f2 = f_chan f /\ f_nord f2 = f_nord f /\ f_nowr f2 = f_nowr f /\ f_eof f2 = f_eof f
                 /\ (f_stdoutw f2 = true -> f_stdoutw f = true) /\ (f_lbf_nl f2 = true -> f_lbf_nl f = true) /\ f_rbuf f2 = []).
    { destruct G2 as [-> | (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10)]; [subst g; cbn; repeat split; auto|].
      subst g. cbn in *. repeat split; auto. }
    destruct K2 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
    unfold ubf_rel. destruct F3 as [-> | ->]; cbn; repeat split; cbn; auto; try congruence; try (intros HH; discriminate HH).
  Qed.
End Crawl.

End WithCeil.
End TwB.
End Vfprintf_leaf.
