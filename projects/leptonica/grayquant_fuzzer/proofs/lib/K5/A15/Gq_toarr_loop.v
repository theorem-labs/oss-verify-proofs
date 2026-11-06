(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation TA_W rmap gmap bmap amap n := [(rmap, rmap + 4 * n); (gmap, gmap + 4 * n); (bmap, bmap + 4 * n); (amap, amap + 4 * n)]%Z (only parsing).

(* [comment removed for export] *)
Definition toarr_exit (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (rmap gmap bmap amap n : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a5' a6' a7' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9940c) fc None m' (seg_rom asegs)
    /\ munch (TA_W rmap gmap bmap amap n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma nth_error_ex : forall {X} (l : list X) (i : Z), 0 <= i < Z.of_nat (length l) -> exists x, nth_error l (Z.to_nat i) = Some x.
Proof. intros X l i Hi. destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E; [exists x; reflexivity|]. apply nth_error_None in E. lia. Qed.

Lemma toarr_loop : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 a1 a2 a5 a6 a7 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (arr nal rmap gmap bmap amap pa n : Z) (cbs : list byte) (rs gs bs zs : list word),
  Z.of_nat k = n - i -> 0 <= i -> (1 <= k)%nat -> n <= nal -> nal <= 256 -> 0 < pa < 2^64 ->
  u8arr asegs m arr cbs -> Z.of_nat (length cbs) = 4 * nal -> acc asegs m arr (4 * nal) ->
  0 < arr -> arr mod 8 = 0 -> arr + 4 * nal <= 2^47 -> (arr + 4 * nal <= 0x7fff7000 \/ 0x10007fff8000 <= arr) -> (arr + 4 * nal <= 0x10000 \/ SEGTOP_A <= arr) ->
  u32arr asegs m rmap rs -> Z.of_nat (length rs) = n -> acc asegs m rmap (4 * n) ->
  0 < rmap -> rmap mod 8 = 0 -> rmap + 4 * n <= 2^47 -> (rmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= rmap) -> (rmap + 4 * n <= 0x10000 \/ SEGTOP_A <= rmap) ->
  u32arr asegs m gmap gs -> Z.of_nat (length gs) = n -> acc asegs m gmap (4 * n) ->
  0 < gmap -> gmap mod 8 = 0 -> gmap + 4 * n <= 2^47 -> (gmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= gmap) -> (gmap + 4 * n <= 0x10000 \/ SEGTOP_A <= gmap) ->
  u32arr asegs m bmap bs -> Z.of_nat (length bs) = n -> acc asegs m bmap (4 * n) ->
  0 < bmap -> bmap mod 8 = 0 -> bmap + 4 * n <= 2^47 -> (bmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= bmap) -> (bmap + 4 * n <= 0x10000 \/ SEGTOP_A <= bmap) ->
  u32arr asegs m amap zs -> Z.of_nat (length zs) = n -> acc asegs m amap (4 * n) ->
  0 < amap -> amap mod 8 = 0 -> amap + 4 * n <= 2^47 -> (amap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= amap) -> (amap + 4 * n <= 0x10000 \/ SEGTOP_A <= amap) ->
  (arr + 4 * nal <= rmap \/ rmap + 4 * n <= arr) -> (arr + 4 * nal <= gmap \/ gmap + 4 * n <= arr) ->
  (arr + 4 * nal <= bmap \/ bmap + 4 * n <= arr) -> (arr + 4 * nal <= amap \/ amap + 4 * n <= arr) ->
  (rmap + 4 * n <= gmap \/ gmap + 4 * n <= rmap) -> (rmap + 4 * n <= bmap \/ bmap + 4 * n <= rmap) -> (rmap + 4 * n <= amap \/ amap + 4 * n <= rmap) ->
  (gmap + 4 * n <= bmap \/ bmap + 4 * n <= gmap) -> (gmap + 4 * n <= amap \/ amap + 4 * n <= gmap) -> (bmap + 4 * n <= amap \/ amap + 4 * n <= bmap) ->
  mem_inv asegs m ->
  evt asegs (toarr_exit ra sp gp tp t0 t1 t2 (Z_to_bv 64 pa) (Z_to_bv 64 rmap) (Z_to_bv 64 amap) (Z_to_bv 64 arr) (Z_to_bv 64 gmap) (Z_to_bv 64 bmap)
                        s4 (Z_to_bv 64 (4 * n)) s6 (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6 F fc m rmap gmap bmap amap n)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 pa) (Z_to_bv 64 rmap) (Z_to_bv 64 amap) a1 a2 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 arr) a5 a6 a7
             (Z_to_bv 64 gmap) (Z_to_bv 64 bmap) s4 (Z_to_bv 64 (4 * n)) s6 (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x992d8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 a1 a2 a5 a6 a7 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m arr nal rmap gmap bmap amap pa n cbs rs gs bs zs
    HK HI HK1 HN HNAL HPA UAC UACL ACCC C0 C8_ CHI CSH CSEG
    UAR UARL ACCR R0 R8 RHI RSH RSEG UAG UAGL ACCG G0 G8 GHI GSH GSEG UAB UABL ACCB B0 B8 BHI BSH BSEG UAZ UAZL ACCZ Z0 Z8 ZHI ZSH ZSEG
    SCR SCG SCB SCZ SRG SRB SRZ SGB SGZ SBZ MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (TA_W rmap gmap bmap amap n) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0x9940c; 0x994ac; 0x992f0].
  lwalk [0x99300].
  destruct (nth_error_ex cbs (4 * i + 2) ltac:(lia)) as (b2 & NB2).
  pose proof (u8arr_read asegs m arr cbs (4 * i + 2) b2 _ UAC NB2 ltac:(lia) eq_refl) as R.
  replace (arr + (4 * i + 2)) with (arr + 4 * i + 2) in R by lia.
  lstep. clear R.
  lwalk [0x99308].
  (* [comment removed for export] *)
  unpark RSH. unpark SCR. unpark SRG. unpark SRB. unpark SRZ.
  arr_sw rmap i (rmap + 4 * i).
  park RSH. park SCR. park SRG. park SRB. park SRZ.
  (* [comment removed for export] *)
  lwalk [0x99330].
  destruct (nth_error_ex cbs (4 * i + 1) ltac:(lia)) as (b1 & NB1).
  pose proof (u8arr_read asegs m0 arr cbs (4 * i + 1) b1 _ UAC NB1 ltac:(lia) eq_refl) as R.
  replace (arr + (4 * i + 1)) with (arr + 4 * i + 1) in R by lia.
  lstep. clear R.
  lwalk [0x99338].
  unpark GSH. unpark SCG. unpark SRG. unpark SGB. unpark SGZ.
  arr_sw gmap i (gmap + 4 * i).
  park GSH. park SCG. park SRG. park SGB. park SGZ.
  (* [comment removed for export] *)
  lwalk [0x9935c].
  destruct (nth_error_ex cbs (4 * i) ltac:(lia)) as (b0 & NB0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_read asegs mm arr cbs (4 * i) b0 _ UAC NB0 ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  lwalk [0x99364].
  unpark BSH. unpark SCB. unpark SRB. unpark SGB. unpark SBZ.
  arr_sw bmap i (bmap + 4 * i).
  park BSH. park SCB. park SRB. park SGB. park SBZ.
  (* [comment removed for export] *)
  lwalk [0x99390; 0x992d0].
  destruct (nth_error_ex cbs (4 * i + 3) ltac:(lia)) as (b3 & NB3).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_read asegs mm arr cbs (4 * i + 3) b3 _ UAC NB3 ltac:(lia) eq_refl) as R end.
  replace (arr + (4 * i + 3)) with (arr + 4 * i + 3) in R by lia.
  lstep. clear R.
  lwalk [0x992cc].
  unpark ZSH. unpark SCZ. unpark SRZ. unpark SGZ. unpark SBZ.
  arr_sw amap i (amap + 4 * i).
  park ZSH. park SCZ. park SRZ. park SGZ. park SBZ.
  lwalk [0x992d8; 0x9940c].
  replace (4 * i + 4) with (4 * (i + 1)) by lia.
  destruct k as [|k].
  - assert (EI : i + 1 = n) by lia. rewrite EI in *.
    brT. apply evt_done. unfold toarr_exit. do 6 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM| exact MI].
  - brF.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (nal := nal) (cbs := cbs) (pa := pa); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold toarr_exit in PO |- *.
      destruct PO as (a1' & a2' & a3' & a5' & a6' & a7' & m' & E & MU' & WM' & MI').
      exists a1', a2', a3', a5', a6', a7', m'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact MI'].
Qed.
