(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names, addresses and numbers changed; 343 of its 388 lines of code are new or changed and 351 lines of the source are left out. *)
(* Segment F28a of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A): the port-slot loop of the inlined
   check_ports, 0x8265c-0x826d0 (head 0x8265c, 12 turns, a5 counts down from 12). Each turn does the instrumented
   check of the byte blk[8 + i] at a0 = a4 = Φ + 26 + i (the load of the shadow byte at (a0 >> 3) + s10 and, when it
   is not 0, the compare of a0 mod 8 with it at 0x826c8-0x826d0); the branch to the error path (0x82c98) is not taken
   because the bytes Φ + 26 .. Φ + 37 are addressable (HB(Φ) with 50 <= flen). It then loads the code c and counts
   codes {00, 02} into a2, code 01 into a1, code 03 into a3, and keeps the first code >= 4 in a6 / a7 (the plain
   twin's Q05). After the last turn `j 0x826d4` reaches the exit cut Inv_A826d4_at (the entry is Inv_A8265c_at;
   both official SlotInv.v cuts). The loop is proved by induction on the down-counter inside seg_F28a. No memory
   is written, so FRA moves by sl_fra_move, the entry relation ENT by ent_mat and FLSI by b7_flsi_regs. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot B7Cuts.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.

(* ---- Model facts of the plain twin (Tac_b7.v, Q05.v), proofs unchanged ---- *)

Lemma b7_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  exact R.
Qed.

Lemma b7_uzxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* A boolean fact checked for every byte value. *)
Lemma b7_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall u, 0 <= u < 256 -> P u = true.
Proof.
  intros P H u Hu. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat u).
  split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma b7_eqb : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2 ^ 64 =? y mod 2 ^ 64).
Proof. intros x y. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

Lemma b7_eqb_small : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. rewrite b7_eqb, !Z.mod_small by lia. reflexivity. Qed.

Lemma b7_nunk_nonneg : forall bs k, 0 <= RcPorts.pu_nunk bs k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

(* C5.5 / C5.7: the first unknown code is 0 exactly when there is none, and is a byte. *)
Lemma b7_first_spec : forall bs k,
  (RcPorts.pu_first bs k = 0 <-> RcPorts.pu_nunk bs k = 0) /\ 0 <= RcPorts.pu_first bs k < 256.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_first RcPorts.pu_nunk]; [lia|].
  pose proof (b7_nunk_nonneg bs k).
  pose proof (bv_unsigned_in_range 8 (nth (8 + k) bs (Z_to_bv 8 0))) as R. unfold RcPorts.rc_u8.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  set (c := bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) in *.
  destruct IH as [IH1 IH2].
  destruct (Z.eqb_spec (RcPorts.pu_nunk bs k) 0); destruct (Z.leb_spec 4 c); cbn [andb]; lia.
Qed.

Lemma b7_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma b7_nth_firstn : forall (l : list byte) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros n k d Hk.
  - rewrite firstn_nil. destruct k; reflexivity.
  - destruct n as [|n]; [lia|]. destruct k as [|k]; [reflexivity|].
    cbn [firstn nth]. apply IH. lia.
Qed.

(* blk = Φ + 18 holds t_blk (32 bytes); its first 20 bytes are t_pbs. *)
Lemma b7_blk_length : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk, RcFrag.bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. reflexivity. Qed.

Lemma b7_blk_pbs : forall inp j k, (k < 20)%nat ->
  nth k (t_blk inp j) (Z_to_bv 8 0) = nth k (t_pbs inp j) (Z_to_bv 8 0).
Proof.
  intros inp j k Hk. unfold t_blk, t_pbs, RcFrag.bsl.
  rewrite !b7_nth_firstn by (cbn; lia). reflexivity.
Qed.

(* One code c of the loop (AF4): the three counters and the first unknown code. *)
Lemma b7_in : forall c : byte,
  bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (zxb c)) 253)) 1) =
  if RcLeaf.is_in (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite b7_uzxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (Z.land u 253)) 1))
                                      (if RcLeaf.is_in u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma b7_out : forall c : byte,
  bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -1)) 1) =
  if RcLeaf.is_out (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite b7_uzxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (u + -1)) 1))
                                      (if RcLeaf.is_out u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma b7_emp : forall c : byte,
  bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -3)) 1) =
  if is_empty (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite b7_uzxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (u + -3)) 1))
                                      (if is_empty u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma b7_snez : forall f, 0 <= f < 256 ->
  bv_unsigned (PropExec.v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))) =
  if f =? 0 then 0 else 1.
Proof.
  intros f R.
  pose proof (b7_all (fun f => Z.eqb (bv_unsigned (PropExec.v_sltu (Z_to_bv 64 0)
                                  (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                                      (if f =? 0 then 0 else 1)) ltac:(vm_compute; reflexivity) f R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma b7_known : forall c : byte,
  bv_unsigned (PropExec.v_sltiu (zxb c) 4) = if 4 <=? bv_unsigned c then 0 else 1.
Proof.
  intros c. unfold zxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 u) 4))
                                      (if 4 <=? u then 0 else 1)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

(* beqz t1 at 0x82684 with t1 = (zext.b first != 0) | (c <u 4). *)
Lemma b7_brc : forall f (c : byte), 0 <= f < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (PropExec.v_sltu (Z_to_bv 64 0)
                                            (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                             (bv_unsigned (PropExec.v_sltiu (zxb c) 4))))
         (Z_to_bv 64 0) = (f =? 0) && (4 <=? bv_unsigned c).
Proof.
  intros f c Hf. rewrite (b7_snez f Hf), b7_known.
  destruct (f =? 0), (4 <=? bv_unsigned c); vm_compute; reflexivity.
Qed.

Definition b7_f (f u : Z) : Z := if (f =? 0) && (4 <=? u) then u else f.

Lemma b7_first_step : forall bs i,
  b7_f (RcPorts.pu_first bs i) (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) = RcPorts.pu_first bs (S i).
Proof.
  intros bs i. cbn [RcPorts.pu_first]. unfold b7_f, RcPorts.rc_u8.
  destruct (b7_first_spec bs i) as ((E1 & E2) & _).
  destruct (Z.eqb_spec (RcPorts.pu_first bs i) 0) as [F0|F0];
    destruct (Z.eqb_spec (RcPorts.pu_nunk bs i) 0) as [N0|N0]; cbn [andb]; try reflexivity; exfalso; tauto.
Qed.

(* ---- The instrumented check of one addressable byte X ---- *)

(* The shadow byte b at (X >> 3) + ASAN_K is readable and passes the check (b = 0, or X mod 8 < b). *)
Lemma f28_shadow : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* `bnez shadow, slow`: the fast path (shadow byte 0) and the slow path (`andi t0,a0,7; bge t0,a7,error path;
   j back`, the branch to the error path not taken because X mod 8 < b) rejoin at `cont`; the scratch register is
   generalised. Leaves the goal `forall rr, evt .. cont`. *)
Ltac converge scratch Xe b OK BD :=
  match goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr : word, evt segs Q (MS (@bvmap_set 5 word scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota; step; step;
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (unsigned_lit Xe) by (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota; step;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

(* Replace the condition of the branch at the head of the goal by its value. *)
Ltac f28_br v pf :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v by (symmetry; pf); cbv_concl_iota
  end.

Ltac f28_zdec :=
  repeat match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end; cbn [negb andb orb]; first [reflexivity | exfalso; lia].

(* 0x8265c -> 0x826c0: one turn of the port-slot loop on the code c at A (a0 = a4 = A, a5 = N). *)
Lemma f28_body :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A N x1 x2 x3 f : Z) (c : byte),
    a0 = Z_to_bv 64 A -> a4 = Z_to_bv 64 A -> a5 = Z_to_bv 64 N -> a1 = Z_to_bv 64 x1 -> a2 = Z_to_bv 64 x2 ->
    a3 = Z_to_bv 64 x3 -> a6 = Z_to_bv 64 f -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= f < 256 -> addressable m A 1 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [c] ->
    evt rsegs
      (fun ms' => exists t0' t1' : word,
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (A + 1))
                       (Z_to_bv 64 (x1 + if RcLeaf.is_out (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x2 + if RcLeaf.is_in (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x3 + if is_empty (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (A + 1)) (Z_to_bv 64 (N + -1))
                       (Z_to_bv 64 (b7_f f (bv_unsigned c))) (Z_to_bv 64 (b7_f f (bv_unsigned c)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x826c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8265c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A N x1 x2 x3 f c -> -> -> -> -> -> -> -> Hf Had Hrd.
  pose proof Had as Had'. destruct Had' as (HA0 & _ & HA1 & _).
  destruct (f28_shadow m A Had) as (b & HRsh & OK & BD).
  (* 0x8265c srli a7,a0,3 ; add a7,a7,s10 ; lb a7,0(a7) (the shadow byte) ; bnez a7,0x826c8 *)
  step. step.
  rewrite (unsigned_lit A) by (unfold APPMEM_END in *; lia).
  step. step.
  converge (Z_to_bv 5 5) A b OK BD.
  (* 0x8266c lbu t0,0(a4) ; zext.b a7,a6 ; sltiu t1,t0,4 ; snez a7,a7 ; or t1,a7,t1 ; mv a7,t0 ; beqz t1 *)
  do 7 step.
  rewrite (b7_brc f c Hf).
  destruct ((f =? 0) && (4 <=? bv_unsigned c)) eqn:Ec; cbv_concl_iota.
  - do 13 step. rewrite b7_in, b7_out, b7_emp.
    apply evt_done. hnf. eexists _, _. unfold b7_f. rewrite Ec. reflexivity.
  - do 14 step. rewrite b7_in, b7_out, b7_emp.
    apply evt_done. hnf. eexists _, _. unfold b7_f. rewrite Ec. reflexivity.
Qed.

(* The same turn on the model: the code is blk[8 + i] of bs, the counters are the counts over the first i codes. *)
Lemma f28_turn :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (i : nat) (A N : Z),
    a0 = Z_to_bv 64 A -> a4 = Z_to_bv 64 A -> a5 = Z_to_bv 64 N ->
    a1 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs i) -> a2 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs i) ->
    a3 = Z_to_bv 64 (RcLeaf.cnt is_empty bs i) -> a6 = Z_to_bv 64 (RcPorts.pu_first bs i) ->
    s10 = Z_to_bv 64 ASAN_K -> addressable m A 1 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [nth (8 + i) bs (Z_to_bv 8 0)] ->
    evt rsegs
      (fun ms' => exists t0' t1' : word,
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (A + 1))
                       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs (S i)))
                       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs (S i)))
                       (Z_to_bv 64 (RcLeaf.cnt is_empty bs (S i)))
                       (Z_to_bv 64 (A + 1)) (Z_to_bv 64 (N + -1))
                       (Z_to_bv 64 (RcPorts.pu_first bs (S i))) (Z_to_bv 64 (RcPorts.pu_first bs (S i)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x826c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8265c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs i A N E0 E4 E5 E1 E2 E3 E6 E26 Had Hrd.
  destruct (b7_first_spec bs i) as (_ & Hf).
  eapply evt_mono.
  { exact (f28_body ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m A N _ _ _ _ _ E0 E4 E5 E1 E2 E3 E6 E26 Hf Had Hrd). }
  intros ms' (t0' & t1' & ->). exists t0', t1'.
  rewrite <- (b7_first_step bs i). reflexivity.
Qed.

Section F28a.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma f28_rg : forall regs regs' r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v.
Proof. intros regs regs' r v E H. unfold rg in *. rewrite E. exact H. Qed.

Lemma f28_spill : forall regs regs' m off v, getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. split; [exact (f28_rg regs regs' 9 A E HA) | exact Hq]. Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map. *)
Lemma f28_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma seg_F28a : forall j : nat,
  Hat B APIf ra (Inv_A826d4_at B APIf ra) j -> Hat B APIf ra (Inv_A8265c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hj & HHB & HFLSI & HK &
    Hrp & Hunk & Hs4 & Ht2 & HPO & HFI & Ha0 & Ha4 & Ha5 & Ha1 & Ha2 & Ha3 & Ha6).
  subst c. rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Af & spf & s5f & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hrest).
  pose proof HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hfl & Hblk & Hsum & H24 & HSPL).
  (* the 12 codes blk[8 .. 20) = Φ + 26 .. Φ + 37, and their addressable range from HB(Φ) *)
  assert (HR : forall k, (k < 12)%nat ->
    ov_read_bytes rsegs mem (Z_to_bv 64 (phi + 26 + Z.of_nat k)) 1 =
    Some [nth (8 + k) (t_pbs (g_in g) j) (Z_to_bv 8 0)]).
  { intros k Hk.
    pose proof (ULMem.bytes_at_ov_read rsegs mem (phi + 18) (t_blk (g_in g) j) (8 + k) 1 Hblk
                  ltac:(rewrite b7_blk_length; lia)) as E.
    rewrite (b7_firstn1 _ _ (Z_to_bv 8 0)) in E by (rewrite b7_blk_length; lia).
    rewrite b7_blk_pbs in E by lia.
    replace (phi + 18 + Z.of_nat (8 + k)) with (phi + 26 + Z.of_nat k) in E by lia.
    exact E. }
  assert (HAd : forall k, (k < 12)%nat -> addressable mem (phi + 26 + Z.of_nat k) 1).
  { intros k Hk. destruct HHB as (_ & Haddr). unfold AC.a_size in Haddr.
    replace (phi + 26 + Z.of_nat k) with (phi + (26 + Z.of_nat k)) by lia.
    apply (addressable_sub mem phi (Z.max (flen g j) 1)); [exact Haddr | lia | lia | lia]. }
  (* the loop, by induction on the down-counter a5 = n (turn i = 12 - n), for any code list bs read at Φ + 26 *)
  assert (LOOP : forall bs : list byte,
      (forall k, (k < 12)%nat ->
         ov_read_bytes rsegs mem (Z_to_bv 64 (phi + 26 + Z.of_nat k)) 1 = Some [nth (8 + k) bs (Z_to_bv 8 0)]) ->
      forall (n i : nat)
      (x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
      (i + n = 12)%nat -> (0 < n)%nat ->
      a0 = Z_to_bv 64 (phi + 26 + Z.of_nat i) -> a4 = Z_to_bv 64 (phi + 26 + Z.of_nat i) ->
      a5 = Z_to_bv 64 (Z.of_nat n) ->
      a1 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs i) -> a2 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs i) ->
      a3 = Z_to_bv 64 (RcLeaf.cnt is_empty bs i) -> a6 = Z_to_bv 64 (RcPorts.pu_first bs i) ->
      s10 = Z_to_bv 64 ASAN_K ->
      evt rsegs
        (fun ms' => exists t0' t1' a0' a4' a5' a6' : word,
           ms' = MS (mkR x1 x2 x3 x4 t0' t1' t2 s0 s1 a0' (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs 12))
                         (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs 12)) (Z_to_bv 64 (RcLeaf.cnt is_empty bs 12))
                         a4' a5' a6' (Z_to_bv 64 (RcPorts.pu_first bs 12))
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    fp_regs (Z_to_bv 64 0x826d4) fp_csr None mem (seg_rom rsegs))
        (MS (mkR x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            fp_regs (Z_to_bv 64 0x8265c) fp_csr None mem (seg_rom rsegs))).
  { intros bs HRb n. induction n as [|n IH];
      intros i x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        Hin Hpos E0 E4 E5 E1 E2 E3 E6 E26; [lia|].
    eapply evt_cut.
    { exact (f28_turn x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               fp_regs fp_csr mem bs i (phi + 26 + Z.of_nat i) (Z.of_nat (S n))
               E0 E4 E5 E1 E2 E3 E6 E26 (HAd i ltac:(lia)) (HRb i ltac:(lia))). }
    intros ms' (t0' & t1' & ->).
    (* 0x826c0 bnez a5,0x8265c *)
    step.
    destruct n as [|n'].
    - (* last turn: fall through, j 0x826d4 *)
      f28_br false ltac:(rewrite b7_eqb_small by lia; f28_zdec).
      step.
      assert (Ei : i = 11%nat) by lia. subst i.
      apply evt_done. hnf. do 6 eexists. reflexivity.
    - f28_br true ltac:(rewrite b7_eqb_small by lia; f28_zdec).
      eapply (IH (S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia
                         | reflexivity | reflexivity | reflexivity | reflexivity | exact E26]. }
  apply (sl_run regs (Z_to_bv 64 0x8265c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x826d4 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 7 = getr regs 7 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\
       getr R 11 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out (t_pbs (g_in g) j) 12) /\
       getr R 12 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in (t_pbs (g_in g) j) 12) /\
       getr R 13 = Z_to_bv 64 (RcLeaf.cnt is_empty (t_pbs (g_in g) j) 12) /\
       getr R 17 = Z_to_bv 64 (RcPorts.pu_first (t_pbs (g_in g) j) 12))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f28_mkR_of_expand.
    eapply evt_mono.
    { eapply (LOOP (t_pbs (g_in g) j) HR 12%nat 0%nat);
        [ lia | lia
        | unfold rg in Ha0; rewrite Ha0; f_equal; lia
        | unfold rg in Ha4; rewrite Ha4; f_equal; lia
        | exact Ha5 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha6 | exact Hr26 ]. }
    intros ms' (t0' & t1' & a0' & a4' & a5' & a6' & ->).
    do 3 eexists. split; [reflexivity|].
    repeat (apply conj; [reflexivity|]). reflexivity.
  - intros R pc' mem' regs' md'
      (-> & -> & E2 & E3 & E4 & E7 & E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E26 & E18 & K11 & K12 & K13 & K17)
      Hreg Hmat.
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem, md', fr.
    rewrite ?Hasz.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs' mem md md' HFRA);
        [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
        | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
        | rewrite Hreg; exact E26 | exact Hmat ]. }
    split; [exact (ent_mat APIf g (hb1 phi (flen g j)) mem md md' HENT Hmat)|].
    split; [exact Hn|].
    split; [exact Hj|].
    split; [exact HHB|].
    split; [apply (b7_flsi_regs g j fr regs regs' mem HFLSI); rewrite Hreg; exact E9|].
    split.
    { apply (b7_B7K_regs g j phi fr regs regs' mem HK);
        [ rewrite Hreg; exact E9 | rewrite Hreg; exact E18 | rewrite Hreg; exact E21 | rewrite Hreg; exact E22
        | rewrite Hreg; exact E23 | rewrite Hreg; exact E24 ]. }
    split; [exact Hrp|].
    split; [exact Hunk|].
    split; [unfold rg; rewrite Hreg, E20; exact Hs4|].
    split; [unfold rg; rewrite Hreg, E7; exact Ht2|].
    split; [exact HPO|].
    split; [exact HFI|].
    split; [unfold rg, RcLeaf.n_in; rewrite Hreg; exact K12|].
    split; [unfold rg, RcLeaf.n_out; rewrite Hreg; exact K11|].
    split; [unfold rg; rewrite Hreg; exact K13|].
    unfold rg; rewrite Hreg; exact K17.
Qed.

End F28a.
