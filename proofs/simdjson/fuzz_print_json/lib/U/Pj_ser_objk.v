(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require F_printf_core_common.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_cont_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Notation M32M1 := 4294967295%Z.
Notation M32P1 := 4294967297%Z.
Notation M32M8 := 4294967288%Z.
Notation M4020 := 67240448%Z.
Notation M56 := 72057594037927935%Z.
Notation NNETZ := 18446744073709472427%Z.
Notation LITQUZ := 72159%Z.
Notation LITQU2Z := 72161%Z.
Notation LITBSZ := 69679%Z.
Notation LITBS2Z := 69681%Z.
Notation ESCZ := 79444%Z.
Notation NETZ := 79188%Z.

Lemma land_m8_32 : forall l, 0 <= l < 2^32 -> Z.land l 4294967288 = Z.land l 18446744073709551608.
Proof.
  intros l H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. rewrite Z.land_spec.
  destruct (Z.ltb_spec n 32) as [L|L].
  - apply (f_equal2 andb); [reflexivity|].
    replace 4294967288 with (Z.shiftl (Z.ones 29) 3) by reflexivity.
    replace 18446744073709551608 with (Z.shiftl (Z.ones 61) 3) by reflexivity.
    rewrite (Z.shiftl_spec (Z.ones 29)), (Z.shiftl_spec (Z.ones 61)) by lia.
    destruct (Z.ltb_spec n 3) as [L3|L3].
    + rewrite (Z.testbit_neg_r (Z.ones 29)) by lia. rewrite (Z.testbit_neg_r (Z.ones 61)) by lia. reflexivity.
    + rewrite (Z.ones_spec_low 29) by lia. rewrite (Z.ones_spec_low 61) by lia. reflexivity.
  - assert (T : Z.testbit l n = false).
    { destruct (Z.eq_dec l 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32; [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite T. cbn [andb]. reflexivity.
Qed.
Lemma land_m8_32_range : forall l, 0 <= l < 2^32 -> 0 <= Z.land l 4294967288 <= l.
Proof. intros l H. rewrite land_m8_32 by exact H. apply land_m8_range. lia. Qed.

Definition c8c (c : cell) : cell := match c with CB n bs => if Nat.eqb n 8 then C8 (le_bytes_to_word bs) else c | _ => c end.

Lemma c8ify_ok : forall cs, cells_wf cs ->
  cells_wf (map c8c cs) /\ cells_bytes (map c8c cs) = cells_bytes cs /\ cells_size (map c8c cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros Hwf; [repeat split; reflexivity|].
  destruct Hwf as [Hc Hcs]. destruct (IH Hcs) as (W & B & S).
  destruct c as [v|v|v|b|n bs]; cbn [map c8c cells_wf cells_bytes cells_size]; try (rewrite B, S; repeat split; auto; fail).
  destruct (Nat.eqb_spec n 8) as [->|NE]; cbn [cells_wf cells_bytes cells_size cbytes csize cell_wf]; rewrite B, S.
  - cbn in Hc. rewrite (F_printf_core_common.le8_of_bytes bs Hc). repeat split; auto.
  - repeat split; auto.
Qed.

Lemma rw_cells_c8ify : forall m A cs, rw_cells usegs m A cs -> rw_cells usegs m A (map c8c cs).
Proof.
  intros m A cs [[Hwf Hb] Hw]. destruct (c8ify_ok cs Hwf) as (W & B & S).
  split; [split; [exact W| rewrite B; exact Hb]| rewrite S; exact Hw].
Qed.

Lemma lowbyte_shl : forall v k, 8 <= k -> Z.land (Z.shiftl v k) 255 = 0.
Proof.
  intros v k Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec n 8) as [L|L].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - replace 255 with (Z.ones 8) by reflexivity. rewrite Z.ones_spec_high by lia. apply Bool.andb_false_r.
Qed.
Lemma land64_255 : forall X, Z.land (Z.land X 18446744073709551615) 255 = Z.land X 255.
Proof. intros X. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma land255_u8 : forall b, 0 <= b < 256 -> Z.land b 255 = b.
Proof. intros b H. replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac low_byte :=
  rewrite ?Z.land_lor_distr_l; rewrite ?land64_255; rewrite ?Z.land_lor_distr_l; rewrite ?land64_255;
  rewrite ?lowbyte_shl by lia; rewrite ?Z.lor_0_l, ?Z.lor_0_r; rewrite ?land255_u8 by lia.

Notation OST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (Z_to_bv 64 (e_q E + -208)) (e_gp E) (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 (e_SB E)) xs1
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Definition obj_saved (E : senv) : list cell :=
  [C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition obj_frame (E : senv) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 : word) (m : mem) : Prop :=
  rw_cells usegs m (e_q E + -208) [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88]
  /\ stk usegs m (e_q E + -112) (e_q E + -104)
  /\ rw_cells usegs m (e_q E + -104) (obj_saved E).

Lemma obj_frame_local : forall E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88,
  frame_local E (e_q E + -208) (obj_frame E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88).
Proof.
  intros E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 m m' AG (FA & FT & FS). unfold obj_frame.
  split; [| split].
  - eapply rw_cells_agree; [exact AG| exact FA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. lia.
  - eapply stk_agree; [exact AG| exact FT|]. intros a Ha. cbv beta. lia.
  - eapply rw_cells_agree; [exact AG| exact FS|]. intros a Ha. unfold obj_saved in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. lia.
Qed.

Lemma obj_frt_src : forall E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 st s m Src n,
  CERM E (e_q E + -208) (obj_frame E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88) st s m ->
  e_q E + -112 <= Src -> 0 <= n -> Src + n <= e_q E + -104 ->
  exists src, bytes_at usegs m Src src /\ length src = Z.to_nat n.
Proof.
  intros E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 st s m Src n [_ ((_ & FT & _) & _)] H1 Hn H2.
  eapply stk_src; [exact FT| lia| lia| lia].
Qed.

End WithCeiling0.

Notation OBM E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 := (CERM E (e_q E + -208) (obj_frame E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88)).

Ltac obj_open HM OK :=
  cont_open HM OK;
  match goal with H : obj_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold obj_frame, obj_saved in H; destruct H as (FRA & FRT & FRS) end.

Ltac obj_close HM OK :=
  match goal with
  | FRA : rw_cells _ ?m (e_q ?E + -208) [C8 ?v0; C8 ?v8; C8 ?v16; C8 ?v24; C8 ?v32; C8 ?v40; C8 ?v48; C8 ?v56; C8 ?v64; C8 ?v72; C8 ?v80; C8 ?v88],
    FRT : stk _ ?m (e_q ?E + -112) _, FRS : rw_cells _ ?m (e_q ?E + -104) _ |- _ =>
      let H := fresh "HFRP" in
      first [ assert (H : obj_frame E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 m) by (exact (conj FRA (conj FRT FRS)))
            | fail 100 "obj_close: cannot rebuild the frame" ];
      clear FRA FRT FRS;
      cont_close (e_q E + -208) (obj_frame E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88) HM OK
  | _ => fail 100 "obj_close: no frame pieces FRA FRT FRS about the current memory"
  end.
