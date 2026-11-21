(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_fw_model Z_ukit Z_adler32.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_READBUF_STACK : Z := 48 + 128.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rb1_adler (s : deflate_state) (b : Z) : Z :=
  if ds_wrap s =? 1 then adler32_len1 (cs_adler (ds_strm s)) b else cs_adler (ds_strm s).

Lemma arr_get_of_list_nth : forall l i, 0 <= i -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make. rewrite Z.sub_0_r.
  destruct (Z.ltb_spec i (0 + zlength l)).
  - destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (zlength l)); [|lia]. reflexivity.
  - cbn [andb]. rewrite Bool.andb_false_r. symmetry. apply nth_overflow. unfold zlength in *. lia.
Qed.

Lemma u8arr_join3z : forall m A (b1 b2 b3 : list byte) (k n : Z), Z.of_nat (length b1) = k -> Z.of_nat (length b2) = n ->
  u8arr usegs m A b1 -> rw_cells usegs m (A + k) [CB (Z.to_nat n) b2] -> u8arr usegs m (A + k + n) b3 -> u8arr usegs m A (b1 ++ b2 ++ b3).
Proof.
  intros m A b1 b2 b3 k n L1 L2 H1 H2 H3. apply (u8arr_join3 _ A b1 b2 b3 (Z.to_nat n)); [exact H1| |].
  - rewrite L1. exact H2.
  - rewrite L1. replace (Z.of_nat (Z.to_nat n)) with n by lia. exact H3.
Qed.

Ltac with_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
Ltac name_mem id := with_mem ltac:(fun mm => rename mm into id).

(* [comment removed for export] *)
Ltac join_x9 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode ?A ?x1 (TNode (TNode ?B (Some _) ?C) ?x5 ?D)) None ?E) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut usegs (fun ms' => ms' = MS (TNode (TNode A x1 (TNode (TNode B (Some v) C) x5 D)) None E) F (wz pcj) fc None m rom))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_buf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (X : deflate_state) (more : Z) (inp : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (snd (read_buf X (RB_window (ds_strstart X + ds_lookahead X)) more))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + DS_WIN)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L (fst (read_buf X (RB_window (ds_strstart X + ds_lookahead X)) more)) /\ din m' L inp.

