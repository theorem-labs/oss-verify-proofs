(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_defl_iface Z_defl_path Zg_defl_path.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz DeflateBlk Deflate DeflateSafe DeflateParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition ZL_SLIDE_HASH : Z := 0x18464.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slide_hash_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ DST m' L (slide_hash d).

Definition slide_hash_stmt : Prop :=
  forall (L : dlay) (d : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L d -> mem_inv usegs m ->
  ds_w_size d = 32768 -> ds_hash_size d = 32768 ->
  (forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_head d) i < 65536) ->
  (forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_prev d) i < 65536) ->
  a0 = wz (dl_As L) ->
  evt usegs (slide_hash_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ZL_SLIDE_HASH) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZL_DEFLATEPARAMS : Z := 0x16fd4.
Definition Z_DPARAMS_STACK : Z := 64 + Z_DEFLATE_IN_STACK.

(* [comment removed for export] *)
Definition dparams_lv (level strategy : Z) (R : deflate_state * Z) (X : deflate_state) : Prop :=
  0 <= ds_level X <= 9 /\ 0 <= ds_matches X < 2^31
  /\ (ds_level X = level -> R = (set_strategy X strategy, 0))
  /\ (ds_level X <> level ->
      (ds_level X = 0 -> ds_matches X <> 0 ->
         ds_w_size X = 32768 /\ ds_hash_size X = 32768
         /\ (forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_head X) i < 65536)
         /\ (forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_prev X) i < 65536))
      /\ R = (set_strategy (dparams_set_level X level) strategy, 0)).

Definition dparams_path (inp : list Z) (level strategy : Z) (R : deflate_state * Z) (d : deflate_state) : Prop :=
  (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666)
  /\ 0 <= ds_level d <= 9 /\ 0 <= ds_strategy d < 2^31 /\ - 2 <= ds_last_flush d <= 5
  /\ 0 <= level <= 9 /\ 0 <= strategy <= 1
  /\ (dparams_flushes d level strategy = true ->
      let X1 := fst (deflate_core d 5) in
      defl_pathg inp 5 (deflate_core d 5) d
      /\ 0 <= cs_avail_in (ds_strm X1) < 2^31 /\ 0 <= ds_strstart X1 < 2^32 /\ 0 <= ds_lookahead X1 < 2^32
      /\ - 2^62 <= ds_block_start X1 < 2^62
      /\ (length (cs_out_rev (ds_strm X1)) <= length (cs_out_rev (ds_strm (fst R))))%nat
      /\ - 5 <= snd (deflate_core d 5) <= 1
      /\ (snd (deflate_core d 5) = -2 -> R = (X1, -2))
      /\ (snd (deflate_core d 5) <> -2 ->
          (cs_avail_in (ds_strm X1) <> 0 \/ (ds_strstart X1 - ds_block_start X1) + ds_lookahead X1 <> 0) -> R = (X1, -5))
      /\ (snd (deflate_core d 5) <> -2 -> cs_avail_in (ds_strm X1) = 0 -> (ds_strstart X1 - ds_block_start X1) + ds_lookahead X1 = 0 ->
          dparams_lv level strategy R X1))
  /\ (dparams_flushes d level strategy = false -> dparams_lv level strategy R d).

Definition deflateParams_in_stmt : Prop :=
  forall (L : dlay) (d : deflate_state) (level strategy : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> dout m L rest0 (ds_strm d) -> mem_inv usegs m -> relro_clean m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DPARAMS_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  dparams_path inp level strategy (deflateParams_core d level strategy) d ->
  (length (cs_out_rev (ds_strm (fst (deflateParams_core d level strategy)))) <= length rest0)%nat ->
  a0 = wz (dl_S L) -> a1 = wz level -> a2 = wz strategy ->
  evt usegs (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L
               (fst (deflateParams_core d level strategy)) (snd (deflateParams_core d level strategy)) inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ZL_DEFLATEPARAMS) fc None m (seg_rom usegs)).
