From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct strtod_c.
Import ListNotations.
Open Scope Z_scope.

Definition EX_VALUE : Z := 0x143bc.
Definition EX_VALUE_FE : Z := 128.
Definition EX_VALUE_KC : Z := 8928.
Definition ex_value_K (d : Z) : Z := (33 - d) * EX_VALUE_FE + EX_VALUE_KC.

Definition ex_sm (txt : list Z) : Z * Z :=
  match strtod_model txt with Some (bits, c) => (c, bits) | None => (0, 0) end.

Definition ex_V (d : Z) (xs : list Z) : option (jv * list Z) :=
  fst (fst (jr_value ex_sm (Z.to_nat d) xs [])).

Definition ex_apart (a n b k : Z) : Prop := n <= 0 \/ k <= 0 \/ a + n <= b \/ b + k <= a.

Definition ex_off (v : Z) (D : list (Z * Z)) (b k : Z) : Prop :=
  ex_apart v 56 b k /\ Forall (fun ak => ex_apart (fst ak) (snd ak) b k) D.

Definition ex_rec (m : word -> option byte) (q p e dep scr dif : Z) : Prop :=
  rw_cells rsegs m q [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 e); C4 (Z_to_bv 64 dep)] /\
  rw_cells rsegs m (q + 24) [C8 (Z_to_bv 64 scr); C4 (Z_to_bv 64 dif)].

Definition ex_fkeep (F F' : bvmap 5 word) : Prop :=
  forall k : bv 5, In (bv_unsigned k) [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> reg_get F' k = reg_get F k.

Definition ex_value_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (m : word -> option byte) (q v x0 i0 d dl scr lo : Z) (x : list byte) (t : jv) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte) (p' d' dl' : Z) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    ex_fkeep F F' /\ frm0 fc' /\
    munch [(bv_unsigned sp - ex_value_K d, bv_unsigned sp); (q, q + 8); (q + 16, q + 20); (q + 32, q + 36);
           (scr, scr + Z.of_nat (length x) + 1); (STRTOD_ERRNO, STRTOD_ERRNO + 4)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' STRTOD_ERRNO [C4 ev'] /\
    ex_rec m' q (x0 + p') (x0 + Z.of_nat (length x)) d' scr dl' /\ (dl' = 0 \/ dl' = 1) /\
    match ex_V d (map bv_unsigned (skipn (Z.to_nat i0) x)) with
    | None => r = Z_to_bv 64 (-1) /\ 0 <= p' <= Z.of_nat (length x) /\ d <= d' <= 33
    | Some (u, rest) =>
        r = Z_to_bv 64 0 /\ p' = Z.of_nat (length x) - Z.of_nat (length rest) /\ d' = d /\
        stk rsegs m' scr (scr + Z.of_nat (length x) + 1) /\
        (dl' = 1 <-> dl = 1 \/ (v <> 0 /\ t <> u))
    end.

Definition ex_value_spec (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q v x0 i0 d dl scr lo : Z) (x : list byte)
    (lblk : Z -> Z -> Prop) (t : jv) (D : list (Z * Z)) (canary ev : word) : Prop :=
  let len := Z.of_nat (length x) in
  let W0 := bv_unsigned sp - ex_value_K d in
  a0 = Z_to_bv 64 q -> a1 = Z_to_bv 64 v -> tp = Z_to_bv 64 STRTOD_TP ->
  ex_rec m q (x0 + i0) (x0 + len) d scr dl -> q mod 8 = 0 -> STRTOD_GLOBALS_TOP <= q ->
  bytes_at rsegs m x0 x -> 0 < x0 -> x0 + len < 2 ^ 62 -> len <= 3 * 2 ^ 20 ->
  0 <= i0 <= len -> 0 <= d <= 32 -> (dl = 0 \/ dl = 1) ->
  stk rsegs m scr (scr + len + 1) -> 4096 <= scr -> scr + len + 1 <= STRTOD_IMG_LO \/ STRTOD_GLOBALS_TOP <= scr ->
  scr + len + 1 <= W0 ->
  (v = 0 \/ pj_node rsegs m lblk v t D /\ Forall (fun ak => 0 < fst ak) D) ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= W0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2 ^ 62 ->
  STRTOD_GLOBALS_TOP <= W0 ->
  ex_apart q 40 x0 len -> ex_apart q 40 scr (len + 1) -> ex_apart x0 len scr (len + 1) ->
  ex_apart q 40 W0 (ex_value_K d) -> ex_apart x0 len W0 (ex_value_K d) -> ex_apart x0 len STRTOD_ERRNO 4 ->
  (v <> 0 -> ex_off v D q 40 /\ ex_off v D scr (len + 1) /\ ex_off v D W0 (ex_value_K d) /\
             ex_off v D STRTOD_ERRNO 4) ->
  rw_cells rsegs m STRTOD_GOT_GUARD [C8 (Z_to_bv 64 STRTOD_GUARD)] -> rw_cells rsegs m STRTOD_GUARD [C8 canary] ->
  rw_cells rsegs m STRTOD_ERRNO [C4 ev] ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
  evt rsegs (ex_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x t)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EX_VALUE) fc None m (seg_rom rsegs)).

Definition ex_value_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q v x0 i0 d dl scr lo : Z) (x : list byte)
         (lblk : Z -> Z -> Prop) (t : jv) (D : list (Z * Z)) (canary ev : word),
    ex_value_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m q v x0 i0 d dl scr lo x lblk t D canary ev.
