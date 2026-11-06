From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Open Scope Z_scope.

Definition sl_s (pl : list byte) : Z := match pl with [] => 0 | _ :: _ => 1 end.

Definition sl_k (pl : list byte) : Z :=
  match pl with [] => 0 | b :: _ => Z.min (bv_unsigned b) (Z.of_nat (length pl) - 1) end.

Definition sl_uri (p : Z) (pl : list byte) : Z := p + sl_s pl.

Definition sl_text (p : Z) (pl : list byte) : Z := p + sl_s pl + sl_k pl.

Definition sl_ubuf (pl : list byte) : list byte := firstn (Z.to_nat (sl_k pl)) (skipn (Z.to_nat (sl_s pl)) pl).

Definition sl_tbuf (pl : list byte) : list byte := skipn (Z.to_nat (sl_s pl + sl_k pl)) pl.

Definition sl_un (pl : list byte) : Z := strnlen_res (sl_k pl) (sl_ubuf pl).

Definition sl_tn (pl : list byte) : Z := strnlen_res (Z.of_nat (length (sl_tbuf pl))) (sl_tbuf pl).

Definition sl_ub (pl : list byte) : list byte := firstn (Z.to_nat (sl_un pl)) (sl_ubuf pl).

Definition sl_tb (pl : list byte) : list byte := firstn (Z.to_nat (sl_tn pl)) (sl_tbuf pl).

Definition sl_frame (j : list byte) (v5 v4 v3 v2 v1 v0 vra : word) : list cell :=
  [CB 8 j; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra].

Definition sl_s0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (pl : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 (Z.of_nat (length pl)) ->
    4096 <= p -> p + Z.of_nat (length pl) < 2 ^ 62 ->
    bytes_at rsegs m p pl -> (p + Z.of_nat (length pl) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= p) ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    evt rsegs (fun ms' =>
       (0x400000 < sl_tn pl /\
        exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom rsegs) /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          stk rsegs m' lo (bv_unsigned sp)) \/
       (sl_tn pl <= 0x400000 /\
        exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j : list byte) (m' : word -> option byte),
          ms' = MS (mkR (Z_to_bv 64 0x12fb4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2'
                        (Z_to_bv 64 (sl_un pl)) (Z_to_bv 64 (Z.of_nat (length pl) - sl_s pl))
                        (Z_to_bv 64 (sl_uri p pl)) (Z_to_bv 64 (sl_un pl))
                        (Z_to_bv 64 (sl_text p pl)) (Z_to_bv 64 (sl_tn pl)) a4' a5' a6' a7'
                        (Z_to_bv 64 (sl_text p pl)) (Z_to_bv 64 (sl_tn pl)) (Z_to_bv 64 (sl_uri p pl))
                        (Z_to_bv 64 (- sl_s pl)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x130d0) fc None m' (seg_rom rsegs) /\
          rw_cells rsegs m' (bv_unsigned sp + -64) (sl_frame j s5 s4 s3 s2 s1 s0 ra) /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          stk rsegs m' lo (bv_unsigned sp + -64)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ee4) fc None m (seg_rom rsegs)).

Definition sl_s1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (un : Z),
    s0 = Z_to_bv 64 un -> 0 <= un <= 255 ->
    evt rsegs (fun ms' => exists a1' : word,
       ms' = MS (mkR (Z_to_bv 64 0x12fc4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (un + 1)) a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14f8c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fb4) fc None m (seg_rom rsegs)).

Definition sl_s2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ua un tn uri : Z) (ub junk : list byte),
    a0 = Z_to_bv 64 ua -> s0 = Z_to_bv 64 un -> s4 = Z_to_bv 64 uri -> s3 = Z_to_bv 64 tn ->
    4096 <= ua -> ua + un + 1 < 2 ^ 62 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length ub) = un ->
    bytes_at rsegs m uri ub -> (un = 0 \/ uri + un <= ua \/ ua + (un + 1) <= uri) ->
    rw_cells rsegs m ua [CB (Z.to_nat (un + 1)) junk] -> mem_inv rsegs m ->
    evt rsegs (fun ms' =>
       exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13000) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ua) (Z_to_bv 64 (tn + 1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14f8c) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' ua (ub ++ [Z_to_bv 8 0]) /\
         munch [(ua, ua + (un + 1))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fc4) fc None m (seg_rom rsegs)).

Definition sl_s3_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ta tn text : Z) (live : word)
         (tb junk : list byte),
    a0 = Z_to_bv 64 ta -> s3 = Z_to_bv 64 tn -> s2 = Z_to_bv 64 text ->
    4096 <= ta -> ta + tn + 1 < 2 ^ 62 -> (ta + (tn + 1) <= 0x2f620 \/ 0x2f630 <= ta) ->
    0 <= tn <= 2 ^ 22 -> Z.of_nat (length tb) = tn ->
    bytes_at rsegs m text tb -> (tn = 0 \/ text + tn <= ta \/ ta + (tn + 1) <= text) ->
    rw_cells rsegs m ta [CB (Z.to_nat (tn + 1)) junk] ->
    bytes_at rsegs m 0x2f620 (le8 live) -> wr_at rsegs m 0x2f628 8 ->
    mem_inv rsegs m ->
    evt rsegs (fun ms' =>
       exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x1304c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ta) s1
                       a2' a3' a4' a5' a6' a7' live (Z_to_bv 64 (ta + tn)) (Z_to_bv 64 ta) s5
                       s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13e10) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' ta (tb ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m' 0x2f628 (le8 live) /\
         munch [(ta, ta + (tn + 1)); (0x2f628, 0x2f630)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13000) fc None m (seg_rom rsegs)).

Definition sl_s4_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo un ua ta : Z) (live peak : word)
         (tb ts ub us : list byte),
    a0 = Z_to_bv 64 (names (zbytes tb) (zbytes ub)) ->
    s0 = Z_to_bv 64 un -> s1 = Z_to_bv 64 ua -> s2 = live -> s4 = Z_to_bv 64 ta ->
    Z.of_nat (length ub) = un -> 0 <= un <= 255 ->
    bytes_at rsegs m 0x2f628 (le8 peak) -> bytes_at rsegs m 0x2f620 (le8 live) ->
    bv_unsigned live <= bv_unsigned peak <= bv_unsigned live + un + 3 ->
    cstr_at m ta tb ts -> cstr_at m ua ub us -> 4096 <= ta -> 4096 <= ua ->
    Z.of_nat (length tb) + 1 < 2 ^ 62 ->
    bytes_at rsegs m 0x10485 (map (Z_to_bv 8) (prefix_lc ++ [0])) ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 288 <= bv_unsigned sp ->
    0x2f630 <= bv_unsigned sp - 288 ->
    off_stack sp 288 ta (Z.of_nat (length tb + 1 + length ts)) ->
    off_stack sp 288 ua (Z.of_nat (length ub + 1 + length us)) ->
    off_stack sp 288 0x10485 7 ->
    evt rsegs (fun ms' =>
       exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13084) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ta) (Z_to_bv 64 ua)
                       a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (names (zbytes tb) (zbytes ub))) s4 s5
                       s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13390) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 288, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1304c) fc None m (seg_rom rsegs)).

Definition sl_s5_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x1308c) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x133ec) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13084) fc None m (seg_rom rsegs)).

Definition sl_s6_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x13094) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14e4c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1308c) fc None m (seg_rom rsegs)).

Definition sl_s7_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x1309c) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14e4c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13094) fc None m (seg_rom rsegs)).

Definition sl_s8_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte) (v5 v4 v3 v2 v1 v0 vra : word),
    rw_cells rsegs m (bv_unsigned sp) (sl_frame j v5 v4 v3 v2 v1 v0 vra) ->
    evt rsegs (fun ms' =>
       ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                     v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1309c) fc None m (seg_rom rsegs)).
