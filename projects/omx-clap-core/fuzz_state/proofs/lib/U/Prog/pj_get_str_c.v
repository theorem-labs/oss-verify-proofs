From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
Import ListNotations.
Open Scope Z_scope.

Definition PJ_GET_STR : Z := 0x14a34.

Definition pj_get_str_res (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (t : jv) (D : list (Z * Z))
    (kname : list Z) (z : Z) : Prop :=
  match t with
  | JObj members =>
      (forall nm u, In (nm, u) members -> nm <> kname) /\ z = 0 \/
      exists i v kids,
        nth_error members i = Some (kname, v) /\
        (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) /\
        pj_u64 rsegs m (o + 24) kids /\
        match v with
        | JStr s => pj_u64 rsegs m (kids + 56 * Z.of_nat i + 16) z /\
                    exists n, pj_cstr rsegs m lblk z n s /\ In (z, n) D
        | _ => z = 0
        end
  | _ => z = 0
  end.

Definition pj_get_str_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lblk : Z -> Z -> Prop)
         (o k : Z) (kname : list Z) (t : jv) (D : list (Z * Z)) (lo : Z),
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k ->
    (o = 0 \/ pj_node rsegs m lblk o t D) ->
    pj_cbytes rsegs m k kname ->
    (forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\
       disjoint_from [(a, a + n)] (bv_unsigned sp - 96) 96) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 ->
    disjoint_from [(o, o + 56); (k, k + Z.of_nat (length kname) + 1)] (bv_unsigned sp - 96) 96 ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ pj_cbytes rsegs m' k kname /\
         (o = 0 /\ r = Z_to_bv 64 0 \/
          o <> 0 /\ pj_node rsegs m' lblk o t D /\
          exists z, r = Z_to_bv 64 z /\ pj_get_str_res m' lblk o t D kname z))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_GET_STR) fc None m (seg_rom rsegs)).
