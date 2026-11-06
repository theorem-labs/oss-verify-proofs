From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_NAME : Z := 0x13fa4.
Definition BN_K : Z := 288.
Definition BN_TS : Z := 0x1dea8.
Definition BN_S1 : Z := 0x102d0.
Definition BN_S2 : Z := 0x103a4.
Definition BN_S3 : Z := 0x104e9.
Definition BN_REAC : Z := 0x10533.
Definition BN_PAREN : Z := 0x103b6.
Definition BN_IN : Z := 0x1034e.
Definition BN_OUT : Z := 0x10507.

Definition bn_bytes (s : list Z) : list byte := map (Z_to_bv 8) s.

Definition bn_cstr (m : word -> option byte) (lo hi a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  exists sl : list byte,
    bytes_at rsegs m a (bn_bytes s ++ Z_to_bv 8 0 :: sl) /\
    (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length sl) /\
    disjoint_from [(lo, hi)] a (Z.of_nat (length s) + 1 + Z.of_nat (length sl)).

Definition bn_lit (m : word -> option byte) (lo hi a : Z) (s : list Z) : Prop :=
  bytes_at rsegs m a (bn_bytes (s ++ [0])) /\ disjoint_from [(lo, hi)] a (Z.of_nat (length s) + 1).

Definition bn_image (m : word -> option byte) (lo hi : Z) : Prop :=
  bytes_at rsegs m BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3)) /\
  disjoint_from [(lo, hi)] BN_TS 24 /\
  bn_cstr m lo hi BN_S1 (bn_STEM 1) /\ bn_cstr m lo hi BN_S2 (bn_STEM 2) /\
  bn_cstr m lo hi BN_S3 (bn_STEM 3) /\ bn_cstr m lo hi BN_REAC (bn_STEM 0) /\
  bn_lit m lo hi BN_PAREN [32; 40] /\ bn_lit m lo hi BN_IN [32; 105; 110; 32; 47; 32] /\
  bn_lit m lo hi BN_OUT [32; 111; 117; 116; 41].

Definition bn_said (m : word -> option byte) (lo hi said : Z) (sd : list Z) : Prop :=
  (said = 0 /\ sd = []) \/ (said <> 0 /\ bn_cstr m lo hi said sd).

Definition bn_bufs (m : word -> option byte) (lo hi name name_len token token_len display display_len : Z) : Prop :=
  (exists j, rw_cells rsegs m name [CB (Z.to_nat (Z.min name_len 24)) j]) /\
  (exists j, rw_cells rsegs m token [CB (Z.to_nat (Z.min token_len 24)) j]) /\
  (exists j, rw_cells rsegs m display [CB (Z.to_nat (Z.min display_len 48)) j]) /\
  disjoint_from [(lo, hi); (token, token + Z.min token_len 24); (display, display + Z.min display_len 48)]
    name (Z.min name_len 24) /\
  disjoint_from [(lo, hi); (display, display + Z.min display_len 48)] token (Z.min token_len 24) /\
  disjoint_from [(lo, hi)] display (Z.min display_len 48).

Definition bn_args_ok (name name_len token token_len display display_len i o : Z) : bool :=
  negb (name =? 0) && negb (token =? 0) && negb (display =? 0) &&
  negb (name_len =? 0) && negb (token_len =? 0) && negb (display_len =? 0) &&
  bn_ok i && bn_ok o && negb ((i =? 0) && (o =? 0)).

Definition bn_accept (f : Z) (sd : list Z) (i o name name_len token token_len display display_len : Z) : bool :=
  bn_args_ok name name_len token token_len display display_len i o && (bn_ret f sd i o =? 0) &&
  (Z.of_nat (length (bn_NM f sd i o)) <? name_len) &&
  (Z.of_nat (length (bn_TK (bn_NM f sd i o))) <? token_len) &&
  (Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) <? display_len).

Definition reac_box_name_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f i o : Z) (display display_len : word)
         (sd : list Z),
    a0 = Z_to_bv 64 f -> -2^31 <= f < 2^31 ->
    a2 = Z_to_bv 64 i -> -2^31 <= i < 2^31 ->
    a3 = Z_to_bv 64 o -> -2^31 <= o < 2^31 ->
    bytes_at rsegs m (bv_unsigned sp) (le8 display ++ le8 display_len) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BN_K <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    bn_image m (bv_unsigned sp - BN_K) (bv_unsigned sp) ->
    (bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                (bv_unsigned display) (bv_unsigned display_len) i o = true ->
       bn_said m (bv_unsigned sp - BN_K) (bv_unsigned sp) (bv_unsigned a1) sd /\
       bn_bufs m (bv_unsigned sp - BN_K) (bv_unsigned sp) (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6)
               (bv_unsigned a7) (bv_unsigned display) (bv_unsigned display_len)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                       (bv_unsigned display) (bv_unsigned display_len)
          then a0' = Z_to_bv 64 0 /\
               munch [(bv_unsigned sp - BN_K, bv_unsigned sp);
                      (bv_unsigned a4, bv_unsigned a4 + Z.of_nat (length (bn_NM f sd i o)) + 1);
                      (bv_unsigned a6, bv_unsigned a6 + Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1);
                      (bv_unsigned display,
                       bv_unsigned display + Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1)] m m' /\
               bytes_at rsegs m' (bv_unsigned a4) (bn_bytes (bn_NM f sd i o ++ [0])) /\
               bytes_at rsegs m' (bv_unsigned a6) (bn_bytes (bn_TK (bn_NM f sd i o) ++ [0])) /\
               bytes_at rsegs m' (bv_unsigned display) (bn_bytes (bn_DP (bn_NM f sd i o) i o ++ [0]))
          else a0' = Z_to_bv 64 (-1) /\ munch [(bv_unsigned sp - BN_K, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_NAME) fc None m (seg_rom rsegs)).
