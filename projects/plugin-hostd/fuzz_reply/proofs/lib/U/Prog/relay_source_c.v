From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRep.
Import ListNotations.
Open Scope Z_scope.

Definition RELAY_SOURCE : Z := 0x14e78.
Definition G_NSRC : Z := 0x318b8.
Definition G_SRC : Z := 0x318d0.

Fixpoint src_find (fd : Z) (es : list rentry) : option (nat * rentry) :=
  match es with
  | [] => None
  | e :: es' =>
      if re_fd e =? fd then Some (O, e)
      else match src_find fd es' with Some (i, e') => Some (S i, e') | None => None end
  end.

Definition relay_source_r (G fd : Z) (es : list rentry) : Z :=
  match src_find fd es with Some (i, _) => G + 56 * Z.of_nat i | None => 0 end.

Definition src_table (m : word -> option byte) (G : Z) (es : list rentry) : Prop :=
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ -2^31 <= re_fd e < 2^31) es /\
  bytes_at rsegs m G (concat (map entry_bytes es)).

Definition relay_source_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fd : Z) (g : word) (es : list rentry),
    -2^31 <= fd < 2^31 ->
    a0 = Z_to_bv 64 fd ->
    Z.of_nat (length es) < 2^31 ->
    bytes_at rsegs m G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es)))) ->
    bytes_at rsegs m G_SRC (le8 g) ->
    src_table m (bv_unsigned g) es ->
    (es <> [] -> bv_unsigned g <> 0 /\ bv_unsigned g mod 8 = 0) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (relay_source_r (bv_unsigned g) fd es))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RELAY_SOURCE) fc None m (seg_rom rsegs)).
