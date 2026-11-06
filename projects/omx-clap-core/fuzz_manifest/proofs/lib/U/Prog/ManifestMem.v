From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel.
Import ListNotations.
Open Scope Z_scope.

Definition zbytes (bs : list byte) : list Z := map bv_unsigned bs.

Definition cstr_at (m : word -> option byte) (s : Z) (bs slack : list byte) : Prop :=
  bytes_at rsegs m s (bs ++ Z_to_bv 8 0 :: slack) /\
  Forall (fun b => bv_unsigned b <> 0) bs /\
  (- (s + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack).

Definition kret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo K : Z) (m : word -> option byte) (W : list ivl) (R : word -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ((bv_unsigned sp - K, bv_unsigned sp) :: W) m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    R a0'.

Definition kretm (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo K : Z) (m : word -> option byte) (W : list ivl) (R : word -> (word -> option byte) -> Prop)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ((bv_unsigned sp - K, bv_unsigned sp) :: W) m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    R a0' m'.

Definition off_stack (sp : word) (K a n : Z) : Prop := a + n <= bv_unsigned sp - K \/ bv_unsigned sp <= a.

Fixpoint find_sub_from (h nd : list Z) (i : nat) (fuel : nat) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      if (i + length nd <=? length h)%nat && zl_eqb (firstn (length nd) (skipn i h)) nd then Some i
      else find_sub_from h nd (S i) fuel'
  end.

Definition find_sub (h nd : list Z) : option nat := find_sub_from h nd 0 (S (length h)).

Definition tolower (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
