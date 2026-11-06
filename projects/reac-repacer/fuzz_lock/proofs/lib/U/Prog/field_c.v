(* Contract of reac-repacer's static [field] (src/repace_conf.c:87-99 at 3ac1cf10) in fuzz_lock.ubsan, 0x13490.
   The statement of lib/Prog/field_c.v at the UBSan address, with three more premises the UBSan checks need
   (each check branches to the trap [unimp] at 0x1353c):
   - 0x13494 [andi a3,a0,7; bnez a3]: p is 8-byte aligned (pp mod 8 = 0);
   - 0x134b0 / 0x134f8 [beqz a3 / beqz a4]: the pointer read is not NULL (0 < s, where plain field_c.v has 0 <= s);
   - 0x13524 [andi a1,a2,7; bnez a1]: at is 8-byte aligned (ap mod 8 = 0).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
Import ListNotations.
Open Scope Z_scope.

Definition FIELD : Z := 0x13490.

(* field(&p, end, &at) on the bytes l of [p, end): the separators it skips and the field's length *)
Definition fld_s (l : list byte) : nat := sep_run l.
Definition fld_n (l : list byte) : nat := tok_run (skipn (sep_run l) l).

Definition field_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pp ap s : Z) (l : list byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (fld_n l))) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(pp, pp + 8); (ap, ap + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' pp [C8 (Z_to_bv 64 (s + Z.of_nat (fld_s l + fld_n l)))] /\
    rw_cells rsegs m' ap [C8 (Z_to_bv 64 (s + Z.of_nat (fld_s l)))].

Definition field_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pp ap s : Z) (l J : list byte),
    0 < s -> s + Z.of_nat (length l) < 2^64 ->
    bytes_at rsegs m s l ->
    rw_cells rsegs m pp [C8 (Z_to_bv 64 s)] ->
    rw_cells rsegs m ap [CB 8 J] ->
    pp + 8 <= ap \/ ap + 8 <= pp ->
    pp mod 8 = 0 -> ap mod 8 = 0 ->
    mem_inv rsegs m ->
    evt rsegs (field_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp ap s l)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pp) (Z_to_bv 64 (s + Z.of_nat (length l))) (Z_to_bv 64 ap)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FIELD) fc None m (seg_rom rsegs)).
