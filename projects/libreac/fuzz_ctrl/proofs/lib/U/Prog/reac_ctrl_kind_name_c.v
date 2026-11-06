From Stdlib Require Import String ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_KIND_NAME : Z := 0x1477c.
Definition KIND_NAME : Z := 0x1fc58.
Definition QMARK : Z := 0x102ef.

Definition kind_name_addrs : list Z :=
  [0x10501; 0x10408; 0x10369; 0x10310; 0x103de; 0x103ee; 0x1040f; 0x104e3; 0x10298; 0x10441; 0x103f4; 0x102d7;
   0x103fe; 0x10417].

Definition kind_name_addr (x : Z) : Z :=
  if x <=? 13 then nth (Z.to_nat x) kind_name_addrs QMARK else QMARK.

Definition kind_name_bytes : list byte :=
  concat (map (fun a => le8 (Z_to_bv 64 a)) kind_name_addrs).

Definition kind_name_strings (m : word -> option byte) : Prop :=
  forall x, 0 <= x -> bytes_at rsegs m (kind_name_addr x) (cstr_bytes (kind_name x)).

Definition reac_ctrl_kind_name_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m KIND_NAME kind_name_bytes ->
    kind_name_strings m ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr (bv_unsigned a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         bytes_at rsegs m (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_KIND_NAME) fc None m (seg_rom rsegs)).
