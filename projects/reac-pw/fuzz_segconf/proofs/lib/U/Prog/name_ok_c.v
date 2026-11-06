From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** name_ok(s) (reac_declared_vlan.c:20-30, static; at 0x1648c in the UBSan image 1696d6c34ffd; 164 bytes, frame
    48 bytes, saves ra and s0-s4).
    As compiled: the C test `!s` is gone (the one caller, reac_declared_vlan_split, has already returned 0 for a NULL
    parent, so the premise is s <> 0): `lbu s4,0(a0)` reads *s at once and `beqz s4` returns 0 for the empty string.
    The loop (head 0x164d0, latch `bnez s4` 0x164fc) calls isalnum on the byte (`andi a0, s4, 0xff`, `jal` 0x164d4);
    when it answers 0 the byte must be one of "-.:_": a1 = *p - 0x2d, `bltu s1, a1` with s1 = 0x32, then bit a1 of s2
    = 2^50 + 2^13 + 3 (bits 0, 1, 13, 50: '-', '.', ':', '_'), else it returns 0; at the NUL it returns 1.
    The one UBSan check, `beq s0, s3` at 0x164f0 with s3 = -1 (to the `unimp` at 0x1652c), traps on p = 2^64 - 1
    before p++ (pointer-overflow): p is the address of a byte of nm, below s + length nm, and bytes_at gives
    s + length nm + 1 <= 2^64.
    It reads the bytes of s up to its NUL one at a time (`lbu`, no slack) and writes only its frame
    [sp - NAME_OK_STACK, sp).

    Post in the spine's terms: a0 = b2z (SegModel.name_ok nm) for the C string nm at s (isalnum_c.v's alnum_b is
    SegModel.isalnum on a byte).

    Callee contract its walk takes as a premise: isalnum_contract (Prog/isalnum_c.v under lib/U, ISALNUM = 0x167d4;
    commit d8911fcbf9ff): a0 = 1 or 0 by alnum_b, a leaf (no stack, no memory).

    Call site: reac_declared_vlan_split 0x1646c (reac_declared_vlan.c:58) with a0 = parent: the memcpy of the plen <=
    15 bytes before the dot and the NUL stored at parent + plen (`sb zero` 0x16464) make it the C string
    firstn plen segment, with no NUL in it; parent is reac_segconf_declared's buffer at its sp + 8, above this sp and
    so outside [lo, sp). *)
Definition NAME_OK : Z := 0x1648c.
Definition NAME_OK_STACK : Z := 48.

Definition name_ok_pre (m : word -> option byte) (sp lo s : Z) (nm : list Z) : Prop :=
  s <> 0 /\ cstrz_at rsegs m s nm /\ apart s (Z.of_nat (length nm) + 1) lo sp /\
  stack_ok rsegs m lo sp NAME_OK_STACK /\ mem_inv rsegs m.

Definition name_ok_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (nm : list Z),
    name_ok_pre m (bv_unsigned sp) lo (bv_unsigned a0) nm ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (b2z (name_ok nm))
         m
         ([(bv_unsigned sp - NAME_OK_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NAME_OK) fc None m (seg_rom rsegs)).
