From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_address (fuzz_segconf.c:531-542; at 0x14964 in the image 3776ca44d75c; frame 32 bytes).
    n = strlen(want) (`jal strlen`); strncmp(got, want, n) <> 0 aborts (`jal strncmp`).

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With gs the reader's refusal text and ws the model's kept address, the premise is check_kept's first
    conjunct: SegModel.strncmp gs ws (SegModel.strlen ws) = 0.

    Callee contracts its walk takes as premises: strlen_contract (Prog/strlen_c.v, 0x1ec30: want's slack) and strncmp_contract (Prog/strncmp_c.v,
    0x1ed84: StrFun.strncmp_model; SegModel.strncmp agrees with it on these strings: Spec/SegBridge.v).

    Call site (LLVMFuzzerTestOneInput): 0x13bd8 `jal check_address` with a0 = c->refusal[i] = c + 0x2e88 + 200 i (seg_spec.refusal_addr), a1 =
    m->kept[i] = m + 0x200c + 112 i (seg_spec.kept_addr), for i < m->n_kept and i < c->n_refusals: C strings
    in the two blocks (rconf_enc / mconf_enc), with the slack after want inside the mconf block. *)
Definition CHECK_ADDRESS : Z := 0x14964.
Definition CHECK_ADDRESS_STACK : Z := 32.

Definition check_address_pre (m : word -> option byte) (sp lo got want : Z) (gs ws : list Z) : Prop :=
  got <> 0 /\ cstrz_at rsegs m got gs /\ apart got (Z.of_nat (length gs) + 1) lo sp /\
  want <> 0 /\ cstr_at rsegs m want ws /\ apart want (Z.of_nat (length ws) + 1) lo sp /\
  strncmp gs ws (strlen ws) = 0 /\
  stack_ok rsegs m lo sp CHECK_ADDRESS_STACK /\ mem_inv rsegs m.

Definition check_address_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (gs ws : list Z),
    check_address_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) gs ws ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_ADDRESS_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ADDRESS) fc None m (seg_rom rsegs)).
