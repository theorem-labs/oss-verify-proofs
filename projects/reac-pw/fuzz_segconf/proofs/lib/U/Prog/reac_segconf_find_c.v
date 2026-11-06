From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_find(c, name) (reac_segconf.c:517-525; at 0x15ff0 in the UBSan image 1696d6c34ffd; frame 64 bytes, saves
    ra and s0-s5): NULL for a NULL c or name (no call site passes one: the premise excludes them); else n = c->n
    (`lw` of c + 0x2c80) and, for i = 0 .. n-1, strcmp(c->seg[i].name, name) (`jal strcmp`, 0x1f594); the first 0
    returns &c->seg[i] = c + 356 i; none returns NULL. The UBSan checks trap on c & 7 <> 0, on i = 32 (the array bound) and on c + 356 i
    wrapping: c 16-aligned, n <= 32 (rconf_enc) and c + 16616 <= 2^64 (bytes_at) rule them out.
    It reads c->n, the names of seg[0 .. n) and the string at name; it writes only its frame [sp - 64, sp).

    Post in the spine's terms: a0 = seg_spec.find_ptr c rc nm, i.e. &c->seg[i] for SegModel.r_find rc nm = Some i,
    else 0 (strcmp's r = 0 <-> sx = sy is SegModel.strcmp's = 0 on C strings: Spec/SegBridge.v).

    Callee contract its walk takes as a premise: strcmp_contract (Prog/strcmp_c.v under lib/U, STRCMP = 0x1f594;
    commit f0ba542764d9): both strings NUL-terminated, no stack, no store.

    Call sites: check_absent 0x14db4 (c, name = the probe "<name>x" on LLVMFuzzerTestOneInput's frame, or
    "nosuch0" at seg_spec.STR_NOSUCH in .rodata), and through the accessors (ignored, role, role_file, ignore_file,
    model) from LLVMFuzzerTestOneInput's per-segment checks (name = m->seg[i].name in the mconf block) and from
    check_absent. At each: c = the reader's block (malloc(16616): nonzero, 16-aligned), holding the reader's state rc
    after the files (rconf_at, from reac_segconf_parse_file's / reac_segconf_parse's posts); name a C string in the
    mconf block, in main's frame or in .rodata, so outside [lo, sp) and outside the callee frames. *)
Definition REAC_SEGCONF_FIND : Z := 0x15ff0.
Definition FIND_STACK : Z := 64.

(** What every reader query asks of its caller: c the reader's block holding rc, name the C string nm, both apart
    from the stack region [lo, sp) the query uses (depth bytes). *)
Definition query_pre (depth : Z) (m : word -> option byte) (sp lo c name : Z) (rc : rconf) (nm : list Z) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\
  name <> 0 /\ cstrz_at rsegs m name nm /\ apart name (Z.of_nat (length nm) + 1) lo sp /\
  stack_ok rsegs m lo sp depth /\ mem_inv rsegs m.

Definition reac_segconf_find_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (nm : list Z),
    query_pre FIND_STACK m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) rc nm ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (find_ptr (bv_unsigned a0) rc nm)
         m
         ([(bv_unsigned sp - FIND_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_FIND) fc None m (seg_rom rsegs)).
