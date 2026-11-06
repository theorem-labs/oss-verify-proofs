From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_find_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_role(c, name, out) (reac_segconf.c:533-541; at 0x160e4 in the UBSan image 1696d6c34ffd; frame 16 bytes,
    saves ra and s0 = out): s = find(c, name); 0 when s is NULL or s->role_set = 0 (`lw 0x14`); else 1, and when
    out <> NULL `lw a1,0x10(s); sw a1,0(out)`: *out = s->role.
    The UBSan checks trap on s & 3 <> 0 and on out & 3 <> 0: s = c + 356 i with c 16-aligned, and out 4-aligned
    (premise).
    It writes its frame and find's, [sp - ROLE_STACK, sp), and the 4 bytes at out exactly when it returns 1 with
    out <> NULL.

    Post in the spine's terms: a0 = 1 and *out = r when SegModel.r_role rc nm = Some r (out <> NULL), a0 = 0 when it
    is None.

    Callee contract its walk takes as a premise: reac_segconf_find_contract.

    Call sites: LLVMFuzzerTestOneInput 0x13c8c (c, g->name, out = &r, main's cell at sp + 0x60 holding 0x5a:
    4-aligned, writable, above this sp); check_absent 0x14dc8 (c, the probe, out = NULL). *)
Definition REAC_SEGCONF_ROLE : Z := 0x160e4.
Definition ROLE_STACK : Z := 16 + FIND_STACK.

Definition role_pre (m : word -> option byte) (sp lo c name out : Z) (rc : rconf) (nm : list Z) : Prop :=
  query_pre ROLE_STACK m sp lo c name rc nm /\
  (out = 0 \/ (out mod 4 = 0 /\ wr_at rsegs m out 4 /\ apart out 4 lo sp)).

(** The bytes it writes: the frames, and the out cell when it stores. *)
Definition role_W (sp out : Z) (o : option Z) : list ivl :=
  match o with
  | Some _ => if out =? 0 then [(sp - ROLE_STACK, sp)] else [(sp - ROLE_STACK, sp); (out, out + 4)]
  | None => [(sp - ROLE_STACK, sp)]
  end.

Definition reac_segconf_role_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (nm : list Z),
    role_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) rc nm ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (match r_role rc nm with Some _ => 1 | None => 0 end)
         m
         (role_W (bv_unsigned sp) (bv_unsigned a2) (r_role rc nm))
         lo
         (fun m' => match r_role rc nm with
           | Some v => bv_unsigned a2 <> 0 -> bytes_at rsegs m' (bv_unsigned a2) (le4 (Z_to_bv 64 v))
           | None => True
           end))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_ROLE) fc None m (seg_rom rsegs)).
