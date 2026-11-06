From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotFR SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_role.c:133-168 (4896 bytes, 1224 instructions at 0x12ea0 in the plain image; frame
    496 bytes; FrameAPI.ENTRY). It allocates two blocks (pp = malloc(19744), pod = malloc(len ? len : 1); freed pod
    first), so its contract is in the form libreac/fuzz_ctrl's released slot consumes, as reac-pw/fuzz_pin's: the
    frame's obligation SlotFR.slot_goal (lib_contract_g for ENTRY, from FrameAPI.frame_plain), split at the cuts of
    SlotInv.v into the segment statements S_E01, S_M01, S_M02, S_X01 below (ctrl's continuation form: the H of each
    exit cut -> the H of the entry cut), plus the n >= 2^26 run (0x12ed8 `srli a2,a1,26`; 0x12ee0 `j 0x14168`:
    `mv a0,zero` and the epilogue, no call), which the slot proves as one evt like ctrl's slot_early. What the whole
    function promises is lib_contract_g's: from lib_pre at ENTRY (a0 = data, a1 = n, the input block or `empty` for
    n = 0; sp 16-aligned with 65536 writable bytes below it, above alloc_ceiling; ra even; frm = 0), it returns to ra
    with a0 = 0, every callee-saved register as at entry, the allocator back to its entry blocks (RES_END), the input
    bytes unchanged, no byte changed outside [sp - 65536, sp) and the allocator's own state, at an FP state with
    frm = 0 (lib_post). On the way none of check_absent, check_role, check_malformed, check_answer, check_code aborts:
    that is the content of role_check_contract's evt reaching 0x14158.

    The two middle segments' bodies are stated as evts, role_build_contract and role_check_contract, so that their
    walks can be proved apart from the slot; S_M01's and S_M02's proofs lift them inside FR as ctrl's segments lift
    theirs (the run over the stack window and the live harness blocks). The callee contracts the walks take as premises
    (the released forms relocated to role's image, or written in this directory):
      S_E01: malloc through the frame's malloc_contract (ms_malloc = 0x15e54) by the slot's malloc step (hb = [],
             request 19744 <= 2^26: SlotFR.resb_room);
      role_build_contract: memset_contract (Prog/memset_c.v, 0x1c7b4), memcpy_contract (Prog/memcpy_c.v, 0x1c3b0),
             strlen_contract (Prog/strlen_c.v, 0x1c8e4), and the shared model's pod_build and pp_bytes (Pod/Model.v,
             Pod/Layout.v) with their step lemmas;
      S_M01: malloc again by the slot's malloc step (hb = [(pp, 19744)], request len, 8 <= len <= 5440);
      role_check_contract: memcpy_contract, reac_role_prop_parse_contract, strcmp_contract (Prog/strcmp_c.v,
             0x1c8ac), pod_nearest_contract, check_absent_contract, check_role_contract, check_malformed_contract,
             reac_role_cfg_changes_contract, reac_role_cfg_apply_state_contract, check_answer_contract,
             reac_role_refuse_code_contract, check_code_contract (Prog/<fn>_c.v), and the shared model's
             parse_model_encode (Pod/Role.v: parse_model (buf r) = expect_model false r for an uncorrupted record);
      S_X01: free(pod) by the slot's free of a block in any position (ctrl's b3_free_call form) and free(pp) by its
             one-block free (ctrl's b8_free_call form), both through the frame's free_contract (ms_free = 0x15d14).
    Statement text only: no function is proved here. *)

(** The quantities of the two evts. *)
Definition ROLE_BUILD : Z := 0x12f14.
Definition ROLE_MALLOC2 : Z := 0x13f48.
Definition ROLE_CHECK : Z := 0x13f4c.
Definition ROLE_FREE : Z := 0x14158.
(* The deepest callee stack below the harness sp: pod_nearest's 48-byte frame and __addtf3's 48 bytes. *)
Definition MID_STACK : Z := 96.
(* The harness frame below its saved registers: [sp, sp + 0x188) (the saves are at [sp + 0x188, sp + 0x1f0)). *)
Definition FRAME_LOCALS : Z := 0x188.
(* The absolute-pointer tables of .data.rel.ro the builder reads: vocab (0x1de68, 9 pointers) and odd_ch (0x1deb0,
   14 pointers), inside FrameAPI.frame_RELRO [0x1de58, 0x1dfb0). *)
Definition RELRO_TBL : Z := 0x1de68.
Definition RELRO_TBL_END : Z := 0x1df20.

(* pp->len after pod_build of the bytes after the flags byte. *)
Definition role_len (rest : list byte) : Z := Z.of_nat (length (buf (fst (pod_build rest)))).

(** ** The builder segment as an evt: [0x12f14, 0x13f48)
    From malloc(pp)'s return (0x12f14 `bnez a0`, the abort branch 0x12f18 not taken: pp <> 0) to the second malloc's
    call (0x13f48 `jal malloc`, not executed). Registers at 0x12f14 as SlotInv.Inv_K12f14 names them: a0 = pp,
    s3 = src (the input cursor after the flags byte), s2 = the bytes left, s5 = fl, s1 = 19744, s0 = 0x5000. In order
    (pod.h:382-449, fuzz.h:37-80): memset(pp, 0, 19744) (0x12f38); pod_build's header and property loop (0x130cc),
    its Struct pod loop (0x132fc) with ent_build's jump table (`jr a1` 0x1335c through 0x10538), the inlined
    pod_write_ent and the 104-byte record copy; the size patches; the corruption (0x13ea0-0x13f3c); then
    len = pp->len (0x13f34) and a0 = len + (len = 0) (0x13f40-0x13f44). It ends at 0x13f48 with a0 = s2 = len (len >= 8,
    so the request is len), s11 = pp, s4 = pp + 0x4d14, s5 = fl, the cells sp + 0x50 = pp and sp + 0x80 = pp + 0x4000,
    the pp block = pp_bytes of the record pod_build made of the input, sp, gp, tp, F and fc unchanged (no FP
    instruction in this range), and no byte changed outside the callees' stack below sp, the harness frame's locals
    [sp, sp + 0x188) and the pp block.
    Premises: the k bytes rest at src (src > 0); the pp block's 19744 bytes present and writable (rw_cells), outside
    the image, apart from the input, both below the stack region [lo, sp); the stack region with the frame's locals
    (stk over [lo, sp + 0x188): present and writable, as FR's stk gives; strlen(ch) reads the bytes after ch's NUL
    to the next 8-byte boundary, inside ch[24]), outside the image; the .data.rel.ro tables as in the image (FR's
    relro); mem_inv. The slot discharges
    each from FR at K12f14 (see S_M01). *)
Definition role_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s3 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) -> s5 = Z_to_bv 64 fl -> 0 <= fl < 256 ->
    s1 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s10' t3' t4' t5' t6'
                          : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (role_len rest)) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (role_len rest)) s3' (Z_to_bv 64 (pp + POD_NENT_OFF)) (Z_to_bv 64 fl)
                       s6' s7' s8' s9' s10' (Z_to_bv 64 pp) t3' t4' t5' t6')
                  F (Z_to_bv 64 ROLE_MALLOC2) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 pp)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_BUILD) fc None m (seg_rom rsegs)).

(** ** The checking segment as an evt: [0x13f4c, 0x14158)
    From malloc(pod)'s return (0x13f4c `beqz a0`, the abort branch to 0x141bc not taken: pod <> 0) to the pc after
    check_code's return. Registers at 0x13f4c as SlotInv.Inv_K13f4c names them: a0 = pod, s2 = len, s11 = pp,
    s4 = pp + 0x4d14, s5 = fl; the cells sp + 0x50 = pp, sp + 0x80 = pp + 0x4000; the pp block = pp_bytes r for the
    record r that pod_build made of some input (fuzz_role.c:144-163). In order: memcpy(pod, pp, len) when len <> 0
    (0x13f64); cur = fl bit 1 (0x13f68 `slli s0,s5,62`); the role cell sp + 0x128 := 0x5a (0x13f74);
    rc = reac_role_prop_parse(fl bit 0 ? NULL : pod, sp + 0x128) (0x13f84); when pp->corrupt = 0 (0x13f88-0x13f90),
    expect_role inlined (0x13f94-0x140e0: is_props, params_struct, the pod_next_pair scan with strcmp against
    "reac.cfg.role" (0x14050), pod_int, or pod_float and pod_nearest(f, &flag = sp + 0x88) (0x140d0), flag < 2) and
    check_absent (0x140ac) / check_role (0x141b4) / check_malformed (0x140ec) by its answer; req = rc = 1 ? role :
    !cur (0x140f4-0x14104); check_answer(changes(cur, req), apply_state(cur, req), cur, req) (0x14110, 0x14120,
    0x14134); check_code(refuse_code(0), refuse_code(1)) (0x1413c, 0x14148, 0x14154). It ends at 0x14158 with s1 = pod,
    s11 = pp, sp, gp, tp unchanged, at some FP state with frm = 0 (pod_nearest and the parse write FP registers and
    accrue fflags), and no byte changed outside the callees' stack below sp, the frame's locals and the pod block.
    Reaching 0x14158 at all is the property: no check aborts. It holds because the parse's answer is parse_model of
    buf r (reac_role_prop_parse_contract), which for an uncorrupted r equals expect_model (fl bit 0) r, the answer
    expect_role computes from the record in pp (Pod/Role.v); and check_answer's and check_code's premises hold for
    every rc (their contracts).
    Premises: the record's pp_bytes at pp; the pod block's len bytes present and writable, outside the image, apart
    from pp, both below lo; the stack region with the frame's locals (stk over [lo, sp + 0x188)), outside the image;
    frm0 fc; mem_inv;
    MemNorm.task_mem (bytes only in the image's segments or below TASK_SIZE: the soft-float callees of pod_nearest
    take it, as libreac/fuzz_boxreg's CJ callees do; the slot runs this evt on MemNorm.normalize_cj of the cut's
    memory, which has it by mem_inv_cj_normalize). *)
Definition role_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (fl pp pod lo : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 -> pod mod 16 = 0 ->
    s2 = Z_to_bv 64 (role_len inp) -> s11 = Z_to_bv 64 pp -> s4 = Z_to_bv 64 (pp + POD_NENT_OFF) ->
    s5 = Z_to_bv 64 fl -> 0 <= fl < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m pp (pp_bytes (fst (pod_build inp))) ->
    rw_cells rsegs m pod [CB (Z.to_nat (role_len inp)) junk] ->
    (forall a, pod <= a < pod + role_len inp -> seg_rom rsegs (wa a) = None) ->
    (pod + role_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    pod + role_len inp <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10'
                          t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod) a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' s4' s5' s6' s7' s8' s9' s10' (Z_to_bv 64 pp) t3' t4' t5' t6')
                  F' (Z_to_bv 64 ROLE_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pod, pod + role_len inp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_CHECK) fc None m (seg_rom rsegs)).

(** ** The segment statements (ctrl's Slot.v Section Stmts form, as pin's)
    S_E01, ENTRY -> K12f14: the prologue (saves at [S - 104, S)); n < 2^26 by GV, so 0x12edc falls through; the flags
      byte and the cursor (0x12ee4-0x12f00); malloc(19744) at 0x12f10 with ra = 0x12f14 through the slot's malloc step
      (FR with hb = []), whose continuation gives FR with hb = [(pp, 19744)], pp <> 0, pp mod 16 = 0 and the
      callee-saved registers.
    S_M01, K12f14 -> K13f4c: role_build_contract on the normalized memory, with rest := g_rest g at g_src g (the input
      block's tail, unchanged since ENTRY by FR and GV's blk_data, or empty), fl := g_fl g, lo := S - 65536 (FR's
      stk), sp = S - 496; the pp block's cells from the frame's blocks_writable and the allocator relation (present,
      outside the image); the tables from relro; then `jal malloc` with a0 = g_len g and the slot's malloc step from
      hb = [(pp, 19744)] (g_len g <= 5440: pod_build_wf), whose kept-bytes clause carries the pp block's bytes to the
      cut.
    S_M02, K13f4c -> K14158: role_check_contract on the normalized memory, with inp := g_rest g, the cut's cells and
      registers, the pod block's cells from the frame, frm0 from the cut's frm_zero; then FR and the block list carry
      over (the writes lie in [S - 592, S - 104) and the pod block).
    S_X01, K14158 -> RET: `mv a0,s1` and free(pod) at 0x1415c with ra = 0x14160 by the slot's free of the head block
      of [(pod, g_len g); (pp, 19744)]; `mv a0,s11` and free(pp) at 0x14164 with ra = 0x14168 by its one-block free,
      which leaves hb = []; `mv a0,zero`, the restores from the saved bytes, `addi sp,sp,0x1f0`, ret to ra: Post
      (lib_post; RES_END by resb_end). *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K12f14 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K13f4c B APIf ra empty) -> Hcut B APIf ra (Inv_K12f14 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K14158 B APIf ra empty) -> Hcut B APIf ra (Inv_K13f4c B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K14158 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_X01.

End Stmts.
