From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotFR SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_role.c:133-168 (4964 bytes, 1241 instructions at 0x12ec0 in the UBSan image; frame
    544 bytes; U/FrameAPI.ENTRY). The plain contract (lib/Prog/LLVMFuzzerTestOneInput_c.v) with the UBSan numbers: the
    frame's obligation U/Prog/SlotFR.slot_goal (from U/FrameAPI.frame_ubsan), split at the cuts of U/Prog/SlotInv.v
    into S_E01, S_M01, S_M02, S_X01 below, plus the n >= 2^26 run (0x12ef8 `srli a2,a1,26`; 0x12f00 `j 0x141c4`), as one
    evt like ctrl's slot_early. The whole function promises lib_contract_g's lib_post, as in the plain build.

    UBSan checks: 75 trap branches in this function, all to the `unimp` at 0x14204 (0x14220 is a second `unimp`,
    after the abort call 0x1421c). One is S_E01's: 0x12f14-0x12f18, data + 1 <= 1 when n >= 1 (data is a user block
    above 4096 by blocks_low, so data + 1 neither wraps nor is 1). 68 lie in role_build's range (the cursor's
    pointer-overflow checks on in->p + 1 and in->p + n, pp & 7, the header and buf[len] bounds and pointer checks,
    the table index checks, e->body + n, r[k], ch + k, the record copy's n_ent++ / ent bound / object size, the
    corruption's buf[off + k]); each is dead by a premise of role_build_contract (src > 0 and the input bytes below
    2^64; pp 16-aligned with its block below lo; the bounds len <= 5440 and e_size <= 45 of the model, Pod/Model.v;
    sp + 0x1b8 < lo + 65536 <= 2^64). 6 lie in role_check's range (expect_role's &ent[*at] bound and pointer,
    body + size - 1, the overflow of at++, &ent[v] bound and pointer), dead by n_ent <= 32 and e_size <= 45 of the
    record in pp. pod_write_ent's 10 traps are its contract's (U/Prog/pod_write_ent_c.v).

    The callee contracts the walks take as premises (the released forms relocated to role's UBSan image, or written in
    this directory):
      S_E01: malloc through the frame's malloc_contract (ms_malloc = 0x160ec) by the slot's malloc step;
      role_build_contract: memset_contract (U/Prog/memset_c.v, 0x1ca4c), memcpy_contract (U/Prog/memcpy_c.v,
             0x1c648), strlen_contract (U/Prog/strlen_c.v, 0x1cb7c), pod_write_ent_contract
             (U/Prog/pod_write_ent_c.v, 0x14324; called at 0x131b4, 0x13c60, 0x13d6c), and the shared model's
             pod_build and pp_bytes with their step lemmas;
      S_M01: malloc again by the slot's malloc step (hb = [(pp, 19744)], request len);
      role_check_contract: memcpy_contract, reac_role_prop_parse_contract, strcmp_contract (U/Prog/strcmp_c.v,
             0x1cb44), pod_nearest_contract, check_absent_contract, check_role_contract, check_malformed_contract,
             reac_role_cfg_changes_contract, reac_role_cfg_apply_state_contract, check_answer_contract,
             reac_role_refuse_code_contract, check_code_contract (U/Prog/<fn>_c.v), and Pod/Role.v's
             parse_model_encode;
      S_X01: free(pod) and free(pp) through the frame's free_contract (ms_free = 0x15fac) by the slot's two free
             steps.
    Statement text only: no function is proved here. *)

Definition ROLE_BUILD : Z := 0x12f48.
Definition ROLE_MALLOC2 : Z := 0x13f30.
Definition ROLE_CHECK : Z := 0x13f34.
Definition ROLE_FREE : Z := 0x141b4.
(* The deepest callee stack below the harness sp: pod_nearest's 48-byte frame and __addtf3's 48 bytes. *)
Definition MID_STACK : Z := 96.
(* The harness frame below its saved registers: [sp, sp + 0x1b8) (the saves are at [sp + 0x1b8, sp + 0x220)). *)
Definition FRAME_LOCALS : Z := 0x1b8.
(* The absolute-pointer tables of .data.rel.ro the builder reads: vocab (0x1e100, 9 pointers), odd_ch (0x1e148,
   14 pointers) and param (0x1e1b8, 8 pointers), inside U/FrameAPI.frame_RELRO [0x1e0f0, 0x1e298). *)
Definition RELRO_TBL : Z := 0x1e100.
Definition RELRO_TBL_END : Z := 0x1e1f8.
(* reac_role_refuse_code's codes[] table, read by the checking segment: 2 absolute pointers in .data.rel.ro at
   0x1e1f8 (to "none" 0x103e0 and "malformed" 0x103d6), inside U/FrameAPI.frame_RELRO. *)
Definition CODES_TBL : Z := 0x1e1f8.
Definition CODES_TBL_END : Z := 0x1e208.

(* pp->len after pod_build of the bytes after the flags byte. *)
Definition role_len (rest : list byte) : Z := Z.of_nat (length (buf (fst (pod_build rest)))).

(** ** The builder segment as an evt: [0x12f48, 0x13f30)
    From malloc(pp)'s return (0x12f48 `bnez a0`; pp <> 0) to the second malloc's call (0x13f30 `jal malloc`, not
    executed). Registers at 0x12f48 as U/Prog/SlotInv.Inv_K12f48 names them: a0 = pp, s6 = src, s2 = the bytes left,
    the cell sp + 0x10 = fl, s1 = 19744, s0 = 0x5000. The plain evt's steps (memset(pp, 0, 19744) at 0x12f5c, the
    property loop 0x13160, the Struct pod loop 0x13360 with `jr a1` at 0x133cc through 0x10548, pod_write_ent calls,
    the record copy, the patches, the corruption 0x13e2c-0x13f24, len = pp->len at 0x13f1c, a0 = len + (len = 0) at
    0x13f28-0x13f2c), with no trap reached. It ends at 0x13f30 with a0 = s2 = len, s8 = pp, s7 = pp + 0x4000, the cells
    sp + 0x10 = fl, sp + 0x68 = pp, sp + 0x70 = pp + 0x4d14, the pp block = pp_bytes of the record, sp, gp, tp, F, fc
    unchanged, and no byte changed outside the callees' stack below sp, the frame's locals [sp, sp + 0x1b8) and the pp
    block. Premises as the plain evt's, with the flags cell for s5. *)
Definition role_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s6 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) -> 0 <= fl < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
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
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s9' s10' s11' t3' t4' t5'
                          t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (role_len rest)) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (role_len rest)) s3' s4' s5' s6' (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp)
                       s9' s10' s11' t3' t4' t5' t6')
                  F (Z_to_bv 64 ROLE_MALLOC2) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 pp)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_BUILD) fc None m (seg_rom rsegs)).

(** ** The checking segment as an evt: [0x13f34, 0x141b4)
    From malloc(pod)'s return (0x13f34 `ld s3,0x10(sp)`, then 0x13f38 `beqz a0`, the abort branch to 0x1421c not
    taken: pod <> 0) to the pc after check_code's return. Registers at 0x13f34 as U/Prog/SlotInv.Inv_K13f34 names
    them: a0 = pod, s2 = len, s8 = pp, s7 = pp + 0x4000; the cells sp + 0x10 = fl, sp + 0x68 = pp,
    sp + 0x70 = pp + 0x4d14; the pp block = pp_bytes r for the record r that pod_build made of some input. The plain
    evt's steps (memcpy 0x13f50, the role cell sp + 0x158 := 0x5a at 0x13f5c, the parse 0x13f6c, expect_role
    0x13f80-0x14138 with strcmp 0x14088 and pod_nearest(f, sp + 0xb8) 0x14128, check_absent 0x140f8 / check_role
    0x14214 / check_malformed 0x14144, req, check_answer 0x14190, check_code 0x141b0), with no trap reached. It ends at
    0x141b4 with s1 = pod, s8 = pp, sp, gp, tp unchanged, at some FP state with frm = 0, and no byte changed outside
    the callees' stack below sp, the frame's locals and the pod block. Premises as the plain evt's, MemNorm.task_mem
    included (the slot runs the evt on MemNorm.normalize_cj of the cut's memory), and one more: refuse_code reads its
    codes[] table from .data.rel.ro here (plain: a relative table in .rodata), so those 16 bytes read as the image
    (FR's relro). *)
Definition role_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (fl pp pod lo : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 -> pod mod 16 = 0 ->
    s2 = Z_to_bv 64 (role_len inp) -> s8 = Z_to_bv 64 pp -> s7 = Z_to_bv 64 (pp + POD_LEN_OFF) -> 0 <= fl < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) ->
    bytes_at rsegs m pp (pp_bytes (fst (pod_build inp))) ->
    rw_cells rsegs m pod [CB (Z.to_nat (role_len inp)) junk] ->
    (forall a, pod <= a < pod + role_len inp -> seg_rom rsegs (wa a) = None) ->
    (pod + role_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    pod + role_len inp <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, CODES_TBL <= a < CODES_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s9' s10' s11'
                          t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod) a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' s4' s5' s6' s7' (Z_to_bv 64 pp) s9' s10' s11' t3' t4' t5' t6')
                  F' (Z_to_bv 64 ROLE_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pod, pod + role_len inp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_CHECK) fc None m (seg_rom rsegs)).

(** ** The segment statements (as the plain file's, with the UBSan cuts)
    S_E01, ENTRY -> K12f48: the prologue (saves at [S - 104, S)); n < 2^26; the flags byte into the cell sp + 0x10 and
      the cursor (0x12f04-0x12f34; the trap 0x12f18 dead); malloc(19744) at 0x12f44 with ra = 0x12f48 by the slot's
      malloc step (hb = [] to [(pp, 19744)]).
    S_M01, K12f48 -> K13f34: role_build_contract (rest := g_rest g at g_src g, fl := g_fl g, lo := S - 65536,
      sp = S - 544), then `jal malloc` with a0 = g_len g by the slot's malloc step from hb = [(pp, 19744)], whose
      kept-bytes clause carries the pp block's bytes to the cut.
    S_M02, K13f34 -> K141b4: role_check_contract with inp := g_rest g.
    S_X01, K141b4 -> RET: free(pod) at 0x141b8 (ra = 0x141bc) and free(pp) at 0x141c0 (ra = 0x141c4) by the slot's
      free steps, `mv a0,zero`, the restores, `addi sp,sp,0x220`, ret: Post. *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K12f48 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K13f34 B APIf ra empty) -> Hcut B APIf ra (Inv_K12f48 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K141b4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13f34 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K141b4 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_X01.

End Stmts.
