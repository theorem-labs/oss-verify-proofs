(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own LbB_DStat LbB_ContStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition AT_FIXWORD        : Z := 0xfc800.
Definition AT_IS_HOST_ENDIAN : Z := 0xfc9a0.
Definition AT_OPCODE_SPLIT   : Z := 0xfda14.
Definition AT_OPCODE_STRING  : Z := 0xfdaa4.
Definition AT_GENERATES_TYPE : Z := 0xfdc6c.
Definition AT_IS_EXT_INST    : Z := 0xfdd80.
Definition AT_ODESC_OPERANDS : Z := 0xfdda0.
Definition AT_IDESC_OPERANDS : Z := 0xfde30.
Definition AT_IDESC_NAME     : Z := 0xfdec0.
Definition AT_EDESC_OPERANDS : Z := 0xfdf4c.
Definition AT_LOOKUP_OPCODE  : Z := 0xfdfdc.
Definition AT_LOOKUP_OPERAND : Z := 0xfe148.
Definition AT_LOOKUP_EXT     : Z := 0xfe7a4.
Definition AT_OPERAND_TYPE_STR : Z := 0xfea54.
Definition AT_PUSH_TYPES     : Z := 0xfeac0.
Definition AT_IS_OPTIONAL    : Z := 0xfef48.
Definition AT_EXPAND         : Z := 0xfef88.
Definition AT_TAKE_FIRST     : Z := 0xffe68.
Definition AT_FPENC          : Z := 0xfffc4.
Definition AT_SPEC_LOOKUP    : Z := 0x1002b4.
Definition AT_IMPORT_TYPE_GET : Z := 0x100350.
Definition AT_IS_NONSEMANTIC : Z := 0x1005f8.

Definition TSTR_A : list (Z * Z) := [
  (0x61920, 4); (0x60480, 2); (0x604a0, 7); (0x604c0, 9); (0x60a00, 19); (0x60a80, 8); (0x604e0, 14); (0x605c0, 28);
  (0x60600, 23); (0x60560, 34); (0x604e0, 14); (0x60640, 14); (0x60660, 15); (0x60680, 15); (0x606a0, 16); (0x606e0, 12);
  (0x60700, 14); (0x60720, 13); (0x60740, 14); (0x60760, 23); (0x607a0, 19); (0x607e0, 12); (0x61440, 19); (0x61480, 23);
  (0x60840, 28); (0x60880, 12); (0x608a0, 16); (0x608e0, 28); (0x60920, 10); (0x60940, 8); (0x60aa0, 15); (0x60ac0, 19);
  (0x60b00, 21); (0x60b40, 10); (0x61420, 11); (0x61060, 5); (0x60800, 29); (0x60960, 17); (0x609a0, 12); (0x609c0, 16);
  (0x60a40, 13); (0x60a60, 12); (0x60480, 2); (0x61060, 5); (0x60a40, 13); (0x604e0, 14); (0x604e0, 14); (0x60500, 35);
  (0x60640, 14); (0x608a0, 16); (0x61080, 25); (0x61420, 11); (0x61940, 7); (0x61940, 7); (0x61940, 7); (0x61940, 7);
  (0x610c0, 16); (0x61100, 24); (0x61140, 20); (0x61180, 20); (0x611c0, 15); (0x611e0, 37); (0x61240, 45); (0x612a0, 41);
  (0x61300, 41); (0x61360, 36); (0x613c0, 42); (0x614c0, 14); (0x614e0, 17); (0x61520, 17); (0x61560, 13); (0x60b60, 9);
  (0x60b80, 22); (0x60bc0, 37); (0x60c20, 37); (0x60c80, 20); (0x60c80, 20); (0x60cc0, 27); (0x60cc0, 27); (0x60d00, 25);
  (0x60d40, 22); (0x60ec0, 29); (0x60f00, 21); (0x60f40, 18); (0x60f80, 19); (0x60fc0, 33); (0x61020, 25); (0x61020, 25);
  (0x60d80, 17); (0x60dc0, 25); (0x60e00, 26); (0x60e40, 35); (0x60e40, 35); (0x61580, 32); (0x615e0, 14); (0x61600, 21);
  (0x61640, 61); (0x616a0, 67); (0x61720, 53); (0x61780, 54); (0x617e0, 49); (0x61840, 48); (0x618a0, 53); (0x60ea0, 15);
  (0x60ea0, 15); (0x60b40, 10); (0x61940, 7); (0x61900, 12) ].

Definition tiA : tabl_img := {|
  ti_spans   := 0x25260;
  ti_strings := 0x268c0;
  ti_insn    := 0x381c0;
  ti_opnd    := 0x48260;
  ti_ext     := 0x5be80;
  ti_spec    := 0x17ef40;
  ti_tstr    := TSTR_A;
  ti_tstr_dflt := (0x61940, 7);
  ti_ro_lo   := 0x10000;
  ti_ro_hi   := 0x91000
|}.

Definition idescA (d op : Z) : Prop := TablRep.idesc tiA d op.
Definition odescA (d t v : Z) : Prop := TablRep.odesc tiA d t v.
Definition edescA (d e v : Z) : Prop := TablRep.edesc tiA d e v.

Definition tvis (m : mem) : Prop := mem_inv asegs m /\ ACONST m.

Definition spanA (p : Z) (l : list Z) : Prop :=
  0x10000 <= p /\ p + 4 * Zlen l <= 0x91000 /\ p mod 4 = 0 /\
  forall m, tvis m ->
    (forall i, 0 <= i < Zlen l -> 0 <= Znth i l < 2 ^ 32 /\ fld asegs m (p + 4 * i) 4 (Znth i l))
    /\ accessible m p (4 * Zlen l).

Definition cstrA (p n : Z) : Prop :=
  AIMG_LO + 64 <= p /\ 0 <= n <= 256 /\ p + n + 1 <= 0x91000 /\ in_app_mem p (p + n + 1) /\
  (forall m, ACONST m -> accessible m p (n + 1) /\ shvis m p (p + n + 1)) /\
  (forall m, mem_inv asegs m -> exists (str slack : list byte),
      bytes_at asegs m p (str ++ Z_to_bv 8 0 :: slack) /\ Z.of_nat (length str) = n /\ ~ In (Z_to_bv 8 0) str
      /\ (- (p + n + 1)) mod 8 <= Z.of_nat (length slack)).

Definition tstrA_of (x : Z) : Z * Z :=
  if ((0 <=? x) && (x <? 108))%bool then nth (Z.to_nat x) (ti_tstr tiA) (0, 0) else ti_tstr_dflt tiA.

Definition sx32A (x : Z) : Z := PrsGrammar.sx32 x.

Section Leaves.
  Context {HCEIL : HeapCeil}.

  Definition TL_STACK : Z := 64.

  Definition tl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (STK : Z) (W : list (Z * Z)) (lo : Z) (m : mem) (Q : word -> word -> mem -> Prop) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch ((bv_unsigned sp - STK, bv_unsigned sp) :: W) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
      /\ Q a0 a1 m'.

  Definition tleaf {X : Type} (entry STK : Z) (PRE : X -> mem -> Z -> word -> word -> word -> word -> Prop)
      (W : X -> list (Z * Z)) (Q : X -> mem -> word -> word -> mem -> Prop) : Prop :=
    forall (x : X) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - STK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      mem_inv asegs m -> ACONST m ->
      PRE x m (bv_unsigned sp) a0 a1 a2 a3 ->
      evt asegs (tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc STK (W x) lo m (Q x m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition tl_cell (m : mem) (sp a n : Z) : Prop :=
    wr_at asegs m a n /\ accessible m a n /\ aconst_ok (a, a + n) /\ (a + n <= sp - TL_STACK \/ sp <= a)
    /\ ((0x6e8000 <= a /\ a + n <= 0x7fff7000) \/ (0x10007fff8000 <= a /\ a + n <= 2 ^ 47)).

  Definition fixword_stmtA : Prop :=
    @tleaf (Z * Z) AT_FIXWORD 0
      (fun '(w, e) _ _ a0 a1 _ _ => 0 <= w < 2 ^ 32 /\ a0 = Z_to_bv 64 (sx32A w) /\ 0 <= e < 2 ^ 32 /\ a1 = Z_to_bv 64 e)
      (fun _ => [])
      (fun _ _ r0 _ _ => exists r, 0 <= r < 2 ^ 32 /\ r0 = Z_to_bv 64 (sx32A r)).

  Definition is_host_endian_stmtA : Prop :=
    @tleaf Z AT_IS_HOST_ENDIAN 0
      (fun x _ _ a0 _ _ _ => 0 <= x < 2 ^ 32 /\ a0 = Z_to_bv 64 x)
      (fun _ => [])
      (fun _ _ r0 _ _ => exists r, (r = 0 \/ r = 1) /\ r0 = Z_to_bv 64 r).

  Definition bool_leafA (pc : Z) (P : Z -> Prop) : Prop :=
    @tleaf Z pc 0
      (fun x _ _ a0 _ _ _ => 0 <= x < 2 ^ 32 /\ a0 = Z_to_bv 64 x)
      (fun _ => [])
      (fun x _ r0 _ _ => exists b : bool, r0 = Z_to_bv 64 (if b then 1 else 0) /\ (b = true -> P x)).
  Definition generates_type_stmtA : Prop := bool_leafA AT_GENERATES_TYPE (fun x => tg_generates_type x = true).
  Definition is_ext_inst_stmtA : Prop := bool_leafA AT_IS_EXT_INST (fun _ => True).
  Definition is_optional_stmtA : Prop := bool_leafA AT_IS_OPTIONAL (fun x => 42 <= x).
  Definition is_nonsemantic_stmtA : Prop := bool_leafA AT_IS_NONSEMANTIC (fun _ => True).

  Definition fpenc_stmtA : Prop :=
    @tleaf unit AT_FPENC 0 (fun _ _ _ _ _ _ _ => True) (fun _ => [])
      (fun _ _ r0 _ _ => exists r, 0 <= r < 16 /\ r0 = Z_to_bv 64 r).

  Definition operand_type_str_stmtA : Prop :=
    @tleaf Z AT_OPERAND_TYPE_STR TL_STACK
      (fun x m _ a0 _ _ _ => 0 <= x < 2 ^ 32 /\ a0 = Z_to_bv 64 x /\ relro0 m)
      (fun _ => [])
      (fun x _ r0 _ _ => exists p n, cstrA p n /\ r0 = Z_to_bv 64 p /\ (p, n) = tstrA_of x).

  Definition idesc_name_stmtA : Prop :=
    @tleaf (Z * Z) AT_IDESC_NAME TL_STACK
      (fun '(d, op) _ _ a0 _ _ _ => idescA d op /\ a0 = Z_to_bv 64 d)
      (fun _ => [])
      (fun _ _ r0 _ _ => exists p n, cstrA p n /\ r0 = Z_to_bv 64 p).

  Definition idesc_operands_stmtA : Prop :=
    @tleaf (Z * Z) AT_IDESC_OPERANDS TL_STACK
      (fun '(d, op) _ _ a0 _ _ _ => idescA d op /\ a0 = Z_to_bv 64 d)
      (fun _ => [])
      (fun '(d, op) _ r0 r1 _ => exists p l, g_op TG op = Some l /\ spanA p l /\ r0 = Z_to_bv 64 p /\ r1 = Z_to_bv 64 (Zlen l)).
  Definition odesc_operands_stmtA : Prop :=
    @tleaf (Z * Z * Z) AT_ODESC_OPERANDS TL_STACK
      (fun '(d, t, v) _ _ a0 _ _ _ => odescA d t v /\ a0 = Z_to_bv 64 d)
      (fun _ => [])
      (fun '(d, t, v) _ r0 r1 _ => exists p l, g_operand TG t v = Some l /\ spanA p l /\ r0 = Z_to_bv 64 p /\ r1 = Z_to_bv 64 (Zlen l)).
  Definition edesc_operands_stmtA : Prop :=
    @tleaf (Z * Z * Z) AT_EDESC_OPERANDS TL_STACK
      (fun '(d, e, v) _ _ a0 _ _ _ => edescA d e v /\ a0 = Z_to_bv 64 d)
      (fun _ => [])
      (fun '(d, e, v) _ r0 r1 _ => exists p l, g_ext TG e v = Some l /\ spanA p l /\ r0 = Z_to_bv 64 p /\ r1 = Z_to_bv 64 (Zlen l)).

  Definition opcode_split_stmtA : Prop :=
    @tleaf (Z * Z * Z) AT_OPCODE_SPLIT TL_STACK
      (fun '(w, pwc, pop) m sp a0 a1 a2 _ =>
         0 <= w < 2 ^ 32 /\ a0 = Z_to_bv 64 (sx32A w) /\ a1 = Z_to_bv 64 pwc /\ a2 = Z_to_bv 64 pop /\
         pwc mod 2 = 0 /\ pop mod 2 = 0 /\ tl_cell m sp pwc 2 /\ tl_cell m sp pop 2 /\ (pwc + 2 <= pop \/ pop + 2 <= pwc))
      (fun '(w, pwc, pop) => [(pwc, pwc + 2); (pop, pop + 2)])
      (fun '(w, pwc, pop) _ _ _ m' => rw_cells asegs m' pwc [C2 (Z_to_bv 64 (w / 2 ^ 16))]
                                      /\ rw_cells asegs m' pop [C2 (Z_to_bv 64 (w mod 2 ^ 16))]).

  Definition lookup_shapeA (pc : Z) (nargs : nat) (found : Z -> Z -> Prop) (hnd : Z -> Z -> Z -> Prop) : Prop :=
    @tleaf (Z * Z * Z) pc TL_STACK
      (fun '(x, y, pd) m sp a0 a1 a2 _ =>
         0 <= x < 2 ^ 32 /\ a0 = Z_to_bv 64 x /\
         (nargs = 2%nat -> a1 = Z_to_bv 64 pd) /\
         (nargs = 3%nat -> a1 = Z_to_bv 64 (sx32A y) /\ 0 <= y < 2 ^ 32 /\ a2 = Z_to_bv 64 pd) /\
         pd mod 8 = 0 /\ tl_cell m sp pd 8)
      (fun '(x, y, pd) => [(pd, pd + 8)])
      (fun '(x, y, pd) m r0 _ m' => exists r, r0 = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
         /\ (r = 0 <-> found x y)
         /\ (r = 0 -> exists d, rw_cells asegs m' pd [C8 (Z_to_bv 64 d)] /\ hnd d x y)
         /\ (r <> 0 -> forall a, pd <= a < pd + 8 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a))).
  Definition lookup_opcode_stmtA : Prop :=
    lookup_shapeA AT_LOOKUP_OPCODE 2 (fun op _ => exists l, g_op TG op = Some l) (fun d op _ => idescA d op).
  Definition lookup_operand_stmtA : Prop :=
    lookup_shapeA AT_LOOKUP_OPERAND 3 (fun t v => exists l, g_operand TG t v = Some l) (fun d t v => odescA d t v).
  Definition lookup_ext_stmtA : Prop :=
    lookup_shapeA AT_LOOKUP_EXT 3 (fun e v => exists l, g_ext TG e v = Some l) (fun d e v => edescA d e v).

  Definition spec_lookup_stmtA : Prop :=
    @tleaf Z AT_SPEC_LOOKUP TL_STACK
      (fun op m _ _ a1 _ _ => 0 <= op < 2 ^ 31 /\ a1 = Z_to_bv 64 op /\ relro0 m)
      (fun _ => [])
      (fun op _ r0 _ _ => exists r, r0 = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31 /\ (r = 0 <-> g_specop TG op = true)).
End Leaves.

Record tabl_leavesA {HCEIL : HeapCeil} : Prop := TABL_LEAVES_A {
  tla_fixword : fixword_stmtA;
  tla_is_host_endian : is_host_endian_stmtA;
  tla_generates_type : generates_type_stmtA;
  tla_is_ext_inst : is_ext_inst_stmtA;
  tla_is_optional : is_optional_stmtA;
  tla_is_nonsemantic : is_nonsemantic_stmtA;
  tla_fpenc : fpenc_stmtA;
  tla_operand_type_str : operand_type_str_stmtA;
  tla_idesc_name : idesc_name_stmtA;
  tla_idesc_operands : idesc_operands_stmtA;
  tla_odesc_operands : odesc_operands_stmtA;
  tla_edesc_operands : edesc_operands_stmtA;
  tla_opcode_split : opcode_split_stmtA;
  tla_lookup_opcode : lookup_opcode_stmtA;
  tla_lookup_operand : lookup_operand_stmtA;
  tla_lookup_ext : lookup_ext_stmtA;
  tla_spec_lookup : spec_lookup_stmtA
}.

Definition PT_STACK : Z := 224 + AFS_STACK + AINTRIN_STACK + V4_STACK.
Definition TF_STACK : Z := 80 + 192 + AFS_STACK + 2 * AINTRIN_STACK + 2 * V4_STACK.
Definition OS_STACK : Z := 96 + AFS_STACK + TL_STACK.
Definition IT_STACK : Z := 16 + AINTRIN_STACK.

Definition capmax (len cap k : Z) : Z := Z.max cap (2 * (len + k)).

Section SR.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition span_keep (LB : list block) (LF : list fframe) (spz : Z) (X : list (Z * Z)) (m : mem) (ps p n : Z) : Prop :=
    forall (XS : list (Z * Z)) m', Forall (fs_scratch H LF) XS -> ACONST m' -> mem_inv asegs m' -> xpres H LB spz (X ++ XS) m m' ->
      rw_cells asegs m' ps [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n)] /\ accessible m' ps 16.

  Definition grown (LB LB' : list block) (spz : Z) (XS : list (Z * Z)) (v b cap b' cap' capm : Z) (pid : bptr)
      (m m' : mem) : Prop :=
    (cap' = cap /\ b' = b /\ LB' = LB
     /\ xpres H LB spz ((v, v + 24) :: (b, b + 4 * cap) :: (sh b, sh b + nsh (4 * cap)) :: XS) m m')
    \/ (cap < cap' <= capm /\ (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * cap') /\ ablock_range H b' (4 * cap'))
        /\ xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap) ++ XS) m m').

  Definition pat_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (v b cap capm : Z) (ys : list Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) (R0 : word -> Prop) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                     (b' cap' : Z) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ R0 a0
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ vec32A LB' m' v b' ys cap' /\ as_RHEAP H s' LB' m'
      /\ (0 < cap' -> SHAD m' b' (cc_gen (4 * cap') (4 * Zlen ys)))
      /\ addressable m' v 24 /\ wr_at asegs m' v 24 /\ lb_own LB' m'
      /\ Forall (fs_scratch H LF) XS
      /\ grown LB LB' (bv_unsigned sp) XS v b cap b' cap' capm pid m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - closs cap cap'.

  Definition pat_pre (ra sp tp : word) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
      (LF : list fframe) (v b cap capm : Z) (xs : list Z) (pid : bptr) (lo B shi STK : Z) (errv : word) : Prop :=
      vec32A LB m v b xs cap /\ v mod 8 = 0
      /\ addressable m v 24 /\ obj_win H LB LF (bv_unsigned sp) lo v 24
      /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47))
      /\ wr_at asegs m v 24 /\ lb_own LB m
      /\ v4_oldblk LB b cap pid /\ (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs)))

      /\ (4 * capm <= 2 ^ 26 /\ closs cap capm <= as_AL H s)
      /\ lb_small LB + 3 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX
      /\ as_RHEAP H s LB m /\ as_AKREL H s (mkCfg msF mo) /\ 0 <= as_AL H s
      /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]
      /\ as_rauxv_ok H m B /\ bv_unsigned sp <= B
      /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= 2 ^ 47
      /\ stk asegs m lo (bv_unsigned sp) /\ aceil <= lo /\ lo <= bv_unsigned sp - STK
      /\ rw_cells asegs m (errno_addr tp) [C4 errv] /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP
      /\ bv_unsigned ra mod 2 = 0
      /\ ACONST m /\ as_RFS H LF m /\ (length LF < AFS_MAXLIVE_BP)%nat
      /\ stack0 m lo shi /\ bv_unsigned sp <= shi.

  Definition push_types_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (pspan p v b cap : Z) (l xs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 AT_PUSH_TYPES) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 pspan -> a1 = Z_to_bv 64 v ->

      span_keep LB LF (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (4 * cap)) m pspan p (Zlen l) -> pspan mod 8 = 0 ->
      (pspan + 16 <= v \/ v + 24 <= pspan) ->
      spanA p l -> Zlen l <= 48 -> Forall (fun t => 0 <= t < 2 ^ 31) l ->
      (pspan + 16 <= lo \/ bv_unsigned sp <= pspan) -> relro0 m ->
      pat_pre ra sp tp msF m mo s LB LF v b cap (capmax (Zlen xs) cap (Zlen l)) xs pid lo B shi PT_STACK errv ->
      as_SR H (pat_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap (capmax (Zlen xs) cap (Zlen l))
                        (push_types l xs) pid lo B shi m mo (fun _ => True))
        (mkCfg msF mo).

  Definition take_first_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (v b cap : Z) (xs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 AT_TAKE_FIRST) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v ->
      xs <> [] -> Forall (fun t => 0 <= t < 2 ^ 31) xs -> relro0 m ->
      pat_pre ra sp tp msF m mo s LB LF v b cap (capmax (Zlen xs - 1) cap 3) xs pid lo B shi TF_STACK errv ->
      as_SR H (pat_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap (capmax (Zlen xs - 1) cap 3)
                        (snd (take_first xs)) pid lo B shi m mo (fun r0 => r0 = Z_to_bv 64 (fst (take_first xs))))
        (mkCfg msF mo).

  Definition opcode_string_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)) (p n : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ a0 = Z_to_bv 64 p /\ cstrA p n
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((bv_unsigned sp - OS_STACK, bv_unsigned sp) :: XS) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ as_RFS H LF m' /\ ACONST m' /\ as_RHEAP H s LB m'.
  Definition opcode_string_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe) (op lo : Z),
      a0 = Z_to_bv 64 op -> 0 <= op < 2 ^ 32 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - OS_STACK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> as_RHEAP H s LB m ->
      mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> relro0 m ->
      evt asegs (opcode_string_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AT_OPCODE_STRING) fc None m (seg_rom asegs)).

  Definition import_type_get_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (str : list byte) (q lo : Z),
      a0 = Z_to_bv 64 q ->
      bytes_at asegs m q (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
      accessible m q (Z.of_nat (length str) + 1) -> shvis m q (q + Z.of_nat (length str) + 1) ->
      in_app_mem q (q + Z.of_nat (length str) + 1) -> Z.of_nat (length str) + 1 <= 2 ^ 40 ->
      (q + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= q) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - IT_STACK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc IT_STACK [] lo m
                   (fun r0 _ _ => exists r, 0 <= r < 2 ^ 31 /\ r0 = Z_to_bv 64 r))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AT_IMPORT_TYPE_GET) fc None m (seg_rom asegs)).
End SR.
