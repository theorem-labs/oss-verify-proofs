From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition AHDR_GET : Z := 0xea2b4.
Definition HG_STACK : Z := 64.
Definition HG_INVALID_BINARY : Z := -4.

Definition hg_ver_ok (v : Z) : Prop := Z.land v 0xff0000ff = 0 /\ 0x10000 <= v <= 0x10600.

Section HG.
  Context {HCEIL : HeapCeil}.

  Definition hg_pre (x : Z * Z * Z * Z * Z * list Z) (m : mem) (sp : Z) (a0 a1 a2 a3 : word) : Prop :=
    let '(b, code, n, e, h, ws) := x in
    a0 = Z_to_bv 64 b /\ a1 = Z_to_bv 64 e /\ a2 = Z_to_bv 64 h
    /\ fld ASEGS m b 8 code /\ fld ASEGS m (b + 8) 8 n /\ b mod 8 = 0 /\ addressable m b 16
    /\ AIMG_TOP <= b /\ b + 16 <= 2 ^ 47 /\ (b + 16 <= sp - HG_STACK \/ sp <= b)
    /\ (e = 0 \/ e = 1)
    /\ h mod 8 = 0 /\ tl_cell m sp h 32 /\ addressable m h 32 /\ (h + 32 <= b \/ b + 16 <= h)
    /\ AIMG_TOP <= code /\ code mod 4 = 0 /\ code + 20 <= 2 ^ 47 /\ (code + 20 <= sp - HG_STACK \/ sp <= code)
    /\ 5 <= n /\ Zlen ws = 5 /\ (forall i, 0 <= i < 5 -> fld ASEGS m (code + 4 * i) 4 (Znth i ws)) /\ addressable m code (4 * n)
    /\ (h + 32 <= code \/ code + 20 <= h).

  Definition hg_win (x : Z * Z * Z * Z * Z * list Z) : list (Z * Z) :=
    let '(_, _, _, _, h, _) := x in [(h, h + 32)].

  Definition hg_post (x : Z * Z * Z * Z * Z * list Z) (m : mem) (r0 r1 : word) (m' : mem) : Prop :=
    let '(b, code, n, e, h, ws) := x in
    (r0 = Z_to_bv 64 0
     /\ exists mg ver gen bnd sch : Z,
          0 <= mg < 2 ^ 32 /\ 0 <= ver < 2 ^ 32 /\ 0 <= gen < 2 ^ 32 /\ 0 <= bnd < 2 ^ 32 /\ 0 <= sch < 2 ^ 32
          /\ hg_ver_ok ver
          /\ rw_cells asegs m' h [C4 (Z_to_bv 64 mg); C4 (Z_to_bv 64 ver); C4 (Z_to_bv 64 gen); C4 (Z_to_bv 64 bnd);
                                 C4 (Z_to_bv 64 sch)]
          /\ rw_cells asegs m' (h + 24) [C8 (Z_to_bv 64 (code + 20))])
    \/ r0 = Z_to_bv 64 HG_INVALID_BINARY.

  Definition hdr_get_stmt : Prop := @tleaf HCEIL (Z * Z * Z * Z * Z * list Z) AHDR_GET HG_STACK hg_pre hg_win hg_post.
End HG.
