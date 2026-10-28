From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_y4_kit_reload RF_huf_fdw_kit_dsym RF_huf_fdw_cut.
Import ListNotations.
Open Scope Z_scope.

Definition PFDW_D : Z := 0x2027c.

Definition fdw_fmb_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (m1 : fmem) (out : list Z) (s1 s2 c bits p : Z) (jp : list byte)
         (o0 s1a o1 s2a o2 s1b o3 s2b : Z) (d1 d2 d3 d4 : bitD) (y1 y22 y23 y24 y25 y26 y27 : word),
  fdw_pre SP S DT DST dcap lo bs dt ->
  Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt) ->
  decode_sym dt true s1 (mkBD c bits p false) = Ok (o0, s1a, d1) -> decode_sym dt true s2 d1 = Ok (o1, s2a, d2) ->
  decode_sym dt true s1a d2 = Ok (o2, s1b, d3) -> decode_sym dt true s2a d3 = Ok (o3, s2b, d4) ->
  0 <= bits < 8 -> 0 <= c < 2^64 -> 0 <= p -> p + 8 <= Z.max 8 (zlen bs) -> (zlen bs < 8 -> p = 0) ->
  zlen out + 4 <= dcap -> Forall (fun v => 0 <= v < 256) out ->
  0 <= s1 < 2^(dt_tableLog dt) -> 0 <= s2 < 2^(dt_tableLog dt) ->
  fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 (mkBD c bits p false)) jp ->
  fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4) ->
  evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1) (Z_to_bv 64 s2) (Z_to_bv 64 bits) (Z_to_bv 64 DST)
                          (Z_to_bv 64 (DST + zlen out)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S)
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1))
                          (Z_to_bv 64 (S + p)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + dcap - 3))
                          (Z_to_bv 64 1) y22 y23 y24 y25 y26 y27
                          (Z_to_bv 64 c) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                      F (Z_to_bv 64 PFDW_D) fc None m1 (seg_rom usegs)).
