From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRop2Segs.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section GSpec.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition rg_blk (MB : word -> option byte) (s datad nd datas ns : Z) : Prop :=
  (250000 <= s /\ s + 64 < 2 ^ 64)%Z /\
  (4096 <= datad /\ 0 < nd /\ datad + nd + 2 ^ 27 <= 2 ^ 64 /\ datad mod 4 = 0)%Z /\
  (4096 <= datas /\ 0 < ns /\ datas + ns + 2 ^ 27 <= 2 ^ 64 /\ datas mod 4 = 0)%Z /\
  store_ok SEGS MB (Z_to_bv 64 datad) (Z.to_nat nd) = true /\ store_ok SEGS MB (Z_to_bv 64 datas) (Z.to_nat ns) = true /\
  store_ok SEGS MB (Z_to_bv 64 (s - 240)) 240 = true /\ disj_apart datad nd (s - 240) 240.

Definition rg_geo (datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl : Z) (fw f6 f7 nofull nolast f3 : bool) : Prop :=
  (1 <= dh < 2 ^ 24 /\ 0 <= swpl < 2 ^ 24 /\ 0 <= dwpl < 2 ^ 24 /\ 1 <= sls <= 31 /\ 0 <= nfw < 2 ^ 26)%Z /\
  ((0 <= dxb < 32)%Z /\ (if fw then dxb <> 0 else dxb = 0)%Z) /\
  (nofull = false -> (1 <= nfw)%Z) /\
  (fw = true -> (psf mod 4 = 0 /\ pdf mod 4 = 0)%Z /\
    (forall i, 0 <= i < dh -> datad <= pdf + 4 * dwpl * i /\ pdf + 4 * dwpl * i + 4 <= datad + nd /\
                              datas <= psf + 4 * swpl * i /\ psf + 4 * swpl * i + 4 + (if f6 && negb f7 then 4 else 0) <= datas + ns)%Z) /\
  (nofull = false -> (psF mod 4 = 0 /\ pdF mod 4 = 0)%Z /\
    (forall i, 0 <= i < dh -> datad <= pdF + 4 * dwpl * i /\ pdF + 4 * dwpl * i + 4 * nfw <= datad + nd /\
                              datas <= psF + 4 * swpl * i /\ psF + 4 * swpl * i + 4 * nfw + 4 <= datas + ns)%Z) /\
  (nolast = false -> (psl mod 4 = 0 /\ pdl mod 4 = 0)%Z /\
    (forall i, 0 <= i < dh -> datad <= pdl + 4 * dwpl * i /\ pdl + 4 * dwpl * i + 4 <= datad + nd /\
                              datas <= psl + 4 * swpl * i /\ psl + 4 * swpl * i + 4 + (if f3 then 0 else 4) <= datas + ns)%Z).

Definition rg_cells (MB : word -> option byte) (s dh swpl nfw psl : Z) (fw f6 nofull nolast f3 : bool) : Prop :=
  rdn SEGS MB (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0))) /\
  rdn SEGS MB (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))) /\
  rdn SEGS MB (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
  rdn SEGS MB (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn SEGS MB (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) /\
  (fw = true \/ nolast = false -> rg_rows MB s dh) /\
  (fw = true -> rdn SEGS MB (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0)))) /\
  (nofull = false -> rdn SEGS MB (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw))) /\
  (nolast = false -> rdn SEGS MB (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0)))) /\
  (nolast = false -> rdn SEGS MB (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl))) /\
  (nolast = false -> exists mk : word, rdn SEGS MB (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk)).

Definition rg_regs (regs : bvmap 5 word) (s dxb dwpl sls psf pdf psF pdF pdl : Z) (fw f7 nofull nolast : bool) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 1 = Z_to_bv 64 dxb /\ getr regs 14 = Z_to_bv 64 dwpl /\
  getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls) /\
  (fw = true -> getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0)) /\
  (nofull = false -> getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF) /\
  (nolast = false -> getr regs 10 = Z_to_bv 64 pdl).

Definition rg_inv (MB Mi : word -> option byte) (s datad nd : Z) : Prop :=
  (forall x : word, (u x < datad \/ datad + nd <= u x)%Z -> (u x < s - 240 \/ s - 112 <= u x)%Z -> Mi x = MB x) /\ mem_grows MB Mi.

Definition rg_loops_spec (ENTRY : word) : Prop :=
  forall (MB rom : word -> option byte) (s datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl : Z)
    (fw f6 f7 nofull nolast f3 : bool) (regs : bvmap 5 word),
  rg_blk MB s datad nd datas ns ->
  rg_geo datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl fw f6 f7 nofull nolast f3 ->
  rg_cells MB s dh swpl nfw psl fw f6 nofull nolast f3 ->
  rg_regs regs s dxb dwpl sls psf pdf psF pdF pdl fw f7 nofull nolast ->
  exists regs' M',
    msteps SEGS (mkst regs ENTRY MB rom) (mkst regs' RG_E M' rom)
    /\ rg_inv MB M' s datad nd /\ getr regs' 2 = Z_to_bv 64 (s - 240)
    /\ regs_agree (fun r : reg => In r [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.

End GSpec.
