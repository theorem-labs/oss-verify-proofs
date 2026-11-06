(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require RelocLept.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.OL Require CmapFill.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15Kit.
Module O15CmapFill.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import O15Kit.
(* [comment removed for export] *)











Import O15Kit.O15Reloc. Import O15Kit.O15RelocCode. Import O15Kit.O15RelocSites. Import O15Kit.O15RelocImg. Import O15Kit.O15RelocOL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Definition CMAP_CLOB : list nat := [10; 11; 12; 13; 14; 15; 16; 21; 23]%nat.
Section CF.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables cmap dp nc arr nalloc : Z.
Variable bs : list byte.
#[local] Notation data := (dp - 3)%Z (only parsing).
Hypothesis Hcmap : (1 <= cmap /\ cmap + 24 <= 2 ^ 64)%Z.
Hypothesis Hnc : (1 <= nc <= 256)%Z.
Hypothesis Hnal : (nc <= nalloc <= 256)%Z.
Hypothesis Harr : (1 <= arr /\ arr + 4 * nalloc <= 2 ^ 64)%Z.
Hypothesis Hdat : (3 <= dp /\ dp - 3 + 4 * nc <= 2 ^ 64)%Z.
Hypothesis Carr : rdn SEGS M (Z_to_bv 64 cmap) 8 = Some (Z_to_le_bytes 8 arr).
Hypothesis Cnal : rdn SEGS M (Z_to_bv 64 (cmap + 12)) 4 = Some (Z_to_le_bytes 4 nalloc).
Hypothesis Cn0 : rdn SEGS M (Z_to_bv 64 (cmap + 16)) 4 = Some (Z_to_le_bytes 4 0).
Hypothesis Dbs : rdn SEGS M (Z_to_bv 64 (dp - 3)) (Z.to_nat (4 * nc)) = Some bs.
Hypothesis SOKa : store_ok SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * nalloc)) = true.
Hypothesis SOKc : store_ok SEGS M (Z_to_bv 64 cmap) 24 = true.
Hypothesis A_ca : (cmap + 24 <= arr \/ arr + 4 * nalloc <= cmap)%Z.
Hypothesis A_cd : (cmap + 24 <= dp - 3 \/ dp - 3 + 4 * nc <= cmap)%Z.
Hypothesis A_ad : (arr + 4 * nalloc <= dp - 3 \/ dp - 3 + 4 * nc <= arr)%Z.
Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof. rl_tail (@CmapFill.lez8). Qed.

End CF.

Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill 0x18f78 0x18e7c 9 21 3 23 [(8%nat, 4%Z); (20%nat, 4%Z)] CMAP_CLOB).
Proof. rl_tail (@CmapFill.cmapfill_contract fx o15_reloc o15_code_ol). Qed.

End VPORT.
End O15CmapFill.

From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLoop.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptCmapArr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRmcLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15LeptRmcSegs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15LeptRmcFP.
Module O15LeptRmcLoops.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLoop.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptCmapArr.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRmcLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptRmcSegs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptRmcFP.
(* [comment removed for export] *)







Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Lemma wr_readable_s15 : forall {fx : FPState}, wr_readable SEGS.
Proof.
  intros fx seg Hin Hw. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hw] |]). destruct Hin.
Qed.

Lemma pcw : forall z : Z, (0 <= z < 2 ^ 64)%Z -> forall w : word, bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z Hz w <-. apply zbv_self. Qed.

Section Loops.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmc_fill_loop : forall (k : nat) (fx : FPState) regs (M0 M : word -> option byte) (g rm gm bm n i : Z),
  frm_zero (@fp_csr fx) -> Z.of_nat k = (n - i)%Z -> (0 <= i < n)%Z -> (n <= 256)%Z ->
  (0 <= g)%Z -> (g + 1024 < 2 ^ 63)%Z -> (0 <= rm)%Z -> (rm + 1024 < 2 ^ 63)%Z -> (0 <= gm)%Z -> (gm + 1024 < 2 ^ 63)%Z -> (0 <= bm)%Z -> (bm + 1024 < 2 ^ 63)%Z ->
  store_ok SEGS M0 (Z_to_bv 64 g) 1024 = true ->
  arr255 SEGS M0 rm n -> arr255 SEGS M0 gm n -> arr255 SEGS M0 bm n ->
  (g + 1024 <= rm \/ rm + 4 * n <= g)%Z -> (g + 1024 <= gm \/ gm + 4 * n <= g)%Z -> (g + 1024 <= bm \/ bm + 4 * n <= g)%Z ->
  rinv [(g, 1024%Z)] M0 M ->
  getr regs 11 = Z_to_bv 64 (rm + 4 * i) -> getr regs 12 = Z_to_bv 64 (gm + 4 * i) -> getr regs 13 = Z_to_bv 64 (bm + 4 * i) ->
  getr regs 15 = Z_to_bv 64 (g + 4 * i) -> getr regs 14 = Z_to_bv 64 (g + 4 * n) ->
  exists fr' cs' regs' M',
    msteps SEGS (@mkst fx regs (0x1994c : word) M rom) (@mkst (mkFP fr' cs') regs' (0x19994 : word) M' rom)
    /\ frm_zero cs' /\ rinv [(g, 1024%Z)] M0 M'
    /\ regs_agree (fun r => In r [11; 12; 13; 15; 16; 17]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros fx regs M0 M g rm gm bm n i Hz Hk Hi Hn Hg Hg63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 SOK Ar Ag Ab APr APg APb RI H11 H12 H13 H15 H14; [lia|].
  assert (CELL : forall p, (0 <= p)%Z -> (p + 1024 < 2 ^ 63)%Z -> arr255 SEGS M0 p n -> (g + 1024 <= p \/ p + 4 * n <= g)%Z ->
                 exists bs, rdn SEGS M (Z_to_bv 64 (p + 4 * i)) 4 = Some bs /\ length bs = 4%nat).
  { intros p Hp Hp63 A AP. destruct (A i Hi) as (v & _ & R). exists (Z_to_le_bytes 4 v). split; [|apply length_Z_to_le_bytes].
    rewrite <- R. apply (rinv_rdn SEGS [(g, 1024%Z)] M0 M (p + 4 * i) 4 RI); [clear - Hp Hi; lia | cbn; clear - Hp63 Hi Hn; lia|].
    intros r [<- | []]. cbn [fst snd]. clear - AP Hi. lia. }
  destruct (CELL rm Hrm Hrm63 Ar APr) as (bsr & Cr & Lr). destruct (CELL gm Hgm Hgm63 Ag APg) as (bsg & Cg & Lg). destruct (CELL bm Hbm Hbm63 Ab APb) as (bsb & Cb & Lb).
  assert (SOKi : store_ok SEGS M (Z_to_bv 64 (g + 4 * i)) 4 = true)
    by (apply (reg_sok SEGS M0 M g 1024 (g + 4 * i) 4 (proj1 RI) SOK Hg); cbn; clear - Hg63 Hi Hn; lia).
  assert (N : (0 <= rm + 4 * i)%Z /\ (rm + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= gm + 4 * i)%Z /\ (gm + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= bm + 4 * i)%Z /\ (bm + 4 * i + 4 < 2 ^ 63)%Z /\
              (0 <= g + 4 * i)%Z /\ (g + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= g + 4 * n < 2 ^ 63)%Z) by (clear - Hi Hn Hg Hg63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63; lia).
  destruct N as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct (Z.eq_dec (i + 1) n) as [LAST|MORE].
  - destruct (rmc_L1 rom true fx regs M (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (g + 4 * i) (g + 4 * n) bsr bsg bsb Hz N1 N2 N3 N4 N5 N6 N7 N8 N9
                Cr Lr Cg Lg Cb Lb SOKi ltac:(cbn; clear - LAST; lia) H11 H12 H13 H15 H14)
      as (fr1 & cs1 & r1 & bs & RUN & Hz1 & Lbs & _ & _ & _ & _ & AG).
    exists fr1, cs1, r1, (wbytes M (Z_to_bv 64 (g + 4 * i)) bs). split; [exact RUN|]. split; [exact Hz1|]. split; [|exact AG].
    apply (rinv_wbytes [(g, 1024%Z)] M0 M (g + 4 * i) 4 bs RI); [rewrite Lbs; reflexivity | clear - N7 N8; lia | clear - N8; lia|].
    exists (g, 1024%Z). split; [left; reflexivity | cbn [fst snd]; clear - Hi Hn; lia].
  - destruct (rmc_L1 rom false fx regs M (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (g + 4 * i) (g + 4 * n) bsr bsg bsb Hz N1 N2 N3 N4 N5 N6 N7 N8 N9
                Cr Lr Cg Lg Cb Lb SOKi ltac:(cbn; clear - MORE; lia) H11 H12 H13 H15 H14)
      as (fr1 & cs1 & r1 & bs & RUN & Hz1 & Lbs & F11 & F12 & F13 & F15 & AG).
    assert (RI1 : rinv [(g, 1024%Z)] M0 (wbytes M (Z_to_bv 64 (g + 4 * i)) bs)).
    { apply (rinv_wbytes [(g, 1024%Z)] M0 M (g + 4 * i) 4 bs RI); [rewrite Lbs; reflexivity | clear - N7 N8; lia | clear - N8; lia|].
      exists (g, 1024%Z). split; [left; reflexivity | cbn [fst snd]; clear - Hi Hn; lia]. }
    destruct (IH (mkFP fr1 cs1) r1 M0 _ g rm gm bm n (i + 1)%Z Hz1 ltac:(clear - Hk; lia) ltac:(clear - Hi MORE; lia) Hn Hg Hg63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63
                SOK Ar Ag Ab APr APg APb RI1) as (fr2 & cs2 & r2 & M2 & RUN2 & Hz2 & RI2 & AG2).
    + rewrite F11. f_equal. clear; lia.
    + rewrite F12. f_equal. clear; lia.
    + rewrite F13. f_equal. clear; lia.
    + rewrite F15. f_equal. clear; lia.
    + rewrite (AG 14%bv) by notin_list. exact H14.
    + exists fr2, cs2, r2, M2. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact Hz2|]. split; [exact RI2|].
      intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Raster.
Context {fx : FPState}.
Variables (s g w h wqs wqd sbase slen dbase dlen : Z) (M0 : word -> option byte).
Definition RR : list (Z * Z) := [(dbase, dlen); ((s - 112)%Z, 4%Z)].
Hypothesis GEO : (4096 <= s - 256 /\ s <= 2 ^ 47 /\ 4096 <= g /\ g + 1024 <= s - 256 /\ 4096 <= sbase /\ 0 <= slen /\ sbase + slen <= s - 256 /\
                  4096 <= dbase /\ 0 <= dlen /\ dbase + dlen <= s - 256 /\ 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= 4 * wqs /\ w <= 4 * wqd)%Z.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 sbase) (Z.to_nat slen) = true.
Hypothesis SOKg : store_ok SEGS M0 (Z_to_bv 64 g) 1024 = true.
Hypothesis SOKd : store_ok SEGS M0 (Z_to_bv 64 dbase) (Z.to_nat dlen) = true.
Hypothesis SOKc : store_ok SEGS M0 (Z_to_bv 64 (s - 112)) 4 = true.
Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cd : rdn SEGS M0 (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 8).
Variables (wplsv datasv : Z).
Hypothesis Rwd : (0 <= wplsv < 2 ^ 31 /\ 0 <= datasv < 2 ^ 63)%Z.
Hypothesis Cws : rdn SEGS M0 (Z_to_bv 64 (s - 240)) 8 = Some (Z_to_le_bytes 8 wplsv).
Hypothesis Cds : rdn SEGS M0 (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datasv).

Ltac geo := pose proof GEO as (Gs & Gs47 & Gg & Gg2 & Gsb & Gsl & Gsb2 & Gdb & Gdl & Gdb2 & Gw & Gh & Gws & Gwd).

(* [comment removed for export] *)
Lemma fcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RR M0 M -> (s - 256 <= a)%Z -> (a + Z.of_nat n <= s - 112)%Z ->
  rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn R. geo. rewrite <- R. apply (rinv_rdn SEGS RR M0 M a n RI); [lia | lia|].
  intros r Hr. unfold RR in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Definition rowok (srow drow : Z) : Prop :=
  (srow mod 4 = 0 /\ sbase <= srow /\ srow + 4 * wqs <= sbase + slen /\ drow mod 4 = 0 /\ dbase <= drow /\ drow + 4 * wqd <= dbase + dlen)%Z.

(* [comment removed for export] *)
Lemma rmc_x4_loop : forall (k : nat) regs (M : word -> option byte) (srow drow j : Z),
  rowok srow drow -> (w - j <= Z.of_nat k)%Z -> (0 <= j)%Z -> (j + 4 <= w)%Z -> rinv RR M0 M ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 (srow + j) -> getr regs 8 = Z_to_bv 64 (drow + j) ->
  getr regs 9 = Z_to_bv 64 j ->
  exists regs' M' jend,
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19bfc) M rom) (@mkst fx regs' (Z_to_bv 64 0x19fbc) M' rom)
    /\ rinv RR M0 M' /\ (0 <= jend <= w)%Z /\ getr regs' 18 = Z_to_bv 64 jend /\ getr regs' 25 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [8; 9; 12; 18; 25; 26; 27]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M srow drow j RO Hk Hj Hj4 RI H2 H10 H12 H8 H9; [lia|]. geo.
  destruct RO as (As & Bs1 & Bs2 & Ad & Bd1 & Bd2).
  (* [comment removed for export] *)
  destruct (reg_read SEGS M0 M sbase (Z.to_nat slen) (srow + j) 4 wr_readable_s15 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsw & Rw).
  destruct (rdn_word_val SEGS M _ bsw Rw) as (sw & Hsw & Csw).
  destruct (lut_o_range sw Hsw) as (O0 & O1 & O2 & O3).
  assert (LUT : forall o, (0 <= o <= 1020)%Z -> exists bs, rdn SEGS M (Z_to_bv 64 (g + o)) 4 = Some bs).
  { intros o Ho. apply (reg_read SEGS M0 M g 1024 (g + o) 4 wr_readable_s15 (proj1 RI) SOKg); cbn; lia. }
  destruct (LUT _ O3) as (bs3 & C3). destruct (LUT _ O2) as (bs2 & C2). destruct (LUT _ O1) as (bs1 & C1). destruct (LUT _ O0) as (bs0 & C0).
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (drow + j)) 4 = true)
    by (apply (reg_sok SEGS M0 M dbase (Z.to_nat dlen) (drow + j) 4 (proj1 RI) SOKd); rewrite ?Z2Nat.id by lia; cbn; lia).
  pose proof (fcell M (s - 120) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  assert (RI1 : forall v : word, rinv RR M0 (wbytes M (Z_to_bv 64 (drow + j)) (word_to_le_bytes 4 v))).
  { intros v. apply (rinv_wbytes RR M0 M (drow + j) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists (dbase, dlen). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct (Z_lt_ge_dec (j + 7) w) as [MORE|LAST].
  - destruct (rmc_B4 rom true fx regs M s g (srow + j) (drow + j) j w sw bs3 bs2 bs1 bs0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj ltac:(lia) Hsw
                Csw CwM C3 C2 C1 C0 SOKj ltac:(left; lia) ltac:(cbn; lia) H2 H10 H12 H8 H9)
      as (r1 & v & RUN & F9 & F18 & F12 & F8 & F25 & AG).
    destruct (IH r1 _ srow drow (j + 4)%Z ltac:(unfold rowok; repeat split; assumption) ltac:(lia) ltac:(lia) ltac:(lia) (RI1 v))
      as (r2 & M2 & jend & RUN2 & RI2 & Hje & G18 & G25 & AG2).
    + rewrite (AG 2%bv) by notin_list. exact H2.
    + rewrite (AG 10%bv) by notin_list. exact H10.
    + rewrite F12. f_equal. lia.
    + rewrite F8. f_equal. lia.
    + exact F9.
    + exists r2, M2, jend. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact RI2|]. split; [exact Hje|]. split; [exact G18|]. split; [exact G25|].
      intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
  - destruct (rmc_B4 rom false fx regs M s g (srow + j) (drow + j) j w sw bs3 bs2 bs1 bs0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj ltac:(lia) Hsw
                Csw CwM C3 C2 C1 C0 SOKj ltac:(left; lia) ltac:(cbn; lia) H2 H10 H12 H8 H9)
      as (r1 & v & RUN & F9 & F18 & F12 & F8 & F25 & AG).
    exists r1, (wbytes M (Z_to_bv 64 (drow + j)) (word_to_le_bytes 4 v)), (j + 4)%Z. split; [exact RUN|]. split; [exact (RI1 v)|]. split; [lia|]. split; [exact F18|]. split; [exact F25 | exact AG].
Qed.

(* [comment removed for export] *)
Lemma rmc_tail_loop : forall (k : nat) regs (M : word -> option byte) (srow drow j : Z),
  rowok srow drow -> (w - j <= Z.of_nat k)%Z -> (0 <= j < w)%Z -> rinv RR M0 M ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 10 = Z_to_bv 64 g -> getr regs 20 = Z_to_bv 64 srow -> getr regs 24 = Z_to_bv 64 drow ->
  getr regs 18 = Z_to_bv 64 j ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19fc0) M rom) (@mkst fx regs' (Z_to_bv 64 0x199f0) M' rom)
    /\ rinv RR M0 M' /\ regs_agree (fun r => In r [8; 12; 18]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M srow drow j RO Hk Hj RI H2 H10 H20 H24 H18; [lia|]. geo.
  destruct RO as (As & Bs1 & Bs2 & Ad & Bd1 & Bd2).
  pose proof (bytea_bounds srow wqs (srow + j) As ltac:(lia)) as BS. pose proof (bytea_bounds drow wqd (drow + j) Ad ltac:(lia)) as BD.
  destruct (reg_read SEGS M0 M sbase (Z.to_nat slen) (bytea (srow + j)) 1 wr_readable_s15 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsb & Cb).
  pose proof (rdv_byte_range bsb (rdn_length _ _ _ _ _ Cb)) as Rb.
  destruct (reg_read SEGS M0 M g 1024 (g + 4 * rdv false 1 bsb) 4 wr_readable_s15 (proj1 RI) SOKg ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as (bsl & Cl).
  pose proof (fcell M (s - 120) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  assert (SOKcM : store_ok SEGS M (Z_to_bv 64 (s - 112)) 4 = true) by (apply (reg_sok SEGS M0 M (s - 112) 4 (s - 112) 4 (proj1 RI) SOKc); cbn; lia).
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (bytea (drow + j))) 1 = true)
    by (apply (reg_sok SEGS M0 M dbase (Z.to_nat dlen) (bytea (drow + j)) 1 (proj1 RI) SOKd); rewrite ?Z2Nat.id by lia; cbn; lia).
  assert (RI1 : rinv RR M0 (RMCT M s drow j (Z_to_bv 64 (rdv true 4 bsl)))).
  { unfold RMCT. apply (rinv_wbytes RR M0 _ (bytea (drow + j)) 1); [ | rewrite length_N_to_le_bytes; reflexivity | lia | lia | ].
    - apply (rinv_wbytes RR M0 M (s - 112) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
      exists ((s - 112)%Z, 4%Z). split; [right; left; reflexivity | cbn [fst snd]; lia].
    - exists (dbase, dlen). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct (Z_lt_ge_dec (j + 1) w) as [MORE|LAST].
  - destruct (rmc_TB rom true fx regs M s g srow drow j w bsb bsl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj ltac:(lia) Cb Cl CwM SOKcM SOKj
                ltac:(left; lia) ltac:(cbn; lia) H2 H10 H20 H24 H18) as (r1 & RUN & F18 & AG).
    destruct (IH r1 _ srow drow (j + 1)%Z ltac:(unfold rowok; repeat split; assumption) ltac:(lia) ltac:(lia) RI1)
      as (r2 & M2 & RUN2 & RI2 & AG2).
    + rewrite (AG 2%bv) by notin_list. exact H2.
    + rewrite (AG 10%bv) by notin_list. exact H10.
    + rewrite (AG 20%bv) by notin_list. exact H20.
    + rewrite (AG 24%bv) by notin_list. exact H24.
    + exact F18.
    + exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact RI2|].
      intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
  - destruct (rmc_TB rom false fx regs M s g srow drow j w bsb bsl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj ltac:(lia) Cb Cl CwM SOKcM SOKj
                ltac:(left; lia) ltac:(cbn; lia) H2 H10 H20 H24 H18) as (r1 & RUN & F18 & AG).
    exists r1, (RMCT M s drow j (Z_to_bv 64 (rdv true 4 bsl))). split; [exact RUN|]. split; [exact RI1 | exact AG].
Qed.

(* [comment removed for export] *)
Definition rowregs (regs : bvmap 5 word) (srow drow i sstep dstep : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 256) /\ getr regs 10 = Z_to_bv 64 g /\ getr regs 11 = Z_to_bv 64 i /\ getr regs 13 = Z_to_bv 64 sstep /\
  getr regs 15 = Z_to_bv 64 3 /\ getr regs 7 = Z_to_bv 64 4 /\ getr regs 31 = Z_to_bv 64 8 /\ getr regs 21 = Z_to_bv 64 dstep /\
  getr regs 23 = Z_to_bv 64 srow /\ getr regs 20 = Z_to_bv 64 srow /\ getr regs 22 = Z_to_bv 64 drow /\ getr regs 24 = Z_to_bv 64 drow.

(* [comment removed for export] *)
Lemma rmc_row : forall regs (M : word -> option byte) (srow drow i sstep dstep : Z),
  rowok srow drow -> rinv RR M0 M -> rowregs regs srow drow i sstep dstep ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19a14) M rom) (@mkst fx regs' (Z_to_bv 64 0x199f0) M' rom)
    /\ rinv RR M0 M' /\ regs_agree (fun r => In r [8; 9; 12; 16; 18; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs M srow drow i sstep dstep RO RI (H2 & H10 & H11 & H13 & H15 & H7 & H31 & H21 & H23 & H20 & H22 & H24). geo.
  pose proof RO as (As & Bs1 & Bs2 & Ad & Bd1 & Bd2). destruct Rwd as (Rw1 & Rw2).
  pose proof (fcell M (s - 128) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cd) as CdM. pose proof (fcell M (s - 120) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  pose proof (fcell M (s - 240) 8 _ RI ltac:(lia) ltac:(cbn; lia) Cws) as CwsM. pose proof (fcell M (s - 232) 8 _ RI ltac:(lia) ltac:(cbn; lia) Cds) as CdsM.
  (* [comment removed for export] *)
  assert (TAIL : forall r1 M1 j, rinv RR M0 M1 -> (0 <= j <= w)%Z -> getr r1 18 = Z_to_bv 64 j -> getr r1 25 = Z_to_bv 64 w ->
                   getr r1 2 = Z_to_bv 64 (s - 256) -> getr r1 10 = Z_to_bv 64 g -> getr r1 20 = Z_to_bv 64 srow -> getr r1 24 = Z_to_bv 64 drow ->
                   exists r2 M2, msteps SEGS (@mkst fx r1 (Z_to_bv 64 0x19fbc) M1 rom) (@mkst fx r2 (Z_to_bv 64 0x199f0) M2 rom)
                                 /\ rinv RR M0 M2 /\ regs_agree (fun r => In r [8; 12; 18]%list) r1 r2).
  { intros r1 M1 j RI1 Hj G18 G25 G2 G10 G20 G24. destruct (Z_lt_ge_dec j w) as [LT|GE].
    - destruct (rmc_TH rom true fx r1 M1 j w ltac:(lia) ltac:(lia) ltac:(cbn; lia) G18 G25) as (r2 & RUN2 & AG2).
      destruct (rmc_tail_loop (Z.to_nat w) r2 M1 srow drow j RO ltac:(lia) ltac:(lia) RI1) as (r3 & M3 & RUN3 & RI3 & AG3);
        try (rewrite (AG2 _) by notin_list; assumption).
      exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN2 RUN3)|]. split; [exact RI3|]. intros r Hr. rewrite (AG3 r Hr). apply AG2. intros [].
    - destruct (rmc_TH rom false fx r1 M1 j w ltac:(lia) ltac:(lia) ltac:(cbn; lia) G18 G25) as (r2 & RUN2 & AG2).
      exists r2, M1. split; [exact RUN2|]. split; [exact RI1|]. intros r Hr. apply AG2. intros []. }
  destruct (Z_lt_ge_dec w 4) as [SMALL|BIG].
  - destruct (rmc_RH rom false fx regs M s w wplsv datasv srow drow ltac:(lia) ltac:(lia) Rw1 Rw2 ltac:(lia) ltac:(lia) CdM CwM CwsM CdsM ltac:(cbn; lia)
                H2 H15 H7 H31 H23 H22) as (r1 & RUN1 & F25 & F18 & AG1).
    destruct (TAIL r1 M 0%Z RI ltac:(lia) F18 F25) as (r2 & M2 & RUN2 & RI2 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|].
    intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (rmc_RH rom true fx regs M s w wplsv datasv srow drow ltac:(lia) ltac:(lia) Rw1 Rw2 ltac:(lia) ltac:(lia) CdM CwM CwsM CdsM ltac:(cbn; lia)
                H2 H15 H7 H31 H23 H22) as (r1 & RUN1 & F25 & (F9 & F12 & F8) & AG1).
    destruct (rmc_x4_loop (Z.to_nat w) r1 M srow drow 0%Z RO ltac:(lia) ltac:(lia) ltac:(lia) RI) as (r2 & M2 & jend & RUN2 & RI2 & Hje & G18 & G25 & AG2);
      try (rewrite (AG1 _) by notin_list; assumption); try (rewrite Z.add_0_r; assumption); try assumption.
    destruct (TAIL r2 M2 jend RI2 Hje G18 G25) as (r3 & M3 & RUN3 & RI3 & AG3);
      try (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; assumption).
    exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|].
    intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

(* [comment removed for export] *)
Hypothesis LEN : (slen = 4 * (wqs * h) /\ dlen = 4 * (wqd * h) /\ sbase mod 4 = 0 /\ dbase mod 4 = 0 /\ 0 <= wqs /\ 0 <= wqd)%Z.

Lemma rmc_rows : forall (k : nat) regs (M : word -> option byte) (i : Z),
  Z.of_nat k = (h - i)%Z -> (0 <= i < h)%Z -> rinv RR M0 M ->
  rowregs regs (sbase + 4 * (wqs * i)) (dbase + 4 * (wqd * i)) i (4 * wqs) (4 * wqd) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19a14) M rom) (@mkst fx regs' (Z_to_bv 64 0x1a038) M' rom)
    /\ rinv RR M0 M'
    /\ regs_agree (fun r => In r [8; 9; 11; 12; 14; 16; 18; 19; 20; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i Hk Hi RI RR0; [lia|]. geo. destruct LEN as (Ls & Ld & As & Ad & Wqs & Wqd).
  pose proof (row_bounds wqs i h Wqs ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h Wqd ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  assert (RO : rowok (sbase + 4 * (wqs * i)) (dbase + 4 * (wqd * i))).
  { unfold rowok. split; [apply al4_add; exact As|]. split; [lia|]. split; [lia|]. split; [apply al4_add; exact Ad|]. split; lia. }
  destruct (rmc_row regs M _ _ i _ _ RO RI RR0) as (r1 & M1 & RUN1 & RI1 & AG1).
  destruct RR0 as (H2 & H10 & H11 & H13 & H15 & H7 & H31 & H21 & H23 & H20 & H22 & H24).
  pose proof (fcell M1 (s - 124) 4 _ RI1 ltac:(lia) ltac:(cbn; lia) Ch) as ChM.
  destruct (Z_lt_ge_dec (i + 1) h) as [MORE|LAST].
  - destruct (rmc_RL rom false fx r1 M1 s i h (sbase + 4 * (wqs * i)) (dbase + 4 * (wqd * i)) (4 * wqs) (4 * wqd) ltac:(lia) Hi ltac:(lia) ChM ltac:(cbn; lia))
      as (r2 & RUN2 & F11 & F23 & F20 & F22 & F24 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    destruct (IH r2 M1 (i + 1)%Z ltac:(lia) ltac:(lia) RI1) as (r3 & M3 & RUN3 & RI3 & AG3).
    { unfold rowregs. replace (sbase + 4 * (wqs * (i + 1)))%Z with (sbase + 4 * (wqs * i) + 4 * wqs)%Z by ring.
      replace (dbase + 4 * (wqd * (i + 1)))%Z with (dbase + 4 * (wqd * i) + 4 * wqd)%Z by ring.
      repeat split; try assumption; (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; assumption). }
    exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|].
    intros r Hr. rewrite (AG3 r Hr). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (rmc_RL rom true fx r1 M1 s i h (sbase + 4 * (wqs * i)) (dbase + 4 * (wqd * i)) (4 * wqs) (4 * wqd) ltac:(lia) Hi ltac:(lia) ChM ltac:(cbn; lia))
      as (r2 & RUN2 & F11 & F23 & F20 & F22 & F24 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    exists r2, M1. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI1|].
    intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

End Raster.

End Loops.
End O15LeptRmcLoops.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.OL Require MaxIndex.
Module O15MaxIndex.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import O15Kit.
(* [comment removed for export] *)











Import O15Kit.O15Reloc. Import O15Kit.O15RelocCode. Import O15Kit.O15RelocSites. Import O15Kit.O15RelocImg. Import O15Kit.O15RelocOL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Theorem maxindex_contract : SSP.sum_contract SEGS (SSP.spec_maxindex 0x18fb0 144).
Proof. rl_tail (@MaxIndex.maxindex_contract fx o15_reloc o15_code_ol o15_sites_ol). Qed.

End VPORT.
End O15MaxIndex.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.OL Require PadBits.
Module O15PadBits.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.RelocLept.
Import O15Kit.
(* [comment removed for export] *)











Import O15Kit.O15Reloc. Import O15Kit.O15RelocCode. Import O15Kit.O15RelocSites. Import O15Kit.O15RelocImg. Import O15Kit.O15RelocOL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Section PB.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables pix w h d wpl data sp : Z.
Variables ra s0v s1v s2v : word.
Hypothesis Hpix : (1 <= pix /\ pix + 12 <= 2 ^ 64)%Z.
Hypothesis Hpix64 : (pix + 64 <= 2 ^ 64)%Z.
Hypothesis Rw : (0 <= w < 2 ^ 32)%Z.
Hypothesis Rh : (0 <= h < 2 ^ 32)%Z.
Hypothesis Hw : (1 <= w <= 20000)%Z.
Hypothesis Hh : (1 <= h <= 20000)%Z.
Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z.
Hypothesis Hsp : (48 <= sp /\ sp < 2 ^ 64)%Z.
Hypothesis Hra : ret_ok ra.
Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
Hypothesis Hwpl : (0 <= wpl <= 20000)%Z.
Hypothesis Hdata : (1 <= data /\ data < 2 ^ 64)%Z.
Hypothesis HR : (data + 4 * (wpl * h) <= 2 ^ 64)%Z.
Hypothesis SOKr : store_ok SEGS M (Z_to_bv 64 data) (Z.to_nat (4 * (wpl * h))) = true.
Hypothesis FR : disj_apart data (4 * (wpl * h)) (sp - 48) 48.
Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 48)) 48 = true.
Hypothesis FP12 : disj_apart pix 12 (sp - 48) 48.
Hypothesis FP : disj_apart pix 64 (sp - 48) 48.
Definition M1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
                           (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
                   (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
           (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v).
Definition M2g (vw vh : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 vw))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 vh))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
Definition M2 : word -> option byte := M2g (Z_to_bv 64 w) (Z_to_bv 64 h).
Lemma lez4 : forall z, (0 <= z < 2 ^ 32)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
Proof. rl_tail (@PadBits.lez4). Qed.

#[local] Notation RS := (4 * (wpl * h))%Z (only parsing).
Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < data \/ data + RS <= bv_unsigned x)%Z -> Mi x = M2 x)
    /\ mem_grows M2 Mi.
Lemma M2_grows : mem_grows M M2.
Proof. rl_tail (@PadBits.M2_grows M w h d sp ra s0v s1v s2v). Qed.

Lemma M2g_outside : forall vw vh (x : word),
    (bv_unsigned x < sp - 48 \/ sp <= bv_unsigned x)%Z -> M2g vw vh x = M x.
Proof. rl_tail (@PadBits.M2g_outside M d sp ra s0v s1v s2v Hsp). Qed.

Theorem padbits_run : forall regs,
    (d <> 24)%Z -> (wpl = (w * d + 31) / 32)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17960 : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 11; 12; 13; 14; 18]%list) regs regs'.
Proof. rl_tail (@PadBits.padbits_run fx o15_reloc o15_code_ol o15_sites_ol o15_lept o15_img_ol M rom pix w h d wpl data sp ra s0v s1v s2v Hpix Hpix64 Rw Rh Hw Hh Hd Hsp Hra Cw Ch Cd Cwpl Cdata Hwpl Hdata HR SOKr FR SOKf FP12 FP). Qed.

End PB.

Definition padbits24_L_ok (L : SSP.ls_addrs) : Prop :=
  (SSP.ls_entry L = 0x153dc /\ SSP.ls_sev_got L = 0x2c780 /\ In 0x109e6 (SSP.ls_fmts1 L)
   /\ (0 <= SSP.ls_img_lo L <= 0x109e6 /\ 0x10d82 <= SSP.ls_img_hi L <= SSP.ls_sp_lo L)
   /\ 0 <= SSP.ls_frame L)%Z.
Theorem padbits24_contract : forall L : SSP.ls_addrs,
  padbits24_L_ok L ->
  SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
  SSP.sum_contract SEGS (SSP.spec_padbits24 0x17960 (48 + SSP.ls_frame L) L).
Proof.
  intros L HL HC.
  pose proof (@PadBits.padbits24_contract fx o15_reloc o15_code_ol o15_sites_ol o15_lept o15_img_ol L) as RLT.
  unfold PadBits.padbits24_L_ok in RLT. unfold padbits24_L_ok in HL.
  rl_bare_in RLT.
  apply RLT; [ | exact HC].
  destruct HL as (HLe & HLsg & HLfmt & HLimg & HLfr). repeat split; try assumption; lia.
Qed.

End VPORT.
End O15PadBits.
