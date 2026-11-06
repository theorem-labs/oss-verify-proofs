(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3bR.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3b.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.
Section K3R.
  Variables (mem rom : word -> option byte) (S : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2448).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2464)) 16 = true.

  Lemma k3_run_r :
    exists r, msteps BSEGS (mkst regs (0x4ea10 : word) mem rom) (mkst r (0x78e2c : word) (fr_k3 mem S) rom)
      /\ getr r 1 = Z_to_bv 64 0x78004 /\ getr r 2 = at_ S (-2464)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4ea10 D_4ea10.                              (* [comment removed for export] *)
      an F_77ff8 D_77ff8.                              (* [comment removed for export] *)
      fsd F_77ffc D_77ffc (at_ S (-2456)).             (* [comment removed for export] *)
      an F_78000 D_78000.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_k3 mem S). wd_refl.
    - post.
  Qed.
End K3R.
End FPGen.
End BoAllocFRc3bR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3b BoAllocFRc3bR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRcS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRcS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Lemma at0_litS5 : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof. intros c Hc. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. reflexivity. Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma rd_lock_back : forall (m : word -> option byte) (b1 b2 b3 : byte),
  rdn BSEGS (wbytes (wbytes m (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3]) (Z_to_bv 64 0x10ae00) [Z_to_bv 8 0]) (Z_to_bv 64 0x10ae00) 4
  = Some [Z_to_bv 8 0; b1; b2; b3].
Proof using.
  intros m b1 b2 b3.
  assert (E : wbytes (wbytes m (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3]) (Z_to_bv 64 0x10ae00) [Z_to_bv 8 0]
              = wbytes m (Z_to_bv 64 0x10ae00) [Z_to_bv 8 0; b1; b2; b3]).
  { apply functional_extensionality. intros a. (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end).
    destruct (decide (a = Z_to_bv 64 0x10ae00)) as [-> | NE]; [reflexivity|].
    rewrite (bv_eqb_neq a (Z_to_bv 64 0x10ae00) NE). reflexivity. }
  rewrite E. apply (rdn_wbytes_hit BSEGS [Z_to_bv 8 0; b1; b2; b3] m (Z_to_bv 64 0x10ae00)). unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
Qed.

(* [comment removed for export] *)
Definition fr_sA (M : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 cbp : word) (b1 b2 b3 : byte) (m T h msz len ptr i last : Z)
                 (j0 j1 wnf wca w16 w24 : word) : word -> option byte :=
  let M1 := fr_ks1 M S ra0 s0v s1v s2v s3v s4v in
  let M2 := fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3 in
  let M3 := fr_gbb1 M2 in
  let M4 := fr_k3 M3 S in
  let M5 := wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) in
  let M6 := fr_k4 M5 T j0 j1 in
  let M7 := fr_sd1 M6 S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24 in
  wbytes (ps_frame M7 (at_ S (-2432)) (Z_to_bv 64 0x4ef64) (Z_to_bv 64 h) (Z_to_bv 64 h) (Z_to_bv 64 msz) s3v s4v x21)
         (Z_to_bv 64 (shad (Z_to_bv 64 h))) (repeat (MemsetLibF.cbyte (Z_to_bv 64 0)) (Z.to_nat (shlen (Z_to_bv 64 msz)))).

Section RUNSA.
  Variables (M rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 cbp tp tsdp v midend : word) (b1 b2 b3 : byte).   (* [comment removed for export] *)
  Variables (m n spb T tctx h msz i len ptr last : Z) (hs : list Z).
  Variables (bf0 bf1 bnf bca b16 b24 : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation negm := (v_sub (Z_to_bv 64 0) (Z_to_bv 64 msz)).
  #[local] Abbreviation wnf := (at_ (Z_to_bv 64 (bytes_le_to_Z bnf)) 1).
  #[local] Abbreviation wca := (v_sub (Z_to_bv 64 (bytes_le_to_Z bca)) (Z_to_bv 64 msz)).
  #[local] Abbreviation w16 := (v_add (Z_to_bv 64 (bytes_le_to_Z b16)) negm).
  #[local] Abbreviation w24 := (v_add (Z_to_bv 64 (bytes_le_to_Z b24)) negm).
  #[local] Abbreviation shlo := (0x7fff8000 + h / 8)%Z.
  (* [comment removed for export] *)
  Hypothesis H1 : getr r0 1 = ra0.
  Hypothesis H2 : getr r0 2 = at_ S (-2400).
  Hypothesis H10 : getr r0 10 = cbp.
  Hypothesis H11 : getr r0 11 = Z_to_bv 64 m.
  Hypothesis H8 : getr r0 8 = s0v.   Hypothesis H9 : getr r0 9 = s1v.   Hypothesis H18 : getr r0 18 = s2v.
  Hypothesis H19 : getr r0 19 = s3v. Hypothesis H20 : getr r0 20 = s4v. Hypothesis H21 : getr r0 21 = x21.
  Hypothesis H4 : getr r0 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gh : (AIMGHI <= h /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584)%Z.
  Hypothesis Ghs : hideW (h + msz <= 0x7fff7000 \/ 0x10007fff8000 <= h)%Z.
  Hypothesis Ghp : hideW (h + msz <= spb \/ spb + 2 ^ 37 <= h)%Z.
  Hypothesis Gm : (h + 4096 <= m /\ m + 16 <= h + msz)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GhT : hideW (h + msz <= T \/ T + 4096 <= h)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis Gctxi : hideW (tctx + 4096 <= AIMGLO \/ AIMGHI <= tctx)%Z.
  Hypothesis Gtp : (0x10ae04 + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= 0x10ae00 \/ 0x10ae04 <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis Glen : (0 <= i < len /\ len <= 2 ^ 20 /\ Z.of_nat (length hs) = len)%Z.
  Hypothesis Gptr : (AIMGHI <= ptr /\ ptr + 8 * len <= U S - 3584)%Z.
  Hypothesis GptrT : hideW (ptr + 8 * len <= T \/ T + 4096 <= ptr)%Z.
  Hypothesis GptrH : hideW (ptr + 8 * len <= h \/ h + msz <= ptr)%Z.
  Hypothesis Glast : (AIMGHI <= last /\ last + 32 <= U S - 3584)%Z.
  Hypothesis GlastH : hideW (last = h \/ last + 32 <= h \/ h + msz <= last)%Z.
  Hypothesis GptrL : hideW (ptr + 8 * len <= last \/ last + 32 <= ptr)%Z.
  Hypothesis Ghs63 : Forall (fun x => (0 <= x < 2 ^ 63)%Z) hs.
  Hypothesis Hscan : gbb_scan m hs 0 = h.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M (at_ S (-2512)) 112 = true.
  Hypothesis OkT : store_ok BSEGS M (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Okslot : store_ok BSEGS M (Z_to_bv 64 (ptr + 8 * i)) 8 = true.
  Hypothesis Oklast : store_ok BSEGS M (Z_to_bv 64 (last + 24)) 8 = true.
  Hypothesis Oksh : store_ok BSEGS M (Z_to_bv 64 (shad (Z_to_bv 64 h))) (Z.to_nat (msz / 8)) = true.
  (* [comment removed for export] *)
  Hypothesis C_spb : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_pg : rdn BSEGS M (Z_to_bv 64 0x10ab98) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_lock : rdn BSEGS M (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U v.
  Hypothesis C_n : rdn BSEGS M (Z_to_bv 64 (0x10ab98 + 56)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis C_ptr : rdn BSEGS M (Z_to_bv 64 (0x10ab98 + 8)) 8 = Some (LE8 (Z_to_bv 64 ptr)).
  Hypothesis C_hs : forall j x, nth_error hs j = Some x -> rdn BSEGS M (Z_to_bv 64 (ptr + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 x)).
  Hypothesis C_slot : rdn BSEGS M (Z_to_bv 64 (ptr + 8 * i)) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis C_last : rdn BSEGS M (Z_to_bv 64 (ptr + 8 * (len - 1))) 8 = Some (LE8 (Z_to_bv 64 last)).
  Hypothesis C_mbh : rdn BSEGS M (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis C_msz : rdn BSEGS M (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis C_idx : rdn BSEGS M (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 i)).
  Hypothesis C_kif : rdn BSEGS M (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS M (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS M (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS M tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS M (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_nhi : rdn BSEGS M (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS M (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn BSEGS M (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS M (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_nf : rdn BSEGS M (Z_to_bv 64 (0x10ab98 + 80)) 8 = Some bnf.
  Hypothesis L_nf : length bnf = 8%nat.
  Hypothesis C_ca : rdn BSEGS M (Z_to_bv 64 (0x10ab98 + 88)) 8 = Some bca.
  Hypothesis L_ca : length bca = 8%nat.
  Hypothesis C_16 : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 688 + 16)) 8 = Some b16.
  Hypothesis L_16 : length b16 = 8%nat.
  Hypothesis C_24 : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 688 + 24)) 8 = Some b24.
  Hypothesis L_24 : length b24 = 8%nat.
  Hypothesis C_gsh : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_gcf : rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_thr64 : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)).

  Definition sA_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x4ef70 /\ getr r 2 = at_ S (-2432) /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz
      /\ getr r 8 = Z_to_bv 64 h /\ getr r 9 = Z_to_bv 64 h /\ getr r 18 = Z_to_bv 64 msz /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = x21 /\ getr r 3 = getr r0 3 /\ getr r 4 = tp
      /\ getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23 /\ getr r 24 = getr r0 24
      /\ getr r 25 = getr r0 25 /\ getr r 26 = getr r0 26 /\ getr r 27 = getr r0 27.

  Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  (* [comment removed for export] *)
  Ltac gl G := clear - G; unfold hideW in G; lia.
  Ltac gl0 G := clear - G; unfold hideW in G; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  (* [comment removed for export] *)
  Ltac xq G Q H :=
    eapply rd_same; [ intros x Hx; apply Q; clear - G Hx; unfold hideW in G; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | clear - G; unfold hideW in G; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
  Ltac rch := repeat (first [ reflexivity | assumption
                            | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
  Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob, gct_clob in G in change_no_check G' end); notin)); rch.
  (* [comment removed for export] *)
  Ltac outwg GX :=
    rewrite !wbytes_outside;
    [ | (wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - GX; unfold hideW in GX;
         first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ]) .. ].
  Ltac sokstk Mx GR G := eapply (store_ok_sub BSEGS Mx (at_ S (-2512)) _ 112);
    [ clear - G; unfold hideW in G; rewrite at_u; lia | first [exact Hstk | eapply store_ok_mono; [exact GR | exact Hstk]]
    | clear - G; unfold hideW in G; rewrite ?at_at, !at_u; lia | clear - G; unfold hideW in G; rewrite ?at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].

  Theorem run_sA :
    exists r, msteps BSEGS (mkst r0 (0x4e8a4 : word) M rom)
                           (mkst r (0x6ea68 : word)
                              (fr_sA M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last (at_ f0 1) (v_add (Z_to_bv 64 n) f1) wnf wca w16 w24) rom)
      /\ sA_regs r.
  Proof using C_thr64 C_gcf C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh L_24 C_24 L_16 C_16 L_ca C_ca L_nf C_nf L_f1 C_f1 L_f0 C_f0 C_nlo C_nhi C_thr C_tctx C_tsdp C_key C_kif C_idx C_msz C_mbh C_last C_slot C_hs C_ptr C_n HV C_lock C_pg C_spb Oksh Oklast Okslot OkT Hstk Hscan Ghs63 GptrL GlastH Glast GptrH GptrT Gptr Glen Gtsdp Gtp Gctxi Gctx GhT GT Gn Gm Ghp Ghs Gh Gspb GS H4 H21 H20 H19 H18 H9 H8 H11 H10 H2 H1 hs tctx spb midend v tsdp.
    (lazymatch goal with |- ?G => let G' := eval unfold sA_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr.
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5). destruct Gm as (Gm1 & Gm2).
    destruct GT as (GT1 & (GTS & GT2)). destruct Gctx as (Gc1 & Gc2). destruct Glen as (Gi & Gl & Glh). destruct Gptr as (Gp1 & Gp2).
    destruct Glast as (Gla1 & Gla2).
    (* [comment removed for export] *)
    pose proof (conj HSr (conj Htpr (conj Htsr (conj GS1 (conj GS2 (conj Gs1 (conj Gs2 (conj Gh1 (conj Gh4 (conj Gh5 (conj Gm1 (conj Gm2
                (conj GT1 (conj GT2 (conj Gc1 (conj Gc2 (conj Gi (conj Gl (conj Gp1 (conj Gp2 (conj Gla1 (conj Gla2 Gtp)))))))))))))))))))))) as G0.
    hidehypW G0.
    pose proof (conj G0 GTS) as G0T. hidehypW G0T.
    pose proof (conj G0T GhT) as G0h. hidehypW G0h.
    pose proof (conj G0T GptrT) as G0q. hidehypW G0q.
    assert (Hsecm : (m < spb \/ spb + 2 ^ 37 <= m)%Z) by (pose proof (conj G0 Ghp) as G; gl G).
    assert (Hsecp : (h + 4096 < spb \/ spb + 2 ^ 37 <= h + 4096)%Z) by (pose proof (conj G0 Ghp) as G; gl G).
    hidehypW Hsecm. hidehypW Hsecp.
    (* [comment removed for export] *)
    destruct (ks1_run M rom S ra0 s0v s1v s2v s3v s4v cbp m spb r0 H1 H2 H10 H11 H8 H9 H18 H19 H20
                ltac:(gl G0) ltac:(gl G0) ltac:(gl G0) Hsecm ltac:(sokstk M GR1 G0) C_spb)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A8 & A9 & A18 & A19 & A20 & A3 & A4 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    assert (GR1 : mem_grows M (fr_ks1 M S ra0 s0v s1v s2v s3v s4v)) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_ks1 in G in change_no_check G' end); grows_tac).
    assert (Q1 : forall x : word, ((U x < U S - 2448)%Z \/ (U S - 2400 <= U x)%Z) -> fr_ks1 M S ra0 s0v s1v s2v s3v s4v x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_ks1 in G in change_no_check G' end). intros x Hx. pose proof (conj G0 Hx) as GX. outwg GX. reflexivity. }
    assert (FRM1 : rdn BSEGS (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) (at_ S (-2408)) 8 = Some (LE8 ra0) /\ rdn BSEGS (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) (at_ S (-2416)) 8 = Some (LE8 s0v)
                   /\ rdn BSEGS (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) (at_ S (-2424)) 8 = Some (LE8 s1v) /\ rdn BSEGS (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) (at_ S (-2432)) 8 = Some (LE8 s2v)
                   /\ rdn BSEGS (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) (at_ S (-2440)) 8 = Some (LE8 s3v) /\ rdn BSEGS (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) (at_ S (-2448)) 8 = Some (LE8 s4v)).
    { clear - GS1 GS2 HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_ks1 in G in change_no_check G' end). repeat split; rd_own. }
    remember (fr_ks1 M S ra0 s0v s1v s2v s3v s4v) as M1 eqn:EM1 in RUN1, GR1, Q1, FRM1.
    (* [comment removed for export] *)
    destruct (gbb_head M1 rom S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v v b1 b2 b3 len ptr r1 A1 A2 A8 A9 A18 A10
                ltac:(gl G0) ltac:(gl G0) ltac:(gl G0) ltac:(sokstk M1 GR1 G0)
                ltac:(xq G0 Q1 C_lock) HV ltac:(xq G0 Q1 C_n) ltac:(xq G0 Q1 C_ptr))
      as (r2 & RUN2 & B2 & B8 & B10 & B11 & B12 & B13 & B14 & B3 & B4 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    assert (GR2 : mem_grows M (fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3))
      by (eapply mem_grows_trans; [exact GR1|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb0 in G in change_no_check G' end); grows_tac).
    assert (Q2 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z ->
                 fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3 x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb0 in G in change_no_check G' end). intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply Q1. gl GX. }
    assert (J2 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z ->
                 fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3 x = M1 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb0 in G in change_no_check G' end). intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. reflexivity. }
    assert (FRB2 : rdn BSEGS (fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4e91c))
                   /\ rdn BSEGS (fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3) (at_ S (-2464)) 8 = Some (LE8 cbp)
                   /\ rdn BSEGS (fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3) (at_ S (-2472)) 8 = Some (LE8 (Z_to_bv 64 m))
                   /\ rdn BSEGS (fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3) (at_ S (-2480)) 8 = Some (LE8 s2v)).
    { clear - GS1 GS2 HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb0 in G in change_no_check G' end). repeat split; rd_own. }
    remember (fr_gbb0 M1 S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v b1 b2 b3) as M2 eqn:EM2 in RUN2, GR2, Q2, J2, FRB2.
    (* [comment removed for export] *)
    assert (NEhs : hs <> []) by (intros E; rewrite E in Glh; cbn in Glh; clear - Glh Gi; lia).
    destruct (gbb_loop hs r2 M2 rom m ptr 0%Z NEhs B12 B13 ltac:(rewrite B11; exact A11) ltac:(rewrite B14, Glh; reflexivity)
                ltac:(gl G0) ltac:(gl G0) Ghs63 ltac:(rewrite Glh; gl G0))
      as (r3 & RUN3 & KP3 & D13).
    { intros j xh Hj.
      assert (Lj : (Z.of_nat j < len)%Z).
      { pose proof (nth_error_Some hs j) as NS. rewrite Hj in NS. assert (L0 : (j < length hs)%nat) by (apply NS; discriminate). clear - L0 Glh. lia. }
      pose proof (C_hs j xh Hj) as CJ. pose proof (conj G0 Lj) as G0j. xq G0j Q2 CJ. }
    rewrite Hscan in D13.
    destruct KP3 as (K1 & K2 & K3 & K4 & K8 & K9 & K10 & K11 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    (* [comment removed for export] *)
    assert (RET_B : ret_ok (Z_to_bv 64 0x4e91c)) by (apply ret_ok_lit; [lia | reflexivity]).
    destruct FRB2 as (FB_ra & FB_s0 & FB_s1 & FB_s2).
    destruct (gbb_tail M2 rom S (Z_to_bv 64 0x4e91c) cbp (Z_to_bv 64 m) s2v m h msz r3
                ltac:(rewrite K2; exact B2) ltac:(rewrite K8; exact B8) ltac:(rewrite K10; exact B10) ltac:(rewrite K11, B11; exact A11) D13
                ltac:(gl G0) ltac:(pose proof (conj G0 Gh2) as G; gl G) RET_B
                ltac:(xq G0 Q2 C_mbh) ltac:(xq G0 Q2 C_msz) ltac:(xq G0 Q2 C_pg) FB_ra FB_s0 FB_s1 FB_s2)
      as (r4 & RUN4 & E2 & E10 & E8 & E9 & E18 & E3 & E4 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    assert (GR3 : mem_grows M (fr_gbb1 M2)) by (eapply mem_grows_trans; [exact GR2|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb1 in G in change_no_check G' end); grows_tac).
    assert (Q3 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z -> fr_gbb1 M2 x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb1 in G in change_no_check G' end). intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply Q2; gl GX. }
    assert (J3 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z -> fr_gbb1 M2 x = M1 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb1 in G in change_no_check G' end). intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply J2; gl GX. }
    assert (LK3 : rdn BSEGS (fr_gbb1 M2) (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { rewrite EM2. (lazymatch goal with |- ?G => let G' := eval unfold fr_gbb1, fr_gbb0 in G in change_no_check G' end). apply rd_lock_back. }
    remember (fr_gbb1 M2) as M3 eqn:EM3 in RUN4, GR3, Q3, J3, LK3.
    (* [comment removed for export] *)
    destruct (ks2_run M3 rom (h + 4096)%Z spb r4 E10 ltac:(rewrite E19, K19, B19; exact A19) ltac:(rewrite E20, K20, B20; exact A20)
                ltac:(gl G0) ltac:(gl G0) Hsecp ltac:(xq G0 Q3 C_spb))
      as (r5 & RUN5 & F18 & F1 & F2 & F3 & F4 & F8 & F9 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    (* [comment removed for export] *)
    destruct (k3_run_r M3 rom S r5 ltac:(rewrite F2; exact E2) ltac:(gl G0) ltac:(sokstk M3 GR3 G0))
      as (r6 & RUN6 & W1 & W2 & W3 & W4 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
    assert (GR4 : mem_grows M (fr_k3 M3 S)) by (eapply mem_grows_trans; [exact GR3|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end); grows_tac).
    assert (Q4 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z -> fr_k3 M3 S x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end). intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply Q3; gl GX. }
    assert (J4 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z -> fr_k3 M3 S x = M1 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end). intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply J3; gl GX. }
    assert (K4o : forall x : word, ((U x < U S - 2456)%Z \/ (U S - 2448 <= U x)%Z) -> fr_k3 M3 S x = M3 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end). intros x Hx. pose proof (conj G0 Hx) as GX. outwg GX. reflexivity. }
    assert (RA4 : rdn BSEGS (fr_k3 M3 S) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14))) by (clear - GS1 GS2 HSr; (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end); rd_hit8).
    remember (fr_k3 M3 S) as M4 eqn:EM4 in RUN6, GR4, Q4, J4, RA4, K4o.
    (* [comment removed for export] *)
    assert (RET_G : ret_ok (Z_to_bv 64 0x78004)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (V4 : getr r6 4 = tp) by (rewrite W4, F4, E4, K4, B4, A4; exact H4).
    assert (GH : gctH BSEGS both_gct_tab M4 (at_ S (-2464)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq G0 Q4 C_kif. - xq G0 Q4 C_key. - xq G0 Q4 C_tsdp.
      - pose proof (conj G0 Gtsdp) as G0t. xq G0t Q4 C_tctx.
      - pose proof (conj G0 Gctxi) as G0c. xq G0c Q4 C_thr.
      - clear - Gc1 Gc2 HSr. unorm. lia.
      - rewrite at_at. sokstk M4 GR4 G0.
      - gl0 G0. - gl0 G0. - gl0 G0. - pose proof (conj G0 Gtsdp) as G0t. gl0 G0t. - gl0 G0. }
    destruct (gct_run BSEGS both_gct_tab both_gct_tab_ok M4 rom r6 (Z_to_bv 64 0x78004) (at_ S (-2464)) tp tsdp ctxw thr GH RET_G W1 W2 V4)
      as (r7 & RUN7 & X10 & X11 & AGX).
    cbn [gt_rb both_gct_tab] in RUN7. rewrite at0_litS5 in RUN7 by lia. rewrite at_at in RUN7. change (-2464 + -8)%Z with (-2472)%Z in RUN7.
    assert (GR5 : mem_grows M (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)))) by (eapply mem_grows_trans; [exact GR4|]; grows_tac).
    assert (Q5 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z ->
                 wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) x = M x).
    { intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply Q4; gl GX. }
    assert (J5 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z ->
                 wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) x = M1 x).
    { intros x Hx Hx2. pose proof (conj G0 (conj Hx Hx2)) as GX. outwg GX. apply J4; gl GX. }
    assert (K5o : forall x : word, ((U x < U S - 2472)%Z \/ (U S - 2448 <= U x)%Z) -> wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) x = M3 x).
    { intros x Hx. pose proof (conj G0 Hx) as GX. outwg GX. apply K4o. gl GX. }
    assert (RA5 : rdn BSEGS (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004))) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14))).
    { rewrite rdn_wbytes_out; [ exact RA4 | clear - GS1 GS2 HSr; rd8_side | clear - GS1 GS2 HSr; rd8_side | clear - GS1 GS2 HSr; rd8_side ]. }
    remember (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004))) as M5 eqn:EM5 in RUN7, GR5, Q5, J5, K5o, RA5.
    assert (Y2 : getr r7 2 = at_ S (-2464)) by viac AGX (2:reg).
    assert (Y9 : getr r7 9 = Z_to_bv 64 m) by (viac AGX (9:reg); rewrite F9, E9; reflexivity).
    assert (Y18 : getr r7 18 = Z_to_bv 64 (h + 4096)) by viac AGX (18:reg).
    assert (Y19 : getr r7 19 = Z_to_bv 64 0x10ab58) by (viac AGX (19:reg); rewrite F19, E19, K19, B19; exact A19).
    assert (Y20 : getr r7 20 = Z_to_bv 64 (2 ^ 37)) by (viac AGX (20:reg); rewrite F20, E20, K20, B20; exact A20).
    (* [comment removed for export] *)
    destruct FRM1 as (FR_ra & FR_s0 & FR_s1 & FR_s2 & FR_s3 & FR_s4).
    destruct (ks4_run M5 rom S ra0 s0v s1v s2v s3v s4v T m n spb (h + 4096)%Z bf0 bf1 r7 Y2 X10 Y9 Y18 Y19 Y20
                ltac:(gl G0) ltac:(split; [exact GT1 | split; [exact GTS | exact GT2]]) ltac:(gl G0) Gn ltac:(gl G0) ltac:(gl G0) Hsecp RA5
                ltac:(xq G0 Q5 C_nhi) ltac:(xq G0 Q5 C_nlo) ltac:(xq G0T Q5 C_f0) L_f0 ltac:(xq G0T Q5 C_f1) L_f1
                ltac:(eapply (store_ok_sub BSEGS M5 (Z_to_bv 64 T) _ (Z.to_nat 4096)); [clear - GT1 GT2 HSr; wd_ulia | eapply store_ok_mono; [exact GR5 | exact OkT] | clear - GT1 GT2 HSr; wd_ulia | clear - GT1 GT2 HSr; wd_ulia_c])
                ltac:(xq G0 Q5 C_spb) ltac:(xq G0 J5 FR_ra) ltac:(xq G0 J5 FR_s0) ltac:(xq G0 J5 FR_s1) ltac:(xq G0 J5 FR_s2) ltac:(xq G0 J5 FR_s3) ltac:(xq G0 J5 FR_s4))
      as (r8 & RUN8 & Z1 & Z2 & Z10 & Z11 & Z12 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    assert (GR6 : mem_grows M (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1))) by (eapply mem_grows_trans; [exact GR5|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end); grows_tac).
    assert (Q6 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < 0x10ae00 \/ 0x10ae04 <= U x)%Z -> (U x < T + 2840 \/ T + 2856 <= U x)%Z ->
                 fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1) x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end). intros x Hx Hx2 Hx3. pose proof (conj G0 (conj Hx (conj Hx2 Hx3))) as GX. outwg GX. apply Q5; gl GX. }
    assert (LK6 : rdn BSEGS (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { eapply rd_same; [| clear; wd_ulia_c | exact LK3]. intros x Hx. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros Hx.
      (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end). pose proof (conj G0T Hx) as GX. outwg GX. apply K5o. gl GX. }
    remember (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as M6 eqn:EM6 in RUN8, GR6, Q6, LK6.
    (* [comment removed for export] *)
    destruct (sd1_run M6 rom S ra0 s0v s1v s2v v b1 b2 b3 h msz i len ptr last bnf bca b16 b24 r8 Z1 Z2 Z8 Z9 Z18 Z10 Z11 Z12
                ltac:(gl G0) ltac:(pose proof (conj G0 Gh2) as G; gl G) ltac:(gl G0) ltac:(gl G0) ltac:(gl G0) GlastH GptrH GptrL
                ltac:(sokstk M6 GR6 G0)
                ltac:(eapply store_ok_mono; [exact GR6 | exact Okslot]) ltac:(eapply store_ok_mono; [exact GR6 | exact Oklast])
                ltac:(xq G0T Q6 C_pg) LK6 HV ltac:(xq G0h Q6 C_idx) ltac:(xq G0T Q6 C_ptr) ltac:(xq G0q Q6 C_slot) ltac:(xq G0T Q6 C_n)
                ltac:(xq G0h Q6 C_mbh) ltac:(xq G0h Q6 C_msz) ltac:(xq G0q Q6 C_last)
                ltac:(xq G0T Q6 C_nf) L_nf ltac:(xq G0T Q6 C_ca) L_ca ltac:(xq G0T Q6 C_16) L_16 ltac:(xq G0T Q6 C_24) L_24)
      as (r9 & RUN9 & P1 & P2 & P10 & P11 & P12 & P8 & P9 & P18 & P3 & P4 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    assert (GR7 : mem_grows M (fr_sd1 M6 S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24)) by (eapply mem_grows_trans; [exact GR6|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end); grows_tac).
    assert (Q7 : forall x : word, ((U x < U S - 2480)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < 0x10ab98 + 56 \/ 0x10ab58 + 688 + 32 <= U x)%Z -> (U x < T + 2840 \/ T + 2856 <= U x)%Z ->
                 (U x < ptr + 8 * i \/ ptr + 8 * i + 8 <= U x)%Z -> (U x < last + 24 \/ last + 32 <= U x)%Z ->
                 fr_sd1 M6 S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24 x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end). intros x Hx Hx2 Hx3 Hx4 Hx5. pose proof (conj G0 (conj Hx (conj Hx2 (conj Hx3 (conj Hx4 Hx5))))) as GX. outwg GX. apply Q6; gl GX. }
    remember (fr_sd1 M6 S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24) as M7 eqn:EM7 in RUN9, GR7, Q7.
    (* [comment removed for export] *)
    assert (H8m : (h mod 8 = 0 /\ msz mod 8 = 0)%Z) by (clear - Gh2 Gh3; Z.div_mod_to_equations; lia).
    destruct H8m as (Hh8 & Hm8).
    (* [comment removed for export] *)
    pose proof (conj G0T (conj GptrH GlastH)) as G0i. hidehypW G0i.
    assert (PH : poisonH BSEGS both_poison_tab M7 (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 0) (Z_to_bv 64 0x4ef64) (at_ S (-2432)) (Z_to_bv 8 1) midend 18446744073709551615).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset both_poison_tab] in G in change_no_check G' end).
      - xq G0T Q7 C_gsh. - xq G0T Q7 C_sh. - xq G0T Q7 C_gmb. - xq G0T Q7 C_mb. - xq G0T Q7 C_gme. - xq G0T Q7 C_me. - xq G0T Q7 C_ghe. - xq G0T Q7 C_he.
      - xq G0T Q7 C_grm. - xq G0T Q7 C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros NZ. exfalso. apply NZ. reflexivity.
      - intros _. split; [xq G0T Q7 C_gcf|]. split; [xq G0T Q7 C_thr64|].
        (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). clear - Gh1 Gh4 Gh5 HSr GS2. unorm. split; [Z.div_mod_to_equations; lia | lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
        clear - GS1 GS2 HSr. repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
      - clear - Gh1 Gh4 Gh5 HSr GS2 Hh8. unorm. exact Hh8.
      - clear - Gh1 Gh4 Gh5 HSr GS2 Hm8. unorm. exact Hm8.
      - pose proof (conj G0 Ghs) as G. clear - G. unfold hideW in G. unorm. lia.
      - clear - GS1 GS2 HSr. rewrite at_u by lia. lia.
      - rewrite !at_at. sokstk M7 GR7 G0.
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). replace (U (Z_to_bv 64 msz)) with msz by (clear - Gh1 Gh4 Gh5 HSr GS2; unorm; reflexivity). eapply store_ok_mono; [exact GR7 | exact Oksh].
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (both_poison_shadow M7 rom (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 0) (Z_to_bv 64 0x4ef64) (at_ S (-2432)) (Z_to_bv 8 1) midend 18446744073709551615 r9 PH P1 P2 P10 P11 P12)
      as (r10 & RUN10 & AGP).
    rewrite P8, P9, P18 in RUN10.
    assert (R21c : getr r9 21 = x21) by (rewrite P21, Z21; viac AGX (21:reg); rewrite F21, E21, K21, B21, A21; exact H21).
    replace (getr r9 19) with s3v in RUN10 by (rewrite P19; symmetry; exact Z19).
    replace (getr r9 20) with s4v in RUN10 by (rewrite P20; symmetry; exact Z20).
    rewrite R21c in RUN10.
    (* [comment removed for export] *)
    assert (V9 : getr r10 9 = Z_to_bv 64 h) by viac AGP (9:reg).
    assert (V18 : getr r10 18 = Z_to_bv 64 msz) by viac AGP (18:reg).
    destruct (sd2_run (wbytes (ps_frame M7 (at_ S (-2432)) (Z_to_bv 64 0x4ef64) (Z_to_bv 64 h) (Z_to_bv 64 h) (Z_to_bv 64 msz) s3v s4v x21)
                              (Z_to_bv 64 (shad (Z_to_bv 64 h))) (repeat (MemsetLibF.cbyte (Z_to_bv 64 0)) (Z.to_nat (shlen (Z_to_bv 64 msz)))))
                      rom h msz r10 V9 V18)
      as (r11 & RUN11 & T1 & T10 & T11 & T2 & T3 & T4 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27).
    (* [comment removed for export] *)
    exists r11. split.
    { replace (Z_to_bv 64 0x4e91c : word) with (0x4e91c : word) in RUN4 at 1 by (apply bv_eq; reflexivity).
      replace (0x78004 : word) with (Z_to_bv 64 0x78004 : word) in RUN8 by (apply bv_eq; reflexivity).
      replace (0x78e2c : word) with (Z_to_bv 64 0x78e2c : word) in RUN6 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x4ef64 : word) with (0x4ef64 : word) in RUN10 at 1 by (apply bv_eq; reflexivity).
      subst M7 M6 M5 M4 M3 M2 M1. (lazymatch goal with |- ?G => let G' := eval unfold fr_sA in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. eapply msteps_trans; [exact RUN9|].
      eapply msteps_trans; [exact RUN10 | exact RUN11]. }
    assert (R3c : getr r9 3 = getr r0 3) by (rewrite P3, Z3; viac AGX (3:reg); rewrite F3, E3, K3, B3; exact A3).
    assert (R4c : getr r9 4 = tp) by (rewrite P4, Z4; viac AGX (4:reg)).
    assert (R22c : getr r9 22 = getr r0 22) by (rewrite P22, Z22; viac AGX (22:reg); rewrite F22, E22, K22, B22; exact A22).
    assert (R23c : getr r9 23 = getr r0 23) by (rewrite P23, Z23; viac AGX (23:reg); rewrite F23, E23, K23, B23; exact A23).
    assert (R24c : getr r9 24 = getr r0 24) by (rewrite P24, Z24; viac AGX (24:reg); rewrite F24, E24, K24, B24; exact A24).
    assert (R25c : getr r9 25 = getr r0 25) by (rewrite P25, Z25; viac AGX (25:reg); rewrite F25, E25, K25, B25; exact A25).
    assert (R26c : getr r9 26 = getr r0 26) by (rewrite P26, Z26; viac AGX (26:reg); rewrite F26, E26, K26, B26; exact A26).
    assert (R27c : getr r9 27 = getr r0 27) by (rewrite P27, Z27; viac AGX (27:reg); rewrite F27, E27, K27, B27; exact A27).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - rewrite T2. viac AGP (2:reg).
    - rewrite T8. viac AGP (8:reg).
    - rewrite T9. exact V9.
    - rewrite T18. exact V18.
    - rewrite T19. viac AGP (19:reg).
    - rewrite T20. viac AGP (20:reg).
    - rewrite T21. viac AGP (21:reg).
    - rewrite T3. viac AGP (3:reg).
    - rewrite T4. viac AGP (4:reg).
    - rewrite T22. viac AGP (22:reg).
    - rewrite T23. viac AGP (23:reg).
    - rewrite T24. viac AGP (24:reg).
    - rewrite T25. viac AGP (25:reg).
    - rewrite T26. viac AGP (26:reg).
    - rewrite T27. viac AGP (27:reg).
  Qed.
End RUNSA.
End FPGen.
