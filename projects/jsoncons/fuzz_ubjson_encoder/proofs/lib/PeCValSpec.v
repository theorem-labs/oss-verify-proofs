(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core PmLayout PmStatics PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCValSpec () := "c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCValSpec5PECVSAvalidate_fun_specC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP5entryC13~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP6pm_scrC13~~~C56Stdlib6ZArith6BinInt1Z3subC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PmStatics4PMST7base_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib5Lists7ListDef6Forall00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface>regs_preservedC13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L59frame_butC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk9mem_growsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP3cfgC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef:utf8_validC13~~~C47Corelib4Init5Logic3iffI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

Definition validate_fun_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (p n sp r : Z) (l : list Z),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n ->
    (n = 0 \/ sp <= p \/ p + n <= sp - PMSP.pm_scr 0) ->
    PMST.base_ok segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (v : Z),
        regs_preserved R R' -> L5.frame_but [(sp - PMSP.pm_scr 0, PMSP.pm_scr 0)] M M' -> mem_grows M M' ->
        getr R' 11%bv = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model) K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.

(* [comment removed for export] *)
Lemma scan_of_fun pc : validate_fun_spec pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (p n sp r : Z) (l : list Z),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n ->
    (n = 0 \/ sp <= p \/ p + n <= sp - PMSP.pm_scr 0) ->
    PMST.base_ok segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> L5.frame_but [(sp - PMSP.pm_scr 0, PMSP.pm_scr 0)] M M' -> mem_grows M M' ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model) K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCValSpec ()) ["Specs"] "h02M'h12R'h23fx'h32pch42H1h53H10h63H11h73H12h83H13h93H14h:3H15h;3H16h<2H2h=2H3h>2H4h?2H5h@2H6hA2H7hB2H8hC2H9hD1KhE4KONThF1MhG2P1hH2P2hI2P3hJ1RhK2VFhL2_HhM3_H0hN3_H1hO1bhP2fxhQ1lhR5modelhS1nhT1phU1rhV2sphW1vp;1p;2p;3p;7p;4p;6p;5g0000j1[Tg001Mj10Tg0022j14Tg002Wj19Tg0035j1ITg003Xj2UTg004Dj1CTg004fj1ATg005Fj1STg006=j1PTg006_j31Tg0079j2>Tg007Yj1JTg008Qj1<Tg0091j7VTg00:>j12Tg00:\j3GTg00;?j27Tg00<Gj2DTg00<mj23Tg00=Ij2BTg00=fj25Tg00>Bj2:Tg00>]j2;Tg00?7j2@Tg00?Tj3RTg00@`j1QTg00Anj26Tg00BKj3OTg00C\j4NTg00Dij2LTg00EIj1KTg00Eij3MTg00FJj2?Tg00G]j4ETg00H=j3=Tg00H]j3HTg00Ikj2FTg00K7j1TTg00L=j6ZTg00MHj5YTg00NTj1XTg00Oej2WTg00P>R0f0R1g00P\R231p=8%[1g00Q:R3g00RGR4#0R5#4R6#9R7%05#0R8#0#0#0R9#9R:#IR;'UR<%98#I#C\;R8g00Rlg00Sb%A0%C;f6R=#S%P;311>;;R>#Af7R?#J%<>31P?g00Tj#<O1p,1AR>p,1Lf;R@f:RAf5RBf4RCP2FVf<RD%06#2g00U`RE5G7'7f8RF,D:RG51;f=RH%46R6#2=G7ERE'7=1;Gf9RG,32%25R5%44R4#0#4#0#2'B,5G':132@%8@152D';1@HD%46#4#2,B5'3fAR5f>R6;RH%86f?R7,3H1@76%Q2RI,6H'3';';p,4segsRJfCRK7O>PJfDR>P5PHCN1L06#K=1051321%09#0#2,51':XO0=M07fKR9f1RL'?1>00RMP0P0fFRN/6IPICE%<MRO3=?H9LfLRPf2RQ'Fp,3bmKPJp,6SCFG_P#TPJPBPCfGRJf3RRPPEZP9DY[[[^08^1<^23P9fJR9fIfHRPPJPNfEP>PKfBP5f@P7P6PHPDP@PAPGPFP?P=PBPCPRPQPLfMRL/?QP0P016PIPICE==MO?HLQfN/FR17BE1D:R51;132C%44#2,5C':%8Bg00V<%X9g00V\31'WPAPGPFP?PBPCPRO6WNWMWLWIWHWGXW0X08X1<X23OKWEW;W:W9W8W7W6W5WCWBWAW@W?W>W=W<W4WQXU0XV0XS0XT0WDWRWFWJWPWKX30P1O1X30o"). Qed.
End Specs.
End PECVS.
