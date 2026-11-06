(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4skx () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib6Common5KXTac4zregC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib6Common4KXGo>Forall_map_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common5KXTac4ztabC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac4zshzC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib6Common5KXTac2kEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9kentry_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib6Common8KXBridge4zexp02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common5KXTac2zk01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6Common4KXGo;atom_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6zk_entC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Common8KXBridge4zdenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo;zk_range_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib6Common4KXGo>atom_ranges_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common7KXSound3KXS7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6shz_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo6shz_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6tab_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo7tabs_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Common5KXTac9region_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common8KXBridge4zexp01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Common5KXTac6zr_regC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX25saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zsaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib6Common4KXGo>zr_ok_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoF6win_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoF5zw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM6unp_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM5zu_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM8unp_raccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM:zur_ok_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoF8shz_raccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGoCForall2_map_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge9zatoms_ltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C59OSSVerify5KrLib6Common8KXBridge:kx_regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge2zxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge5lnormC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge4mkRlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge7kx_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge6kx_envC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac7kE_atomC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common6KXExec3KX22evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX29sym_state01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk8kxl_execC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge<reads_scopedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM6rv_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM9rv_chk_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk5rv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk>kxl_know_finalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge:rfull_mkRlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM8sc_auto3C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC69OSSVerify5KrLib6Common7KXSound3KXS9scs_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8sc_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM<kx_scs_bulk3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM9acc_auto3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXFoot4accPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM@kx_accs_ok_part3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<kx_regs_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9mem_denotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib6Common6KXExec3KX26edenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common6KXExec3KX26erangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib6Common8KXBridge7kx_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost8kE_atomsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost?kx_regs_keep_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXChk<kx_run_evtFLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXGoM<kx_pendingFmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K69OSSVerify5KrLib6Common6KXExec3KX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX28sidecond01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX28sidecond06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost<kx_erange_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost7kx_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib6Common8KXBridge4zexp00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib6Common6KXExec3KX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02I69OSSVerify5KrLib6Common6KXExec3KX26kentry00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I69OSSVerify5KrLib6Common6KXExec3KX28sidecond00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I59OSSVerify5KrLib6Common5KXTac2zk00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib6Common6KXExec3KX23env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX27scripts00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX26sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW<AF_huf_z4skx:z4s_J_caseC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Notation amem := (word -> option byte).

Lemma z4s_byte_rng : forall w : word, 0 <= bv_unsigned w <= 255 -> 0 <= bv_unsigned w < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4skx ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51wp;1p;2p;4p;8p;3p;7g0000j10Tg000Uj1LTg0013j1@Tg001Vj27Tg002@j22Tg002\j11Tg003Aj18Tg003_j23Tg004:j1>Tg004Zj1=Tg005:j2<Tg005Xj1;Tg0066j1:Tg006aj26Tg007Dj2KTg007gj45Tg008Rj1JTg0094j8CTg009Xj2BTg00::j2ATg00:Tj2?Tg00;@j3DTg00;Zj3ETg00<9j4FTg00<kj2GTg00=Gj7HTg00=kj7ITf1R0g00>OR1g00>nR2P2g00?NR3f0R4g00?nFHp=4f2R5P1P2P2P3P0P4FIp=9g00@NR6#0#0#0#0#0#0R7#LR8#@g00A3R91784R:'2%16#1#1#1#1#1#1#8R;,2:'3g00AQR:g00AoR<#>%=<1<:0%;:%::R<P1P2P2P3P:16:9g00B[R11K:6R6C5,4<R=P:P6P116:;C5,4<59<%J2P:P6g00CB%07#0#8R7,6:C5,4<99<=GC1B<3P4P5g00CiR<g00DIR3'A1?45=D<3dAE:90CFb2b3b4W01294124;'312901G07'3[^0:P41785P0O2b1UW5o"). Qed.

Ltac z4s_rng :=
  lazymatch goal with
  | |- ?lo <= bv_unsigned (ev ?E ?j) <= ?hi => let H := fresh "H" in kx_range (EVar j) H; exact H
  | |- 0 <= bv_unsigned (ev ?E ?j1) + 256 * bv_unsigned (ev ?E ?j2) < 65536 =>
      let H1 := fresh "H" in let H2 := fresh "H" in kx_range (EVar j1) H1; kx_range (EVar j2) H2; lia
  end.

Definition z4s_J_case : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
         (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (SS n SBL SBH : Z) (sbuf : list byte),
    mem_inv bsegs mm ->
    bytes_at bsegs mm SS sbuf -> Z.of_nat (length sbuf) = n ->
    unpoisoned mm SBL SBH -> SBL <= SS -> SS + n <= SBH ->
    rng RNG SS n -> rng RNG (shad SBL) (shlen (SBH - SBL + 7)) ->
    SBL mod 8 = 0 ->
    4096 <= SS -> SS + n <= 2^47 -> 10 <= n < 2^26 ->
    4096 <= SBL -> SBH <= 2^47 ->
    (forall (l1 l2 l3 : Z) (a0 a2 a7 t0 t1 t2 t3 : word),
       0 <= l1 < 65536 -> 0 <= l2 < 65536 -> 0 <= l3 < 65536 ->
       evtF bsegs RNG Q (MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 (SS + 6 + l1 + l2)) a0 (Z_to_bv 64 (SS + 6)) a2
                                 x13 x14 (Z_to_bv 64 l1) x16 a7 (Z_to_bv 64 l3) (Z_to_bv 64 l2) (Z_to_bv 64 (SS + 6 + l1))
                                 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 t3 x29 x30 x31)
                            F (Z_to_bv 64 0x8e6a4) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 SS) x13 x14 x15 x16 x17 x18 x19 x20
                             (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x8e590) fc None mm (seg_rom bsegs)).

Ltac z4j_us :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => rewrite (u_small z) by lia end
  end.

Ltac z4j_acc RS KXA :=
  unfold accP, adenot, PropExec.v_addi; cbn [a_base a_off edenot fst snd];
  repeat (match goal with |- context [ev ?E ?j] => rewrite (KXA j) by (cbn; lia) end); cbn [nth];
  z4j_us;
  let R3 := fresh "R3" in destruct RS as (_ & _ & R3); apply R3; cbn; lia.

Ltac z4j_rngs :=
  repeat match goal with
  | |- context [bv_unsigned (ev ?E ?j)] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
      | _ => let H := fresh "Rb" in kx_range (EVar j) H
      end
  end.

Theorem z4s_J : z4s_J_case.
Proof.
  unfold z4s_J_case.
  intros Q RNG mm F fc x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         SS n SBL SBH sbuf MI BS LS UNP L1 L2 RS RSH A8 B1 B2 B3 B4 B5 K.
  kx_runFmd [0x8e6a4] 200%nat [true; true; true]
    [KZRange SS 4096 (2^47 - 10); KZRange n 10 (2^26)]
    [(SS, n)] (@nil (Z * Z)) [(SS, n)].
  all: try (lazymatch goal with |- accP _ _ _ => z4j_acc RS KXA end).
  kx_post_regs_keep.
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ ?t0 ?t1 ?t2 _ _ ?a0 _ ?a2 _ _ (Z_to_bv 64 ?l1) _ ?a7 (Z_to_bv 64 ?l3) (Z_to_bv 64 ?l2)
                         _ _ _ _ _ _ _ _ ?t3 _ _ _) _ _ _ _ _ _) =>
      eapply evtF_eq; [| apply (K l1 l2 l3 a0 a2 a7 t0 t1 t2 t3)]
  end.
  all: try (z4j_rngs; lia).
  all: repeat (first [reflexivity | (apply (f_equal (Z_to_bv 64)); lia) | f_equal]).
Qed.
