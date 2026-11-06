(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W1 ASlot_I.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_RASlot_I () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec5STree4steq00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R;RMallocTree:rimplT_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocNat:eruns_steqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocNat2kSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocNat2bSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree8steq_symC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree7leaf_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R;RMallocTree@ralloc_meta_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R;RMallocTreeBrimplM_membed_steqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2CJ4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib2CJ4Spec5STree5erunsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2CJ1A:MallocTree3memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree8pupd_memC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec4Prog6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2CJ1A:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocNat2KFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R;RMallocTree;rimplT_bindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R;RMallocTree<rimplT_reachC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1R8RASlot_I;rimplT_steqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01c69OSSVerify5KrLib2CJ1R8RASlot_IAralloc_slot_stmt2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1R8RASlot_I;rimplT_nat2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocNat>alloc_slot_natC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib2CJ1R8RASlot_I8ras_pre2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2CJ1R;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib9AllocCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2CJ1R@RAllocSlot_iface9RAS_STACKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK69OSSVerify5KrLib2CJ3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2CJ3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00c69OSSVerify5KrLib2CJ1R8RASlot_I9ras_post2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2CJ1R:F_syscalls5rsegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2CJ1R:RMallocRepAralloc_slot_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocNat>alloc_meta_natC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2CJ1R;RMallocTree8ram_postC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2CJ1R;RMallocTree9RAM_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R:RMallocRepAralloc_meta_entryC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation RISTF := (@ISTF_g ref_reserved).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section AUXSEC.
Context {AUXM : auxv_mode}.

Definition RAMP_AS (am_pre : mstate -> Prop) : Prop :=
  forall st0 LB st sc st1, RAREACH st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 -> am_pre st1.

Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["AC_1"; "AUXSEC"] "h01Qh11Rh22msh31oh41sh52t1h62t2h71Hh82Hsh93ms'h:1rh;2s'p;1p;5p;7p;2p;3p;:p;9p;8p10000p4p70R0g000hR1p4p710p8P0p1001ap4p7210R2p8P0g002aR3p4p710p8P0p1003_R4p4p710R5p8P0p1004Up4p710R6p8P0p1005Kp4p710p8P0p1006Hp4p710R7p8P0p1007Dp4p7210R8p8P0p1008Bp5p7511110R9p8P0p1009Hp4p7210R0p8p100:Fp4p70R:P2p8P:P5p8P:P4p4p7210p8P:P6p8P:P7p8P:P8p8P:P9p8P:P0p8p200R0g00;>R:p4p7210p8P0g00<:R9p4p710p8P0P3p4p741110p8P0g00<oR8p4p7210p8P9j12TP1j59TP:j71Tg00>7j23Tg00>Wj28Tg00?Sj37TP3l:4TP8l95Tg00@0j86Tg00@hR8g00A`R3g00B>R:f3R1g00C6R9f2R7f1R6f0R4G6p=0%26R5%27R2g00D3R;f4R<g00DmR=p-0[\;[R>P8P3f6R?P<P1D9p,5ACEILR@f7RAP?f5RBP1P7P6F1P@f8RC,3:RDg00F4,8:REPCPAP?C0PEPCPAPBC0P<P?f;=7:7P6P4O3X9=X;;X:DP7P8P3P:PCPEP9P?PBP6PAM:4P4M95P@PCPAPBP<P1P7F1eW7W8X2=X0>X4;X62X55X3:X10P?PBP<P1P7P6P4O7X2=W0W4W6W5X3:X10o"). Qed.

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["AC_1"; "AUXSEC"] "p'0h03ms'h12s'h22H0h32HLh42HQh51Ph61Qh72QSh81Rh91Xh:1Yh;4bailh<1kh=2msh>1oi001oh?1rh@1shA1xi011xhB1yi021yhC1HhD2HBhE2HKhF3NAThG2R'hH1pi031pp;1p;2p;5p;6p;7p;4p;8p;<p;9p10000p4p70p200R0p8p100:Fp4p70R1P0p8P1p201R1p8P0g00;>R2p4p7210R3p8P0g00G1R4p4p73110R5p8P0p203R6p8P0g003_R7p4p710p8P0g004UR8p4p710R9p8P0g00GiR:p4p710p8P0g006HR;p4p710R<p8P0g00H_R=p4p7210R>p8P0g00I`R?p4p7210R@p8P1P3p8P1P5p8P1P6p8P1P7p4p7210p8P1P9p8P1P:p4p7210p8P1P<p8P1P>p8P1P@p8P6g00<:R@p4p710R>p8P6p1007Dp4p7210p8P6p1009Hp4p7210p8p202R<P3p8P<P4p4p741110p8P<g00JbR3p60621001p8P<P>p8P<P6p8P<P:p4p73110p8P<g005KR>p4p73110p8P<P=p4p73110p8P@j1:Tg00>7R@j20Tg00K`R9j11TP7j22TP8j13TP:j5=j68TP4j6<Tg000hj5?TP2j75TP;j44Tg00LBj17TP>j6>Tg00LdR>j29TP?j8CTg00M?j2;TP=l<BTP3l9ATg00Maj4@Tf4R3f3R=f2R?f1R;f0R2C@';p=6g00B>R4%:?R:\3\3%:;P:[[^G6R6%:3\3\3R:%:=R8g00D3R7f7R5f6RA'0#1g00DmRBp-0[\7RC[RDPC\ARCg00@hREg00A`RFf8RGPAPGf5RHP3O3PEPFf:RIf9RJ'0RK#1RLPGPAPL12IJ%3KO3PIPJPGPHP3D=E<D?p,5ACEILRKf;RL/0IRM#1RNPGP5PN12LI%3MO3P3P=P;F5f<RMPGf@RNf?RO'0RPPNPOP=P?D6P;P2O3fARQ/0NRR#1RSf>RTf=RUPS12QN%3RO3RVPRPQPNP3P=D6C4PKPNPOPUPHP3O2P=PJP?F5[[^0B^17^BM]AP510OTRW#7P;P2O3%1PRXPUPMPX12NO%3PO3%7PC4PKPOPTPLP=PGP?F5[[^0B^17PMPLPEPF10TURX#1RYPMPIPY12TU%3XO3RXPTPUPMPJPGD=RZE<R[PIPMPJPGO3R\P5PHP3PEPFPMP\P[P=E>PKPYPMPLPXPZP5PJP?P;P2O3PSPTPVP?C4'9X0BX17X?YPHP3PKPYPLPXP5PAP3P?GCP9PWPIP?P;P2O3fBRW/0QR9#1RXPOPTPX12WQ%39O3RLP?C4'9PKPQPNfCRZPWPQPTPUP=E8P?PIP;F5[^0B^17P2P@PQPNPMfDR@/0ZR[/;?R\P;P2O3%1[RFPQPNPF12@Z%3[O3P\C4'9PKPZPWfER\P@PZPNPO10\@RF/;=E8P?PMP;F5[^0B^17P2POfGREfFR]'0R^PEP]P=P?D6R_P;P2O3%1^R`P@PZP`12E]%3^O3P_C4'9P>PNfHR_/0ER^P_PEP3P=D6R`P?P;O3%1^RaP\P@Pa12_E%3^O3P`C4PKPEP]fIR`P_PEP@PZ10`_P`P_PHP3D6E8P=PNP?F5P2PWfJR^/0`P^P`PAPHD6P3P=O3fKRa/0^Rb#1RcP_PEPc12a^%3bO3PbPaP^P5PAD6C4POPGP5PAPHP;P2O6PKP^P`fLR`PaP^PEP]10`aP`PaPGP5D6E8PAPZPHF5eW3W4P;P2O2n2001000000120000000W2X0BX17XBZXAZP;P2O2n2001103000120101102XHPP2O1PJ%7RRRP;P2O3PSPTPVPRC4'9P>PI%79R9P?P;O3PXPOPLP9C4PKPQPNPZPWPQPTPU10ZW#7E8P=PIP?F5P2PM%7[P3P=O3%1FR[PWPQP[12\@%3FO3%7FC4PGPAPHP;P2O4PKP@PZP]P\P@PQPN10]\#7E8PAPUPHF5eW3W4P;P2O2n2001000000120000000W2X0BX17n10110000021110300X?YM<BM9AWDWEWCWFX=BX6CX7DX@7X;8X<:X56X>4X8<X:1X90PIPJPGP5PAPHP3P=P?P;P2O;X=BW6W7W@W;W<W5W>X8<X:1X90o"). Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).

Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["AC_1"; "AUXSEC"] "p'0h03ms'h12s'h22HPh34fuelh43idxi003idxh51ri011rh63st1i023st1h72A0h82A1h92ASh:3AUXh;2BLh<3CLOh=2ERh>1Fh?1Hh@2HLhA1KhB2LOhC2MIhD2MRhE3PREhF1QhG1RhH2R'hI2SThJ2TKhK2TPhL2UAhM2a0hN2a1hO2a2hP2a3hQ2a4hR2a5hS2a6hT2a7hU2b'hV4bailhW4errvhX2fchY2gphZ1kh[2k'h\2loh]1mh^1oh_2rah`3reqha1shb2s0hc2s1hd3s10he3s11hf2s2hg2s3hh2s4hi2s5hj2s6hk2s7hl2s8hm2s9hn2scho2sphp2sthq3st0hr2t0hs2t1ht2t2hu2t3hv2t4hw2t5hx2t6hy2tphz1xh{1yi031pp%0p;1p;2p;5p;4p;3p;Np;9p;7p;Op;8p;?p10000p4p70g00NAR0p61651111001R1p8p100:Fp4p70P1p8P1g00;>R2p4p7210R3p8P1g00<:R4p4p710R5p8P1g009HR1p4p7210R6p8p200R7P3p8P7P5p8P7g00OER5p6064111003p8P7g00PCR3p4p741110p8P7P6p8P0j1]TP4j1<Tg00QEj10Tg00Qjj13Tg00RHj1=Tg00Rkj19Tg00SPj2QTg00T<j5HTg00U7j4CTg00V1j1BTg00Vmj3ATg00Wjj2?Tg00Xjj22Tg00YTj5\Tg00ZRj4UTg00[Gj1TTg00\Cj2;Tg00\_j1STg00]cj2RTg00^@j1PTg00^^j2MTg00_;j1KTg00`3j1GTg00`Sj3FTg00a3j4DTg00alj2ETg00bcj26Tg00cIj3:Tg00cclN1Tg00>7R4j2ITg00K`R0j1JTg003_j2@Tg004Uj1LTP1l95Tg00Maj4NTg00M?j2OTg006Hj44TP2j77Tg00d_lO>Tg00LBj18Tg00eTj1[Tg00fPj7ZTP3l9YTg00gEj4VTg001aj8WTP5l?XTg00h>S00Q00f0R3#]g00h]R2g00A`R1f2R6#<[[R8f1R9#<R:g00B>R;g00D3R<f4R=g00DmR>p-0R?[\<[g00iY#0R@#0#0#0#0RA#0#3RB#=RC%9@R@#3/QC%3A#=f5RAP=P6P9f_RDDHp,5ACEILREp,4RRNDRFPAf7RGCCf6RH#Bf]RIf9RJ5AGf8S01/?IPEPFp,4AUXMf;RFf[RK,2BD\g00j>RLf<S02PJf\RM,2BCU%TEf:RN';f^RO,2B%SN'R,;FPLf?S0312BI%0@#0#9#0#0#P'Mg00k8R@%KJ%G@3FCDf@R@,ELg00l0,6B9:CDfZRPf>S04,6B5:CRQfiRRfhRSfgRTffRUfbRVfaRWfXRXfWRYfVRZfUR[fTR\fSR]fRR^fQR_fPR`fORafJRbfIRcflRdfHRefGRffFRgfkRhfERifDRjfCRkf3RlP6P9P3MN11I21Rm#JRnfmRoPEPng00liRpfrPfPiPj1@21Rq%LmRrM95S05P2P1P=PlCN,OmRsC4PEfqRtfnRufpS06PAP=O2PlPdP6F7[[^0>^1<^41^62P2P1PdPRP5p6067111110002PEP6PpPtPgPjPkP9P3M95XU:X[8WHPhfjR8PSP0PmP?P6P4P2P1P?P3PdPhP8PRfeR:fdR5PKPPfYRvPXPYPZP[P\P]P^fMRwfLRxfoRyfKRzPbPcPuPePfPgP9P3P=PlMN1n2001103000120102100g00meR{n10110100021010300X0>X1<X5nS07PTPUP:P5fcR|PVPWf`R}PDPOPIPMPKPPPvPXPYPZP[P\P]P^P_P`PafNR~PwPxPzPbPcPeMO>Pfg00nB,6BPg%8CPi%[LFZPEPpPuPdPkfARBP@PhP8M9YPoPnPqPrPRPSQ07PUP:P5P|PVPWP}PDPOPIPMPKPPPvPXPYPZP[P\P]P^P_P`PaP~PwPxPzPbPcPePfPgPiPjPkfBPBP@Q03Q04f=Q02PFPNPJQ01PGPHPAP=PlP6P9P8PRPSPTP|PVPvPXPYPZP[P\P]P^P_P`PzPbPoPcPePfPdPgPiPjPlP6P9P3MN1RjPEPnPuPsP6P0PmP?P6P4P2P1P?P3PtQ06PyPuP8PRP}PDPOPIPMPKPPPvPXPYP^P_ftP`PaP~fsR~PwPxPzP9P3P=PlMN1n2001103000120102100P{n10110100021010300X0>X1<X5nP9PLPdPhP8PRP:P5PKPPPvPXPYPZP[P\P]P^PwPxPyPzPbPcPuPePfPgPAP=PlP3MN1X0>P9P3CVGWW2X0>X1<X41X62OmPnPuPEPnPpP~PePgPiPqPrM95PsC4PHPAP=PlP6P9P3O6W@X2jX0>X1<X{1Xz2P{PnPoQ05%8mC4PEPtPuPyP=PdPlF7[P3n010000000X?{X0>X1<M?XWAX8QW7WKWCW=WBW<WIW:W;WLWJWDWEXWCX`1Xn1X\1Xp2Xq2X];WXW>XxCXwCXvCXuCXeCXdCXmCXlCXkCXjCXiCXhCXgCXfCXTCXSCXRCXQCXPCXOCXNCXMCXcCXbCXtCXsCXrCXyCXYCXoCW_WFWaW^WVWZXG7W9W3P3O1W3o"). Qed.

Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 0x1006b8 ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["AC_1"; "AUXSEC"] "p'0h03ms'h12s'h21Hh32HBh42HPh56am_preh62moi002moh71ri011rh83st1i023st1h92AMh:3AUXh;2BLh<3CLOh=2ERh>1Fh?2HLh@1KhA2LOhB2MIhC2MRhD3PREhE1QhF1RhG2R'hH2SThI2TKhJ2TPhK2a0hL2a1hM2a2hN2a3hO2a4hP2a5hQ2a6hR2a7hS2b'hT4bailhU4errvhV2fchW2gphX1khY2k'hZ2loh[1mh\1oh]2rah^1sh_2s0h`2s1ha3s10hb3s11hc2s2hd2s3he2s4hf2s5hg2s6hh2s7hi2s8hj2s9hk2sphl2sthm2t0hn2t1ho2t2hp2t3hq2t4hr2t5hs2t6ht2tphu1xhv1yi031pp%0p;4p;1p;2p;5p;3p;Mp;7p;Op;8p;?p201R0g00;>R1p4p7210p8P0g00<:R2p4p710p8P0g00OER3p6064111003p8P0g00oHR4p4p7210p8P0g007DR5p4p7210p8g008Bj4^TP2j1ATg00QEj11Tg00Qjj19Tg00RHj1>Tg00Rkj12Tg00SPj2MTg00U7j4ETg00V1j1DTg00Wjj24Tg00Xjj27Tg00YTj5BTg00ZRj4]Tg00[Gj1VTg00\Cj2?Tg00]cj2TTg00^@j1STg00^^j2QTg00_;j1PTg00`3j1OTg00`Sj3NTg00a3j4LTg00alj2KTg010Jj1GTg00bcj2=Tg00cIj3FTg010hlM3Tg00>7R2j2HTg00K`R6j1ITg003_j2JTg004Uj1CTP5j55Tg00Maj4<Tg00M?j2;Tg006Hj48TP1j7:Tg00LdS00j26Tg00d_lORTg00LBj1@Tg00eTj1\Tg00fPj7[TP4j5ZTg011fj4WTg00gEj4XTg001aj8YTP3l?UTf0R4#1#1p=0g00h]R1p-0R5[R7p,5ACEILR8p,4RRNDR9p,4AUXMR:P4C^g00:FR;f2R<#A[\1R=f1R>#AR?g00B>R@g00D3RAf4RBg00DmRCP5[\A[g00iYRD#1RE#0#0RF#1#9RG#>RH%2ERE#9/MH%9F#>g00A`f\RFP<O1P8P9f3RIPBCE%DBf5RJfYRK'4P8P9P:f7RLfWRM,7GDBg00j>RNf8ROf6RPfXRQ,7GC]%V8/?LfZRR,7Gg012A'T,?OPNf;S0117GK%0E#2#0#S'Qg00k8RE%PO%OE3NCLf<S02,KNf[RE%1D#0#0#0#0#2#2#1#2#1#2#2#2#1#0#G,=G5FHP8P9P:fcRDfbRSfaRTf`RUPFPEfRRVfQRWfPRXfORYfNRZfMR[fLR\fKR]fJR^fIR_fDR`fCRafARbfeRcf@RdfBRePIP<P>P4MM314B<Rf1H1;Rg#IRhfhRiP8PhPa1J1;Rj%CgRkD5P1P;PJPBC<,;gRlC8P8flRmfiRnfkRoPPPJO2PBfgRpPIF:[[[^0C^1A^6;^81P1P;ffRqPDP3p6067111110002P8P<PbP>P4D5XS?XY=WGPcfdR=PSP6PgP5P<P2P1P;P5P4P8P9P:PqPcP=PDf_R?f^R3fURrfTRsfSRtPVPWPXPYPZP[P\fGRufFRvP`PiPafERwP>P4PBPIMM314>BRx'6n2001103000120102100g00meRyn10110100021010300X0CX1AX7hRzPTPUP?P3f]R{PFPEPRPKPQPMfVR|PrPsPtPVPWPXPYPZP[P\P]P^P_fHR}PuPvPwP`PaPeMORPbg013@,=GPd%@Hf?RG%\NF[P8Pqf>R~PcP=DZPpPhPjPkPDPSPzPUP?P3P{PFPEPRPKPQPMP|PrPsPtPVPWPXPYPZP[P\P]P^P_P}PuPvPwP`PaPePbPdPGP~f=Q02Q01f:R~f9RGPOPLPPPJPBPIP<P>P8P9P:P=PDPSPTP{PFPtPVPWPXPYPZP[P\P]P^PwP`PePqPbPaPIP<P>P4MM3RbP8PhPnPlPIP6PgP5P<P2P1P;P5P4P8P9P:PmPofjR5PnPcP=PEPRPKPQPMP|PrPsPtPVP[P\P^fnP_P]P>P4PBPIMM3/6xn2001103000120102100Pyn10110100021010300X0CX1AX7hP<PNP8P9P:PpPqPcP=PUP?P|PrPsPtPVPWPXPYPZP[P}PuPwPnP`PvPPPJPBP4MM314PB'6X0CP<P8P9P:PqPcP=PDP?P3PrPsPtPVPWPXPYPZP[P\PuPvP`PiPaPwPJPBPIP<MM314JIP>P4CWCXGYX3fW4X0CX1AX6;X81Og14I>,6bQ00P8P9P:PcP=PDPSP3P{PsPtPVPWPXPYPZP[P\P]PvPwPaPpPeP`PBPIP<P>MM3PfPhPnP8PhP`PjPkD5PlC8P8fmP5PmPPPJO2PBPiPIF:[P4P8P9P:PpPqPcP=PUP?P|PrPsPtPVPWPXPYPZP[P}PuPwPnP`PvPPPJPBPIMM314LJPhPmP8PhPuPjPkD5P1P;POPLC<,;gC8P~PGPOPLPPP<P>P4O7W?W3W4P>P4O2n2001000000120000000W2X0CX1AXv;Xu1PyPhPpP8PhPePjPkD5%@gC8P8PoPiPnPBPqPIF:[P4n010000000X2yX0CX1AM?UW@WJWBW=WAW<WHW:W;WIWCWDXUHWZXl1X[@WVW>XsHXrHXqHXpHXbHXaHXjHXiHXhHXgHXfHXeHXdHXcHXRHXQHXPHXOHXNHXMHXLHXKHX`HX_HXoHXnHXmHXtHXWHXkHW]WEW^W\WTWXXF0W9X57P4O1W5o"). Qed.

End AUXSEC.

End AC_1.
