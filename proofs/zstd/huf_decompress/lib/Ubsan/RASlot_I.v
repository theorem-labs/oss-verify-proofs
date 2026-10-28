(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W1 ASlot_I.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_I () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrI5ARocqVerifyHarness?AgentSubmission4Spec5STree4steq00C5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree:rimplT_retC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat:eruns_steqC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat2kSC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree8steq_symC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat2bSC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree7leaf_ofC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree@ralloc_meta_stmtC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:alloc_metaC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc:alloc_slotC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree6rimplTC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc1MC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTreeBrimplM_membed_steqI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4Spec:MallocCtrl4pselC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission4Spec5STree5erunsI5ARocqVerifyHarness?AgentSubmission4Spec6Malloc2ev00I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree3memC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree8pupd_memI5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree8pans_memC5ARocqVerifyHarness?AgentSubmission4Spec5STree5sbindC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat2KFC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree;rimplT_bindC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree<rimplT_reachc5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_I;rimplT_steqI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission5Ubsan@RAllocSlot_iface8ras_postK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission4Spec6Malloc6mstate00I5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I7as_inv200c5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_IAralloc_slot_stmt2C5ARocqVerifyHarness?AgentSubmission5Ubsan@RAllocSlot_iface@ralloc_slot_stmtI47Corelib4Init9Datatypes3nat00c5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_I;rimplT_nat2C5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat>alloc_slot_natc5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_I8ras_pre2C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep5rmrepC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep8ticks_okC5ARocqVerifyHarness?AgentSubmission6Malloc9Malloc_fp9unk_agreeC5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree;brk_link_psC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8rauxv_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission5Ubsan@RAllocSlot_iface9RAS_STACKC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00c5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_I9ras_post2C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RATPC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc8full_layI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRepAralloc_slot_entryC5ARocqVerifyHarness?AgentSubmission6Malloc9MallocNat>alloc_meta_natK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8ram_postK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree9RAM_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRepAralloc_meta_entry".
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g _ ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["CANSEC1"] "h01Qh11Rh22msh31oh41sh52t1h62t2h71Hh82Hsh93ms'h:1rh;2s'p;1p;5p;7p;2p;3p;:p;9p;8p10000p4p70R0g000eR1p4p710p8P0p1001[p4p7210R2p8P0g002\R3p4p710p8P0p1003\R4p4p710R5p8P0p1004Tp4p710p8P0p1005Sp4p710R6p8P0p1006Kp4p710R7p8P0p1007Ip5p73110R8p8P0p1008Pp4p710R9p8P0p1009Kp4p710R0p8p100:Fp4p70R:P2p8P:P5p8P:P4p4p7210p8P:P6p8P:P7p8P:P8p8P:P9p8P:P0p8p200R0g00;;R:p4p7210p8P0g00<8R9p4p710p8P0P3p4p741110p8P0g00<jR8p4p7210p8P9j12TP1j59TP:j71Tg00>3j23Tg00>Sj28Tg00?Lj37TP3l:4TP8l95Tg00?ij86Tg00@^R8g00ASR3g00B1R:f3R1g00BkR9f2R7f1R6f0R4G6p=0%26R5%27R2g00CjR;f4R<g00DcR=p-0[\;[R>P8P3f6R?P<P1D9p,2rcR@f7RAP?f5RBP1P7P6F1P@f8RC,3:RDg00Ej,8:REPCPAP?C0PEPCPAPBC0P<P?f;=7:7P6P4O3X9=X;;X:DP7P8P3P:PCPEP9P?PBP6PAM:4P4M95P@PCPAPBP<P1P7F1eW7W8X2=X0>X4;X62X55X3:X10P?PBP<P1P7P6P4O7X2=X0>X4;X62X55X3:X10P?PBP<P1P7P6P4O7X2=W0W4W6W5X3:X10o"). Qed.

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["CANSEC1"] "p'0h03ms'h12s'h21Ph31Qh42QSh51Rh61Xh71Yh84bailh91kh:2msh;1oi001oh<1sh=2H0h>2HLh?2HQh@1rhA1xi011xhB1yi021yhC1HhD2HBhE2HKhF3NAThG2R'hH1pi031pp;1p;2p;5p;6p;7p;4p;8p;<p;9p10000p4p70p200R0p8p100:Fp4p70R1P0p8P1p201R1p8P0g00FiR2p4p73110R3p8P0g00;;R4p4p7210R5p8P0p203R6p8P0g003\R7p4p710p8P0g005SR8p4p710R9p8P0g00G^R:p4p710p8P0g006KR;p4p710R<p8P0g00HVR=p4p7210R>p8P0g00IXR?p4p7210R@p8P1P3p8P1P5p8P1P6p8P1P7p4p7210p8P1P9p8P1P<p8P1P:p4p7210p8P1P>p8P1P@p8P6g00<8R@p4p710R>p8P6p1008Pp4p710p8P6p1009Kp4p710p8p202R<P2p4p741110p8P<P5p8P<g00J[R5p60521001p8P<P>p8P<P6p8P<g004TR>p4p73110p8P<P:p4p73110p8P<P=p4p73110p8P@j1:Tg00>3R@j20Tg00KZR9j11TP7j22TP8j13TP:j5=j68TP2j6<Tg000ej5?TP4j75TP;j44Tg00L<j17TP>j6>Tg00L^R>j29TP?j8CTg00M9j2;TP=l<BTP5l9ATg00M[j4@Tf4R5f3R=f2R?f1R;f0R4C@';p=6g00B1R2%:?R:\5\5%:;P:[[^G6R6%:5\5\5R:%:=R8g00CjR7f7R3f6RA'0#1g00DcRBp-0[\7RC[RDPC\ARCg00@^REg00ASRFf8RGPAPGf5RHP5O3PEPFf:RIf9RJ'0RK#1RLPGPAPL12IJ%3KO3PIPJPGPHP5D=E<D?p,2rcRKf;RL/0IRM#1RNPGP3PN12LI%3MO3P5P=P;F5f<RMPGf@RNf?RO'0RPPNPOP=P?D6P;P4O3fARQ/0NRR#1RSf>RTf=RUPS12QN%3RO3RVPRPQPNP5P=D6C4PKPNPOPUPHP5O2P=PJP?F5[[^0B^17^BM]AP310OTRW#7P;P4O3%1PRXPUPMPX12NO%3PO3%7PC4PKPOPTPLP=PGP?F5[[^0B^17PMPLPEPF10TURX#1RYPMPIPY12TU%3XO3RXPTPUPMPJPGD=RZE<R[PIPMPJPGO3R\P3PHP5PEPFPMP\P[P=E>PKPYPMPLPXPZP3PJP?P;P4O3PSPTPVP?C4'9X0BX17X@YPHP5PKPYPLPXP3PAP5P?GCP9PWPIP?P;P4O3fBRW/0QR9#1RXPOPTPX12WQ%39O3RLP?C4'9PKPQPNfCRZPWPQPTPUP=E8P?PIP;F5[^0B^17P4P@PQPNPMfDR@/0ZR[/;?R\P;P4O3%1[RFPQPNPF12@Z%3[O3P\C4'9PKPZPWfER\P@PZPNPO10\@RF/;=E8P?PMP;F5[^0B^17P4POfGREfFR]'0R^PEP]P=P?D6R_P;P4O3%1^R`P@PZP`12E]%3^O3P_C4'9P>PNfHR_/0ER^P_PEP5P=D6R`P?P;O3%1^RaP\P@Pa12_E%3^O3P`C4PKPEP]fIR`P_PEP@PZ10`_P`P_PHP5D6E8P=PNP?F5P4PWfJR^/0`P^P`PAPHD6P5P=O3fKRa/0^Rb#1RcP_PEPc12a^%3bO3PbPaP^P3PAD6C4POPGP3PAPHP;P4O6PKP^P`fLR`PaP^PEP]10`aP`PaPGP3D6E8PAPZPHF5eW>W?P;P4O2n2001000000120000000W=X0BX17XBZXAZP;P4O2n2001103000120101102XHPP4O1PJ%7RRRP;P4O3PSPTPVPRC4'9P>PI%79R9P?P;O3PXPOPLP9C4PKPQPNPZPWPQPTPU10ZW#7E8P=PIP?F5P4PM%7[P5P=O3%1FR[PWPQP[12\@%3FO3%7FC4PGPAPHP;P4O4PKP@PZP]P\P@PQPN10]\#7E8PAPUPHF5eW>W?P;P4O2n2001000000120000000W=X0BX17n10110000021110300X@YM<BM9AWDWEWCWFX:BX3CX4DX<7X88X9:X26X;2X5<X71X60PIPJPGP3PAPHP5P=P?P;P4O;X:BX3CX4DX<7X88X9:X26X;2X5<X71X60PIPJPGP3PAPHP5P=P?P;P4O;X:BW3W4W<W8W9W2W;X5<X71X60o"). Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
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

Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["CANSEC1"] "h01Fh12fch22gph33idxh42loh51mh61oh72rah83reqh91sh:2s'h;2s0h<2s1h=3s10h>3s11h?2s2h@2s3hA2s4hB2s5hC2s6hD2s7hE2s8hF2s9hG2schH2sphI2sthJ3st0hK3st1hL2tpp;1p;2g00N;j10Tg00N`j11Tg00O>j12Tg00Oaj13Tg00PFj26Tg00Q2j25Tg00R6j24Tg00RP#0R0#0#0#0#0R1#0#1#2R2%30#1/62%11#2g00B1R1g00S5R0g00CjR3g00ASR4g00Dcp-0[^:3^34^K0^84^G4]4]9^I0]J^51]6]1]0^>2^=2^F2^E2^D2^C2^B2^A2^@2^?2^<2^;2^L2^22^H2]7p,2rcg00Sn'5'4o"). Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["CANSEC1"] "h01Hh14fuelp;1p10000p4p70g00TkR0p615311001R1p8p100:Fp4p70P1p8P1p100;;p4p7210p8P1p100<8p4p710p8P1p1009Kp4p710p8P1p100V0p5p7511110R2p8P2P1p8P0j10Tg00W<f0R0#0]1P0W0o"). Qed.

(* [comment removed for export] *)
Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["CANSEC1"] "p'0h03ms'h12s'h24fuelh32HPh43idxi003idxh51ri011rh63st1i023st1h72A0h82A1h92ASh:3AUXh;2BLh<3CLOh=2ERh>1Fh?1Hh@2HLhA1KhB2LOhC2MIhD2MRhE3PREhF1QhG1RhH2R'hI2SThJ2TKhK2TPhL2UAhM2a0hN2a1hO2a2hP2a3hQ2a4hR2a5hS2a6hT2a7hU2b'hV4bailhW4errvhX2fchY2gphZ1kh[2k'h\2loh]1mh^1oh_2rah`3reqha1shb2s0hc2s1hd3s10he3s11hf2s2hg2s3hh2s4hi2s5hj2s6hk2s7hl2s8hm2s9hn2scho2sphp2sthq3st0hr2t0hs2t1ht2t2hu2t3hv2t4hw2t5hx2t6hy2tphz1xh{1yi031pp%0p;1p;2p;5p;3p;4p;Np;8p;7p;Op;?p200R0g00;;R1p4p7210p8P0g00<8R2p4p710p8P0g00W[R3p6054111003p8P0g00XZR4p4p73110p8P0g009KR5p4p710p8g00Tkj1]TP2j1<Tg00N;j10Tg00N`j13Tg00O>j1=Tg00Oaj19Tg00PFj2QTg00Y^j5HTg00ZZj3CTg00[Uj1BTg00\Sj3ATg00]Rj2?Tg00^Tj22Tg00_>j3\Tg00`=j4UTg00`oj1TTg00aej2;Tg00bAj1STg00cFj2RTg00ccj1PTg00dAj2MTg00d^j1KTg00eSj1GTg00f3j3FTg00fSj4DTg00gIj2ETg00h=j26Tg00hcj3:Tg00i=lN1Tg00>3R2j2ITg00KZR6j1JTg003\j2@Tg005Sj1LTP5j85Tg00M[j4NTg00M9j2OTg006Kj44TP1j77Tg00j:lO>Tg00L<j18Tg00jlj1[Tg00kej7ZTP4j8YTg00lWj4VTg001[j8WTP3l?XTg00W<R4f0R1#]g00S5R5g00ASR7f2R8#<[[R9f1R:#<R;g00B1S00g00CjR<f4R=g00DcR>p-0R?[\<[g00RP#0R@#0#0#0#0RA#0#3RB#=RC%9@R@#3/QC%3A#=Q00f5RAP=P8P:f_RDDHp,2rcREf7RF7CAf6RG#Bf]RHf9RI5AFf8S01/?Hf;RJf[RK,2B5\Eg00mMRLf<S02PIf\RM,2BCU%TEf:RN';f^RO,2B%SN'R,;JPLf?S0312BH%0@#0#9#0#0#P'Mg00nBR@%KI%G@3FCDf@R@,ELg00o7,6B9:CDfZRPf>S04,6B5:CRQfiRRfhRSfgRTffRUfbRVfaRWfXRXfWRYfVRZfUR[fTR\fSR]fRR^fQR_fPR`fORafJRbfIRcflRdfHRefGRffFRgfkRhfERifDRjfCRkf3RlP8P:P1MN11I57Rm#JRnfmRoPng0101RpfrPfPiPj1@57Rq%LmRrG5S05P5P7P=PlCN,OmRsC4PEfqRtfnRufpS06PAP=O2PlPdP8F7[[^0>^1<^47^65P5P7PdPRP3p6057111110002P8PpPtPgPjPkP:P1G5XU;X[9WHPhfjR9PSP6PmP?P8P2P5P7P?P1PdPhP9PRfeR;fdR3PKPPfYRvPXPYPZP[P\P]P^fMRwfLRxfoRyfKRzPbPcPuPePfPgP:P1P=PlMN1n2001103000120102100g010jR{n10110100021010300X0>X1<X5nS07PTPUP;P3fcR|PVPWf`R}PDPOPHPMPKPPPvPXPYPZP[P\P]P^P_P`PafNR~PwPxPzPbPcPeMO>Pfg011G,6BPg%8CPi%[LFZPpPuPdPkfARBP@PhP9GYPoPnPqPrPRPSQ07PUP;P3P|PVPWP}PDPOPHPMPKPPPvPXPYPZP[P\P]P^P_P`PaP~PwPxPzPbPcPePfPgPiPjPkfBPBP@Q03Q04f=Q02PJPNPIQ01PFPGPAP=PlP8P:P9PRPSPTP|PVPvPXPYPZP[P\P]P^P_P`PzPbPoPcPePfPdPgPiPjPlP8P:P1MN1RjPEPnPuPsP8P6PmP?P8P2P5P7P?P1PtQ06PyPuP9PRP}PDPOPHPMPKPPPvPXPYP^P_ftP`PaP~fsR~PwPxPzP:P1P=PlMN1n2001103000120102100P{n10110100021010300X0>X1<X5nP:PLPdPhP9PRP;P3PKPPPvPXPYPZP[P\P]P^PwPxPyPzPbPcPuPePfPgPAP=PlP1MN1X0>P:P1CVGWW3X0>X1<X47X65OmPnPuPnPpP~PePgPiPqPrG5PsC4PGPAP=PlP8P:P1O6W@X3jX0>X1<X{7Xz5P{PnPoQ05%8mC4PEPtPuPyP=PdPlF7[P1n010000000X?{X0>X1<M?XWAX8QW7WKWCW=WBW<WIW:W;WLWJWDWEXWCX`7Xn7X\7Xp5Xq5W]WXW>XxCXwCXvCXuCXeCXdCXmCXlCXkCXjCXiCXhCXgCXfCXTCXSCXRCXQCXPCXOCXNCXMCXcCXbCXtCXsCXrCXyCXYCXoCW_WFWaW^WVWZXG0W9X24P1O1X24P1O1W2o"). Qed.

(* [comment removed for export] *)
Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 0x3b8a0 ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_I ()) ["CANSEC1"] "p'0h03ms'h12s'h26am_preh31Hh42HBh52HPh62moi002moh71ri011rh83st1i023st1h92AMh:3AUXh;2BLh<3CLOh=2ERh>1Fh?2HLh@1KhA2LOhB2MIhC2MRhD3PREhE1QhF1RhG2R'hH2SThI2TKhJ2TPhK2a0hL2a1hM2a2hN2a3hO2a4hP2a5hQ2a6hR2a7hS2b'hT4bailhU4errvhV2fchW2gphX1khY2k'hZ2loh[1mh\1oh]2rah^1sh_2s0h`2s1ha3s10hb3s11hc2s2hd2s3he2s4hf2s5hg2s6hh2s7hi2s8hj2s9hk2sphl2sthm2t0hn2t1ho2t2hp2t3hq2t4hr2t5hs2t6ht2tphu1xhv1yi031pp%0p;2p;1p;3p;4p;Kp;7p;Op;8p;?p201R0g00;;R1p4p7210p8P0g00<8R2p4p710p8P0g00W[R3p6054111003p8P0g012NR4p4p710p8P0g008PR5p4p710p8g007Ij2^TP2j1ATg00N;j11Tg00N`j19Tg00O>j1>Tg00Oaj10Tg00PFj2MTg00ZZj3ETg00[Uj1DTg00]Rj24Tg00^Tj27Tg00_>j3BTg00`=j4]Tg00`oj1VTg00aej2?Tg00cFj2TTg00ccj1STg00dAj2QTg00d^j1PTg00eSj1OTg00f3j3NTg00fSj4LTg00gIj2KTg013Rj1GTg00h=j2=Tg00hcj3FTg0140lK2Tg00>3R2j2HTg00KZR6j1ITg003\j2JTg005Sj1CTP5j45Tg00M[j4<Tg00M9j2;Tg006Kj48TP1j7:Tg00L^S00j26Tg00j:lORTg00L<j1@Tg00jlj1\Tg00kej7[TP4j4ZTg014oj4WTg00lWj4XTg001[j8YTP3l?UTf0R4#1#1p=3g00S5R1p-0R5[R7p,2rcR8/^4g00:FR9f2R:#A[\1R;f1R<#AR=g00B1R>g00CjR?f4R@g00DcRAP5[\?[g00RPRB#1RC#3#3RD#1#9RE#>RF%0CRC#9/MF%9D#>g00ASf\RDP:O1f3RG=E8@%D@f5RHfYRI'4f7RJfWRK,7E5B8g00mMRLf8RMf6RNfXRO,7EC]%V8/?JfZRP,7Eg015J'T,?MPLf;RQ17EI%3C#0#3#S'Qg00nBRC%PM%OC3NCLf<RC,KLf[RR%0B#0#1#0#0#0#1#3#0#1#0#1#3#3#G,=E5FFP8fcRBfbRSfaRTf`RUPDPRfRRVfQRWfPRXfORYfNRZfMR[fLR\fKR]fJR^fIR_fDR`fCRafARbfeRcf@RdfBRePGP:P<P4MK214@:Rf1H19Rg#IRhfhRiPhPa1J19Rj%CgRkC5P1P9PHP@C<,;gRlC8P8flRmfiRnfkRoPNPHO2P@fgRpPGF:[[[^0A^1?^69^81P1P9ffRqPBP3p6057111110002P:PbP<P4C5XS=XY;WGPcfdR;PSP6PgP5P:P2P1P9P5P4P8PqPcP;PBf_R=f^R3fURrfTRsfSRtPVPWPXPYPZP[P\fGRufFRvP`PiPafERwP<P4P@PGMK214<@Rx'6n2001103000120102100g010jRyn10110100021010300X0AX1?X7hRzPTPUP=P3f]R{PDPRPPPIPOPKfVR|PrPsPtPVPWPXPYPZP[P\P]P^P_fHR}PuPvPwP`PaPeMORPbg016J,=EPd%@Ff?RE%\LF[Pqf>R~PcP;CZPpPhPjPkPBPSPzPUP=P3P{PDPRPPPIPOPKP|PrPsPtPVPWPXPYPZP[P\P]P^P_P}PuPvPwP`PaPePbPdPEP~f=PCPQf:RQf9RCPMPJPNPHP@PGP:P<P8P;PBPSPTP{PDPtPVPWPXPYPZP[P\P]P^PwP`PePqPbPaPGP:P<P4MK2RbP8PhPnPlPGP6PgP5P:P2P1P9P5P4P8PmPofjR5PnPcP;PRPPPIPOPKP|PrPsPtPVP[P\P^fnP_P]P<P4P@PGMK2/6xn2001103000120102100Pyn10110100021010300X0AX1?X7hP:PLP8PpPqPcP;PUP=P|PrPsPtPVPWPXPYPZP[P}PuPwPnP`PvPNPHP@P4MK214N@'6X0AP:P8PqPcP;PBP=P3PrPsPtPVPWPXPYPZP[P\PuPvP`PiPaPwPHP@PGP:MK214HGP<P4CWCXGYX4fW5X0AX1?X69X81Og14G<,6bQ00P8PcP;PBPSP3P{PsPtPVPWPXPYPZP[P\P]PvPwPaPpPeP`P@PGP:P<MK2PfPhPnPhP`PjPkC5PlC8P8fmP5PmPNPHO2P@PiPGF:[P4P8PpPqPcP;PUP=P|PrPsPtPVPWPXPYPZP[P}PuPwPnP`PvPNPHP@PGMK214JHPhPmPhPuPjPkC5P1P9PMPJC<,;gC8PQPCPMPJPNP:P<P4O7W?W4W5P<P4O2n2001000000120000000W3X0AX1?Xv9Xu1PyPhPpPhPePjPkC5%@gC8P8PoPiPnP@PqPGF:[P4n010000000X3yX0AX1?M?UW@WJWBW=WAW<WHW:W;WIWCWDXUFWZXl1X[>WVW>XsFXrFXqFXpFXbFXaFXjFXiFXhFXgFXfFXeFXdFXcFXRFXQFXPFXOFXNFXMFXLFXKFX`FX_FXoFXnFXmFXtFXWFXkFW]WEW^W\WTWXXF0W9X27P4O1X27P4O1W2o"). Qed.
End CANSEC1.
