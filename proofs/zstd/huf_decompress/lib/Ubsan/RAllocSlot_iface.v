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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_fp.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RAllocSlot_iface () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addc5ARocqVerifyHarness?AgentSubmission5Ubsan@RAllocSlot_iface9RAS_STACKK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CANSEC1"] "h02sch14__p1h24__x1h34__x2h42H0h57__arithh64__ffh78__varmaph85__with92z0p;1p;2p;3p;4p;6p;7p;8g0000j16Tg000Uj10Tg001:j18Tg001Xj2:Tg0025j2`Tg002Wj2DTg0033j2?Tg003Pj31Tg003jj23Tg004Ej27Tg004aj2ATg005;j2;Tg005dj1ETg006Bj2_Tg006cj1<Tg007Bj3UTg007kj39Tg008Tj2CTg009@j2BTg009lj1OTg00:Lj3@Tg00:lj1NTg00;Lj2MTg00;jj1LTg00<Hj4KTg00<fj1JTg00=Dj1ITg00=oj25Tg00>Rj2>Tg00?5j3HTg00?Xj42Tg00@Cj6GTg00@gj7FTg00AKj1PTg00Amj3QTg00BPj3RTg00C3j8STg00CWj2TTg00D9j2^Tg00DSj2]Tg00E?j3\Tg00E^j4VTg00FPj2WTg00Fmj2XTg00GJj1YTg00HOj7ZTg00I3j7[Tf1R0g00IWR1g00J6R2P2g00JVR3f0R4g00K6FZp=4f2R5P1P2P2P3P0P4F[p==g00KVR6g00L4R7g00LRR8#6#0#6#6#8R9/:4R:'`1D7:1?7:R;=16:'317:7A16;7'3'A1:90R;,?7P6p-0R:g00M7R<g00McR=,;6R>%E8,_6%<=#<R=,;65U6R?996>g00NBR@'C'B%<=,;6=96?996>/C@,B>%O<5@<3@%N<P61M65P0%L6CK%J6%I6R<P1P2P2P3P<P1P2P2P3P61567R>g00Nn1569%08R@,>65H6R?C2,4<P61>68R8g00OUR=P?C2,4<5=<P<P1P2P2P3f4EGP6P8P=P>C2,4<5=<FF%P2P6%0@#6#0#0#0#0R@#0#8R2,56R>g00P<%8@R@,56=Q689R6>C2,4<GS1T<3P4P5g00PcR<g00QCR3'^1]45=1<3dA\670CVb6b7b8X26X36W11D7;A164;'3A1647,35'A1W@0,X2,72[^26^36^1:P4f3R:,:9/77P:P0P5O4b5b9b4%Y4,72eX06P4O1X06P4O1W0o"). Qed.
Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CANSEC1"] "h02sch14__p1h24__p2h34__x1h44__x2h52H0h67__arithh74__ffh88__varmaph95__with:2z0p;2p;1p;3p;4p;7p;6p;8g004Ej21Tg0000j12Tg000Uj10Tg001:j19Tg001Xj2<Tg0025j2WTg002Wj2CTg0033j2ATg003Pj34Tg003jj28Tg004aj2@Tg005;j2;Tg006cj1:Tg007kj3=Tg008Tj2GTg009@j2FTg009lj1VTg00:Lj3DTg00:lj1UTg00;Lj2RTg00;jj1QTg00<Hj4PTg00<fj1NTg00=Dj1MTg00>Rj2?Tg00=oj25Tg00?5j3LTg00?Xj46Tg00@gj7KTg00AKj1JTg00Amj3ITg00BPj3OTg00CWj2HTg00D9j2STg00DSj2TTg00E?j3`Tg00E^j4_Tg00FPj2^Tg00Fmj2]Tg00GJj1\Tg00@Cj6YTg00HOj7XTg00I3j7ZTg00C3j8[Tf1R0g00IWR1g00J6R2P2g00JVR3f0R4EYp=EP0P1P2P2P3P4g00K6FXp=7f2R5P1P2P2P3P0P4FZp=>%04#0p=3f3R6P1P2P2P3P5P0P4G[p=Bg00KVR7g00L4R8/14R9g00LRR:#2#0#2#2#9R;/<0R<,W81C8<1A8<R==47<'811<8A47=8'8'@1<;5,A8P7p-0R=g00M7R>g00McR?,;7R@%:?#:R?#:,;7RA9=7@g00NBRB'G'F1;7?9=7A9=7@/GB,F@%V>5D>3D%U>P71R75P0%Q7CP%N7%M7R>P>P1P2P2P3f4R1,E>P71?7:R@g00OURB157;%0:R:,?7RA5L7C6,7>5>>f5,E>P7P@PB1578RBC6,7>5>>FK%J2R2P>P7PBg00P<RBPAC6,7>P2P7%0:R:#2#3#3R2#0#9RA,57%92R2,57=I7@5O7PB%0:#3#2#0#2#3#3#9R:,57C6,7>CBCB1H>3P4P5g00PcR>g00QCR3'S1T45=4>3dA`780C_b7b8b9X37X47X1=W2A474<,85A4748,86'@11851^25,]A/1:[[^37^47^1=^2=P41<;1R;/181C8;P1P0P5P6O6b6b:b5U%\0/1:\9eX07P4O1X07P4O1W0o"). Qed.
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CANSEC1"] "h01ah11bh24__p1h34__x1h44__x2h54__x3h64__x4h72H0h82H1h97__arithh:4__ffh;8__varmaph<5__with=2z0h>2z1p;2p;1p;3p;4p;6p;7p;8g004Ej24Tg0000j19Tg000Uj12Tg001:j1CTg001Xj2;Tg0025j2PTg002Wj2MTg0033j2ETg003Pj36Tg003jj23Tg004aj2ATg005;j25Tg006cj17Tg005dj1eTg006Bj2^Tg007Bj3\Tg008Tj2?Tg009@j2FTg009lj1YTg00:Lj3<Tg00:lj1XTg00;Lj2LTg00;jj1WTg00<Hj4KTg00<fj1VTg00=Dj1UTg00=oj28Tg00>Rj2=Tg00?5j3ITg00?Xj4>Tg00@Cj6TTg00AKj1STg00Amj3JTg00BPj3RTg00CWj2fTg00D9j2dTg00DSj2cTg00E?j3bTg00E^j4]Tg00FPj2QTg00Fmj2NTg00GJj1OTg007kj3[Tg00HOj7_Tg00I3j7ZTg00@gj7`Tg00C3j8aTg00KVR0f0R1g00L4R236p=:f1R3=[01p=0P3g00IWR4g00J6R5P5g00JVR6P1g00K6F_p=1P0P3g00OUP1C>p=Bf2R7P4P5P5P6P3P1FZp=@P7P4P5P5P6P3P1F`p=HP0P3g00P<P1C>p=Df3R8P4P5P5P6P7P3P1Gap=G1431R9g00LRR:#9R;#2#9#9#CR</;7R=,P21M2=1E2=R>=60='314=2%:>'3'A1;<8R>,E2R=P01P2>1M2>R?A60=>'314>2R@%:='3'Af4R=,;<,E2P0p-0RAg00M7RBg00McRC,50RD%7CRC#7RE#7RF#7RG#7,50RH%e:,^0150FRF5\0RI'0,0Dg00NBRJ'?'F150G/0I,0H,0D/?J,FD150E,0I,0H,0D/?J,FD150C,0F,0H/?J%YB5<B5<B5<B3<%XBP0P01L0=P7%W0CKP31L08CK%V0%U0RBP01802RJg00NnRH180<RF%2:RC#2RD,=0RI5I0REC>,1B1=0:R:/BE,1B5@BPBP4P5P5P6f6R4ET1B:J,1B5@B5HB%S5R5PBP0PJPH1=0;R;9I0FRFC>,1B1=0CRC/BF,1B5@B1DFJ,1B1BCJ,1B5@B5HBP5PB1D;I,1BP5%9D#2#2#2#2RD#2#CR5,80R;%CDRD,80RI=J0:5R0AJ0IC9R0;'D,1BCGCGCG1fB6P1P7g00PcRBg00QCR6'd1c17=6B6dAb023C]b:b;b<X30X40X50X60W2A601>,3?%:1,3='AA607>,3?%:7,3@'Af5R@,4=1QD8,N51QD=,N5'4[[[^30^40^50^60^2AP11;<4/42P4f7P8P3P7P=P@O8b9b>b8b=b7U%O3%O7'4\9eX10X00P3P1O2X10X00P3P1O2X10X00o"). Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CANSEC1"] "h01jh12sch24__p1h34__p2h44__p3h54__x1h64__x2h74__x3h84__x4h92H1h:2H2h;7__arithh<4__ffh=8__varmaph>5__with?2z1h@2z2p;2p;1p;3p;4p;7p;6p;8g002Wj28Tg0000j1DTg000Uj10Tg001:j1<Tg004Ej24Tg001Xj2BTg0025j2NTg0033j2GTg003Pj35Tg003jj21Tg004aj2>Tg005;j23Tg006cj17Tg005dj1cTg006Bj2\Tg007Bj3[Tg007kj39Tg008Tj2OTg009@j2XTg009lj1WTg00:Lj3MTg00:lj1VTg00;Lj2LTg00;jj1UTg00<Hj4KTg00<fj1TTg00=Dj1STg00=oj26Tg00>Rj2=Tg00?5j3JTg00?Xj4:Tg00AKj1RTg00Amj3HTg00BPj3FTg00CWj2eTg00D9j2dTg00DSj2bTg00E?j3aTg00E^j4_Tg00FPj2PTg00Fmj2@Tg00GJj1QTg00HOj7ZTg00I3j7]Tg00@Cj6^Tg00@gj7YTg00C3j8`Tg00KVR0f0R1g00L4R235p=;f1R3g00IWR4g00J6R5P5g00JVR6P1g00K6FZp=2f2R7P4P5P5P6P3P1F]p=?P0P3g00P<P1C:p=CP3P4P5P5P6P1E^p=EP7P4P5P5P6P3P1FYp=If3R8P4P5P5P6P7P3P1G`p=A1831R4g00LRR9#DR:#0#DR;#0#<R<,43R=%D;#<R;/B8R>,N2182>R?1G2>R@=50>'114>2RA%;@'1'>f4R@,B;RB,G2RCP01N2B182BA50CB'114B2%;C'1'>f5RC,B;,G2P0p-0RBg00M7RDg00McRE,30RF%7ERE#7RG#7RH#7RI#7,30%c9,\0130I5[0130GRG590590990Fg00NBRF'O'X130H130E590990G/OF%WD5MD3M%VDP0P01L0@P7%U0CKP31L08CK%T0%S0RDP01602RFg00NnRG160;RE%09RH#0RI,=0RJ5J0RKC:,2DP01=09R9g00OURLPKC:,2D5?D1CKF,2Df6RK,ED5?D5ID%R5R5PDf7RM,EDP01=0HRHPL1=0:R:9J0EREC:,2D5?D1CEF,2Df8RE,ED5?D5IDP5PD160<,CJ,2DP5PDP0P:PGPJC:,2DP5%DI#0#0#0#0RI#0#<R5,60RJ%<IRI,60RG=H095F0=F0GAH0GH9F0J'C,2DCACACACA1eD6P1P7g00PcRDg00QCR6'd1b17=5D6dAa023C_b<b=b>X50X60X70X80X2BX3BW4A501>,1?11A@'>A507>,1K11AM'>14C<18CK1PI@,@5/@I1PIC,@5'4[[[[^50^60^70^80^2B^3B^4BP1%;81B;E,82%;3PMPEP8P3P7P@PCPKO;b;b@b:b?b9UU%Q7/@I%Q8'4\=\4eX00X10P3P1O2X00X10P3P1O2X00X10o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
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
    /\ as_inv st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              (* [comment removed for export] *)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
  forall (fuel : nat) (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

End CANSEC1.
