(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMalloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RAllocSlot_iface () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref@RAllocSlot_iface9RAS_STACKC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition RAS_STACK (sc : Z) : Z := 304 + 144 * Z.max 0 (27 - sc).   (* [comment removed for export] *)

Lemma RAS_STACK_ge sc : 304 <= RAS_STACK sc.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CEIL_WRAP_1"] "h04__p1h14__x1h24__x2h32sch42H0h57__arithh64__ffh78__varmaph85__with92z0p;1p;2p;3p;4p;6p;7p;8g0000j11Tg000Uj10Tg001:j18Tg001Xj2:Tg0025j2`Tg002Wj2DTg0033j2?Tg003Pj32Tg003jj24Tg004Ej27Tg004aj2ATg005;j2;Tg005dj1ETg006Bj2_Tg006cj1<Tg007Bj3UTg007kj39Tg008Tj2CTg009@j2BTg009lj1OTg00:Lj3@Tg00:lj1NTg00;Lj2MTg00;jj1LTg00<Hj4KTg00<fj1JTg00=Dj1ITg00=oj25Tg00>Rj2>Tg00?5j3HTg00?Xj43Tg00@Cj6GTg00@gj7FTg00AKj1PTg00Amj3QTg00BPj3RTg00C3j8STg00CWj2TTg00D9j2^Tg00DSj2]Tg00E?j3\Tg00E^j4VTg00FPj2WTg00Fmj2XTg00GJj1YTg00Hfj7ZTg00IJj7[Tf1R0g00InR1g00JMR2P2g00JmR3f0R4g00KMFZp=6f2R5P1P2P2P3P0P4F[p==g00KmR6g00LKR7g00LiR8#1#0#1#1#8R9/:4R:'`1D7:1?7:R;=26:'417:7A26;7'4'A1:90R;,?7P6p-0R:g00MNR<g00N:R=,;6R>%E8,_6%<=#<R=,;65U6R?996>g00NYR@'C'B%<=,;6=96?996>/C@,B>%O<5@<3@%N<P61M65P0%L6CK%J6%I6R<P1P2P2P3P<P1P2P2P3P61567R>g00OE1569%08R@,>65H6R?C3,6<P61>68R8g00OlR=P?C3,6<5=<P<P1P2P2P3f4EGP6P8P=P>C3,6<5=<FF%P2P6%0@#1R@#1#0#0#0#0#8R2,56R>g00PS%0@#0#0#0#8R@,56=Q689R6>C3,6<GS1T<3P4P5g00Q:R<g00QZR3'^1]45=2<3dA\670CVb6b7b8X16X26W01D7;A264;'4A2647,45'A1W@0,X2,72[^16^26^0:P4f3R:,:9/77P:P0P5O4b5b9b4%Y4,72eX36P4O1W3o"). Qed.
Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4192.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CEIL_WRAP_1"] "h04__p1h14__p2h24__x1h34__x2h42sch52H0h67__arithh74__ffh88__varmaph95__with:2z0p;2p;1p;3p;4p;7p;6p;8g004Ej23Tg0000j10Tg000Uj12Tg001:j19Tg001Xj2<Tg0025j2WTg002Wj2CTg0033j2ATg003Pj34Tg003jj28Tg004aj2@Tg005;j2;Tg006cj1:Tg007kj3=Tg008Tj2GTg009@j2FTg009lj1VTg00:Lj3DTg00:lj1UTg00;Lj2RTg00;jj1QTg00<Hj4PTg00<fj1NTg00=Dj1MTg00>Rj2?Tg00=oj25Tg00?5j3LTg00?Xj46Tg00@gj7KTg00AKj1JTg00Amj3ITg00BPj3OTg00CWj2HTg00D9j2STg00DSj2TTg00E?j3`Tg00E^j4_Tg00FPj2^Tg00Fmj2]Tg00GJj1\Tg00@Cj6YTg00Hfj7XTg00IJj7ZTg00C3j8[Tf1R0g00InR1g00JMR2P2g00JmR3f0R4EYp=EP0P1P2P2P3P4g00KMFXp=7f2R5P1P2P2P3P0P4FZp=>%24#2p=1f3R6P1P2P2P3P5P0P4G[p=Bg00KmR7g00LKR8/34R9g00LiR:#0#2#0#0#9R;/<0R<,W81C8<1A8<R==47<'813<8A47=8'8'@1<;5,A8P7p-0R=g00MNR>g00N:R?,;7R@%:?#:R?#:,;7RA9=7@g00NYRB'G'F1;7?9=7A9=7@/GB,F@%V>5D>3D%U>P71R75P0%Q7CP%N7%M7R>P>P1P2P2P3f4R1,E>P71?7:R@g00OlRB157;%2:R:,?7RA5L7C6,7>5>>f5,E>P7P@PB1578RBC6,7>5>>FK%J2R2P>P7PBg00PSRBPAC6,7>P2P7%2:R:#0R2#0#1#1#9RA,57%12#1#9R2,57=I7@5O7PB%2:#1#0#0#2#1#1#9R:,57C6,7>CBCB1H>3P4P5g00Q:R>g00QZR3'S1T45=4>3dA`780C_b7b8b9X27X37X0=W1A474<,85A4748,86'@13851^25,]A/3:[[^27^37^0=^1=P41<;1R;/381C8;P1P0P5P6O6b6b:b5U%\0/3:\9eX47P4O1W4o"). Qed.
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CEIL_WRAP_1"] "h04__p1h14__x1h24__x2h34__x3h44__x4h51ah61bh72H0h82H1h97__arithh:4__ffh;8__varmaph<5__with=2z0h>2z1p;2p;1p;3p;4p;6p;7p;8g004Ej24Tg0000j17Tg000Uj10Tg001:j1CTg001Xj2;Tg0025j2PTg002Wj2MTg0033j2ETg003Pj36Tg003jj23Tg004aj2ATg005;j25Tg006cj18Tg005dj1eTg006Bj2^Tg007Bj3\Tg008Tj2?Tg009@j2FTg009lj1YTg00:Lj3<Tg00:lj1XTg00;Lj2LTg00;jj1WTg00<Hj4KTg00<fj1VTg00=Dj1UTg00=oj29Tg00>Rj2=Tg00?5j3ITg00?Xj4>Tg00@Cj6TTg00AKj1STg00Amj3JTg00BPj3RTg00CWj2fTg00D9j2dTg00DSj2cTg00E?j3bTg00E^j4]Tg00FPj2QTg00Fmj2NTg00GJj1OTg007kj3[Tg00Hfj7_Tg00IJj7ZTg00@gj7`Tg00C3j8aTg00KmR0f0R1g00LKR236p=:f1R3=[01p=1P3g00InR4g00JMR5P5g00JmR6P1g00KMF_p=2P0P3g00OlP1C>p=Bf2R7P4P5P5P6P3P1FZp=@P7P4P5P5P6P3P1F`p=HP0P3g00PSP1C>p=Df3R8P4P5P5P6P7P3P1Gap=G1431R9g00LiR:#7R;#0#7#7#CR</;7R=,P21M2=1E2=R>=60='314=2%:>'3'A1;<8R>,E2R=P01P2>1M2>R?A60=>'314>2R@%:='3'Af4R=,;<,E2P0p-0RAg00MNRBg00N:RC,50RD%8CRC#8RE#8RF#8RG#8,50RH%e:,^0150FRF5\0RI'1,1Dg00NYRJ'?'F150G/1I,1H,1D/?J,FD150E,1I,1H,1D/?J,FD150C,1F,1H/?J%YB5<B5<B5<B3<%XBP0P01L0=P7%W0CKP31L08CK%V0%U0RBP01902RJg00OERH190<RF%0:RC#0RD,=0RI5I0REC>,2B1=0:R:/BE,2B5@BPBP4P5P5P6f6R4ET1B:J,2B5@B5HB%S5R5PBP0PJPH1=0;R;9I0FRFC>,2B1=0CRC/BF,2B5@B1DFJ,2B1BCJ,2B5@B5HBP5PB1D;I,2BP5%7DRD#7#0#0#0#0#CR5,90R;%0D#0#0#0#CRD,90RI=J0:5R0AJ0IC9R0;'D,2BCGCGCG1fB6P1P7g00Q:RBg00QZR6'd1c17=6B6dAb023C]b:b;b<X10X20X30X40W0A601>,3?%:1,3='AA607>,3?%:7,3@'Af5R@,4=1QD8,N51QD=,N5'4[[[^10^20^30^40^0AP11;<4/42P4f7P8P3P7P=P@O8b9b>b8b=b7U%O3%O7'4\9eX60X50P3P1O2X60X50o"). Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof.
ltac2:(KReplay.run1 (kr_t_RAllocSlot_iface ()) ["CEIL_WRAP_1"] "h04__p1h14__p2h24__p3h34__x1h44__x2h54__x3h64__x4h71jh82sch92H1h:2H2h;7__arithh<4__ffh=8__varmaph>5__with?2z1h@2z2p;2p;1p;3p;4p;7p;6p;8g002Wj26Tg0000j1;Tg000Uj10Tg001:j1=Tg004Ej24Tg001Xj2BTg0025j2NTg0033j2GTg003Pj35Tg003jj22Tg004aj2?Tg005;j23Tg006cj18Tg005dj1cTg006Bj2\Tg007Bj3[Tg007kj3:Tg008Tj2OTg009@j2XTg009lj1WTg00:Lj3MTg00:lj1VTg00;Lj2LTg00;jj1UTg00<Hj4KTg00<fj1TTg00=Dj1STg00=oj27Tg00>Rj2>Tg00?5j3JTg00?Xj49Tg00AKj1RTg00Amj3HTg00BPj3FTg00CWj2eTg00D9j2dTg00DSj2bTg00E?j3aTg00E^j4_Tg00FPj2PTg00Fmj2ATg00GJj1QTg00Hfj7ZTg00IJj7]Tg00@Cj6^Tg00@gj7YTg00C3j8`Tg00KmR0f0R1g00LKR235p=<f1R3g00InR4g00JMR5P5g00JmR6P1g00KMFZp=1f2R7P4P5P5P6P3P1F]p=@P0P3g00PSP1C9p=CP3P4P5P5P6P1E^p=EP7P4P5P5P6P3P1FYp=If3R8P4P5P5P6P7P3P1G`p=D1631R4g00LiR9#;R:#0#;R;#0#=R<,43R=%;;#=R;/B8R>,N2162>R?1G2>R@=50>'214>2RA%<@'2'?f4R@,B;RB,G2RCP01N2B162BA50CB'214B2%<C'2'?f5RC,B;,G2P0p-0RBg00MNRDg00N:RE,30RF%8ERE#8RG#8RH#8RI#8,30%c9,\0130I5[0130GRG5:05:09:0Fg00NYRF'O'X130H130E5:09:0G/OF%WD5MD3M%VDP0P01L0@P7%U0CKP31L08CK%T0%S0RDP01702RFg00OERG170;RE%09RH#0RI,>0RJ5J0RKC9,1DP01>09R9g00OlRLPKC9,1D5@D1CKF,1Df6RK,ED5@D5ID%R5R5PDf7RM,EDP01>0HRHPL1>0:R:9J0EREC9,1D5@D1CEF,1Df8RE,ED5@D5IDP5PD170<,CJ,1DP5PDP0P:PGPJC9,1DP5%;IRI#;#0#0#0#0#=R5,70RJ%0I#0#0#0#=RI,70RG=H095F0=F0GAH0GH9F0J'C,1DCDCDCDCD1eD6P1P7g00Q:RDg00QZR6'd1b17=5D6dAa023C_b<b=b>X30X40X50X60X0BX1BW2A501>,2?12A@'?A507>,2K12AM'?14C<16CK1PI@,A5/AI1PIC,A5'4[[[[^30^40^50^60^0B^1B^2BP1%<81B;E,62%<3PMPEP8P3P7P@PCPKO;b;b@b:b?b9UU%Q7/AI%Q8'4\=\4eX70X80P3P1O2X70X80o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
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
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
End CEIL_WRAP_1.


