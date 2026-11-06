(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel AsanCeil VmLedger.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AllocCredit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc69OSSVerify5KrLib6Common8Mallocng;AllocCredit:alloc_costC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c69OSSVerify5KrLib6Common8Mallocng;AllocCredit=alloc_cost_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz03C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng;AllocCredit=alloc_cost_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib6Common8Mallocng;AllocCredit<ROOM_CREDMAXC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_cost (n : Z) : Z := Z.max 8448 (2 * n + 8300).

Lemma alloc_cost_small : forall n, n <= 74 -> alloc_cost n = 8448.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocCredit ()) [] "h04__p1h14__x1h24__x2h31Hh42H0h57__arithh64__ffh78__varmaph85__with91nh:2z0p;1p;2p;3p;4p;6p;7p;8g0000j12Tg000Uj11Tg001:j18Tg001Xj25Tg0024j2ATg002Qj2<Tg002nj2STg003Pj2PTg003lj2CTg004Ij2:Tg004dj2FTg005>j1aTg005\j2]Tg006=j1;Tg006\j24Tg007Ej3VTg007nj3@Tg008Wj2?Tg009Cj2=Tg009oj1UTg00:Oj3>Tg00:oj1RTg00;Oj2QTg00;mj1OTg00<Kj4NTg00<ij1MTg00=Gj1LTg00>2j27Tg00>Uj2BTg00?8j3KTg00?[j3JTg00@>j49Tg00@ij6ITg00AMj7HTg00B1j1TTg00BSj2`Tg00C5j2_Tg00COj2^Tg00D;j3GTg00DUj3\Tg00E4j4YTg00Efj1XTg00G1j7ZTg00GUj7[Tg00H9j8WTf0R0#2#2p=0g00H]R1f1R2;G0p=3P2g00I;R3g00IZR4P4g00J:R5P0g00JZFZp=6f2R6P3P4P4P5P2P0F[p=Df3R7P3P4P4P5P6P2P0GWp=Eg00K:R8#2R9#2R:#1#2#1#2#8R;,50%0:R:#1#0#0#0#0#8R<%89R=/A2%0:#1#1#2#1#1#0#8R:'<R>'S1P<>R?1C<>R@/3>':15><13@<':'F1A=6/<:,C<P1p-0R@g00K_RA%a8,]1g00LKRB#;RC#;RD,41RE5V1141BRB5@1RFg00LjRG'?%;DRD#;,41141C=@1B/?G'=,=F141DA@1BE/?G'=%UA5>A5>A3>%RAP11Q16P2%O1CN%M1%L1RAPAP3P4P4P5P1171<RGg00MV171=1B19R95K1171:5J1RBC9,6AP11B18R8g00N=REPBC9,6A5DAPAP3P4P4P5f4R3EIP1P8PEPGC9,6ARG5DAFH%T4R4PAP1P9g00Nd171;C9,6AP4PGCECE1`A5P0P6g00OKRAg00OkR5'_1^06=GA5dg00PK=\12CYb6b7b8X11X21W0130>,:?130<,:6'F156;136<[[^11^21^0@P01A=3/<:/5<P3P2P6P7O5b5b:b4%X2/3<eW3X91o"). Qed.
Lemma alloc_cost_le : forall n, 0 <= n -> alloc_cost n <= 2 * n + 8448.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocCredit ()) [] "h04__p1h14__p2h24__x1h34__x2h41Hh52H0h67__arithh74__ffh88__varmaph95__with:1nh;2z0p;2p;1p;3p;4p;7p;6p;8g001Xj21Tg0000j12Tg000Uj14Tg001:j1;Tg0024j29Tg002Qj23Tg002nj2OTg003Pj2?Tg003lj2<Tg00D;j35Tg004Ij28Tg004dj2CTg006=j1FTg006\j2ETg007nj3DTg008Wj2WTg009Cj2VTg009oj1UTg00:Oj3RTg00:oj1QTg00;Oj2PTg00;mj1NTg00<Kj4MTg00<ij1LTg00=Gj1KTg00>Uj2@Tg00>2j27Tg00?8j3JTg00?[j3ATg00@>j46Tg00AMj7ITg00B1j1HTg00BSj2GTg00C5j2STg00COj2TTg00DUj3^Tg00E4j4]Tg00Efj1\Tg00@ij6[Tg00G1j7ZTg00GUj7YTg00H9j8XTf0R0#2#2p=0f1R1g00I;R2g00IZR3P3g00J:R4P0E[p==P1P2P3P3P4P0g00JZFZp=:f2R5P2P3P3P4P1P0FYp=>f3R6P2P3P3P4P5P1P0GXp=Bg00H]R7g00PKR8/10g00K:R9#2R:#2#0R;#4#0#0#0#0#;R<%;:R=/91R>%0;#4#4#2#4#4#0#;R;'3R?'O1?<?1<<?R@=57?'811?<A57@<'8'C19=5/3;,<<P7p-0R@g00K_RAg00LKRB#F#F,E7RC1E7BRB5D7AD7BCg00Lj'W'V%UA3R%QAP71P75P1%N7CM%L7%K7RAPAP2P3P3P4f4R2,=AP71@79R9g00N=RB177=1@7:R:5J7RC177;5A7C6,:A5>Af5,=AP7P9PB177<RBC6,:A5>AFI%H3R3PAP71778g00NdRDP:C6,:AP3P7P9PDAA7CBC6,:ACBCB1GA4P0P5g00OKRAg00OkR4'S1T05=5A4dA^781C]b7b8b9X27X37X0@W1A570?,85A570<,86'C118519=6/3<,15[[^27^37^0@^1@P019=2/3;R;/1<1?<;P2P1P5P6O6b6b;b5%\113><'1eW4W:o"). Qed.
Lemma alloc_cost_ge : forall n, 8448 <= alloc_cost n /\ 2 * n + 8300 <= alloc_cost n.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocCredit ()) [] "h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with71nh82z0p;1p;2p;3p;4p;7p;8g0000j16Tg000Uj15Tg001:j1:Tg0024j2CTg002Qj2>Tg002nj2TTg003Pj2FTg003lj2ETg00D;j34Tg004Ij21Tg001Xj22Tg004dj2GTg005>j1aTg005\j2]Tg006=j1ATg006\j2BTg007Ej3UTg007nj3?Tg008Wj2=Tg00Pij2STg00QRj3RTg009Cj2<Tg009oj1QTg00:Oj38Tg00:oj1PTg00;Oj2OTg00;mj1NTg00<Kj4MTg00<ij1LTg00=Gj1KTg00>2j2;Tg00>Uj2DTg00?8j3JTg00?[j3ITg00@>j47Tg00AMj7HTg00B1j1`Tg00H9j8_Tg00BSj2^Tg00C5j2\Tg00COj2YTg00DUj3XTg00E4j4WTg00Efj1ZTg00G1j7[Tg00GUj7VTf0R0#6#6p=0f1R1g00I;R2g00IZR3P3g00J:R4P0g00JZF[p=3f2R5P2P3P3P4P1P0FVp=9g00H]R6P1g00NdP0C7p=@g00K:R7#6R8#6#0R9#5#0#0#0#0#:R:%:8R;/C0%09#5#5#6#5#5#0#:R9'>R<'T1F:<1E:<R==46<'112<:A46=:'1'G1C;1/>9R=,E:P6g00K_R>%a7,]6g00LKR?#AR@,B6RA5U61B6?R?5?6RBg00LjRC'=RD1S6;=R6?%A@#A,B6R@5?6/=C,<BA?6A?/=C,<@,<B%Q>58>98>D58>38%P>P61O65P1%N6CM%L6%K6R>P2P3P3P4P>P2P3P3P4P61;6:R2g00MV1;6;1D685J61;695I6R8C7,3>P61D67R7g00N=RDP8C7,3>59>1@82,3>P6P7PDP2C7,3>59>FH%`31@27,3>1@87,3>59>G_1^>4P0P5g00OKR>g00OkR4'\1Y05=4>4dg00PK=X61CWb4b5b6X06X161F:=A460='112=:A460:'1'G12:11C;5/>9/21'1[^06^16P0f3P1P5O3b3b8b2%Z0R0,2:12<0'1eX76o"). Qed.
Lemma alloc_cost_mono : forall n n', n <= n' -> alloc_cost n <= alloc_cost n'.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocCredit ()) [] "h04__p1h14__x1h24__x2h34__x3h44__x4h51Hh62H0h72H1h87__arithh94__ffh:8__varmaph;5__with<1nh=2n'h>2z0h?2z1p;2p;1p;3p;4p;6p;7p;8g001Xj23Tg0000j18Tg000Uj15Tg001:j1HTg0024j29Tg002Qj2:Tg002nj2NTg003Pj2ETg003lj2=Tg004dj2<Tg006=j16Tg006\j27Tg005>j1fTg005\j2`Tg007Ej3\Tg008Wj2BTg009Cj2@Tg00Pij2XTg00QRj3OTg009oj1WTg00:Oj3?Tg00:oj1VTg00;Oj2MTg00;mj1UTg00<Kj4LTg00<ij1TTg00=Gj1STg00>2j2DTg00>Uj2;Tg00?8j3KTg00?[j3JTg00@>j4CTg00@ij6RTg00B1j1gTg00BSj2eTg00C5j2dTg00COj2cTg00D;j3QTg00DUj3_Tg00E4j4]Tg00Efj1PTg004Ij2[Tg007nj3^Tg00G1j7ZTg00GUj7aTg00AMj7bTg00H9j8YTf0R0#8#8p=2f2R1g00H]R2f1R3;Q0'[p=1A^230p=4P3g00I;R4g00IZR5P5g00J:R6P0g00JZFZp=0P2P3g00N=P0CCp=AP1P4P5P5P6P3P0Fap=>P1P4P5P5P6P3P0Fbp=IP2P3g00NdP0CCp=Gf3R7P4P5P5P6P1P3P0GYp=F1330g00K:R8#8R9#8R:#2R;#5#2#2#2#2#HR<%H9R=/93%2;#5#5#8#5#5#2#HR;':R>'N1E<>1=<>R?;1>13><?1?<'<19=1/:;R?,=<P2f4R>,9=/:;R@,N<1E<@RA1=<@RB;1@13@<RC?1B<'<f5RB,9=/:;,=<P2p-0RDg00K_REg00LKRF#6RG#6RH#6#6RI,72RJ%f8,`2172HRH5\2172FRF'4'4RKg00LjRL'B172G/4F/BL,@J,@K14FH/BL,@K%6I,721X2=RI=O2FAO2IH,4J'4/BL'@%WE5?E5?E5?E3?%VEP2P21M2>P1%U2CLP31M27CL%T2%S2REP21D2<RLg00MVRJ1D2=RI%58,;2RH5K21D2;RF5J2RKCC,0E1;28R8/AK,0E5>EPEP4P5P5P6f6R4ER1A8L,0E5>E5IE%g5R5PEP2PLPJ1;2:R:9K2I=J2FRFCC,0E1;29R9/AF,0E5>E1GFL,0E1A9L,0E5>E5IEP5PE1GH:,0EP51G89,0ECFCFCF1eE6P0P1g00OKREg00OkR6'd1c01=QE6dg00PK=_23C]b9b:b;X12X22X32X42W01E<??10?A1>0<'<A1A1@A1C1<'<13>B137>[[[^12^22^32^42^0DP0f7R0,9=/:;/3<P4P0P7P3P1P>PBO8b8b?b7b>b6%P1%P3'3eW5X=2X<2o"). Qed.
(* [comment removed for export] *)
Lemma alloc_cost_sum : forall n i, 0 <= n -> 0 <= i -> i * alloc_cost n <= 2 * (i * n) + i * 8448.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocCredit ()) [] "h04__x1h14__x2h24__x3h31Hh42Hih52Hnh67__arithh74__ffh88__varmaph95__with:1ih;1np;2p;1p;3p;4p;7p;8g001Xj23Tg00R;j2WTg00Efj1>Tg0000j14Tg001:j16Tg0024j20Tg000Uj1=Tg002Qj2;Tg005\j2GTg00SIj2FTg006\j27Tg00QRj3ATg006=j1BTg007nj3VTg008Wj2UTg009oj1RTg00:Oj3QTg00:oj1NTg00;Oj2?Tg00<Kj4KTg00<ij1JTg00=Gj1HTg00>Uj25Tg00>2j28Tg00?8j31Tg00?[j3<Tg00B1j1ITg00BSj2ETg00C5j2LTg00COj2MTg00D;j3DTg00DUj3OTg00E4j4PTg00@>j4CTg00G1j7STg00H9j8TTf0R0#4#4p=2g00H]R1f1R2g00NdP0CCp=:P2g00I;R3g00IZR4P4g00J:R5P0g00JZFSp=9f3R6P3P4P4P5f2R3P2P0GTp=@g00PKR7/32R81W62%>6g00K:R9#4R:#6R;/06%4:#2#=#2#2#2#2#6R<';'3g00K_R=%69,G1,F1g00LKR>,715A1%B>R>,71%B>,715A15V1g00Lj'U%R=3Q%N=P11?13P21?16CK%J1%H1R=151:R:181;R>%=9,51R?511181<R@5<1':,9=%I4R4P=18171519R9':,9=P4A119:A119?911>A119@5<1':,9=C@C@1E=5P0P3g00OKR=g00OkR5'L1M03=D=5dAO172CPb7b8b9X01X11X2110;3/;<,321036f4R6,03,0;103<';'3\8[^01^11^21P0f5R0%>0P6P2P3O5b6b3X48W5X:1X;1o"). Qed.

(* [comment removed for export] *)
Definition ROOM_CREDMAX : Z := 48 * 2^20 + 8200.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {AL : AllocLayout} {CL : CallocLayout}.

Class AllocCredit := {
  acr_sure :: AllocSure;

  (* [comment removed for export] *)
  aroomP : AS -> VmMaps -> Z -> Z -> Prop;
  aroomP_mono : forall A h k p k' p',
      aroomP A h k p -> 0 <= k' <= k -> p' <= p -> aroomP A h k' p';
  aroomP_of_aroom : forall A h k b, aroom A h k b -> aroomP A h k b;
  aroom_of_aroomP : forall A h k p,
      aroomP A h k p -> ROOM_CREDMAX <= p -> aroom A h k (p - ROOM_CREDMAX);

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_malloc_p : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some n /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None)) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k p, aroomP A (m_vmmaps md) k p -> 1 <= k -> alloc_margin n + ROOM_CREDMAX <= p ->
                       aroomP A' vm' (k - 1) (p - alloc_cost n)) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_calloc_p : forall (fx : FPState) A m md regs (cnt sz : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some (cnt * sz) /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 (cnt * sz) -> owned A (at_ res i) \/ m (at_ res i) = None) /\
                (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0))) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k p, aroomP A (m_vmmaps md) k p -> 1 <= k -> alloc_margin (cnt * sz) + ROOM_CREDMAX <= p ->
                       aroomP A' vm' (k - 1) (p - alloc_cost (cnt * sz))) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_malloc_psure : forall (fx : FPState) A m md regs (n k p : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      (* [comment removed for export] *)
      aroomP A (m_vmmaps md) k p -> 1 <= k -> alloc_margin n + ROOM_CREDMAX <= p -> n <= ROOM_NMAX ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          bv_unsigned res <> 0 -> live A res = None -> live A' res = Some n ->
          (forall q, q <> res -> live A' q = live A q) ->
          (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          aroomP A' vm' (k - 1) (p - alloc_cost n) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_calloc_psure : forall (fx : FPState) A m md regs (cnt sz k p : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      (* [comment removed for export] *)
      aroomP A (m_vmmaps md) k p -> 1 <= k -> alloc_margin (cnt * sz) + ROOM_CREDMAX <= p -> cnt * sz <= ROOM_NMAX ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          bv_unsigned res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) ->
          (forall q, q <> res -> live A' q = live A q) ->
          (forall i, 0 <= i < round16 (cnt * sz) -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          aroomP A' vm' (k - 1) (p - alloc_cost (cnt * sz)) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S
}.

(* [comment removed for export] *)
Lemma aroomP_loop_ok : forall n i tot p, 0 <= n -> 0 <= i < tot ->
  tot * alloc_cost n + alloc_margin n + ROOM_CREDMAX <= p ->
  alloc_margin n + ROOM_CREDMAX <= p - i * alloc_cost n.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocCredit ()) ["WithLayout"] "h01Hh14__x1h24__x2h34__x3h44__x4h54__x5h64__x6h72H0h82Hch92Hih:2Hnh;2Hph<2_Hh=7__arithh>4__ffh?8__varmaph@5__withA1ihB1nhC1phD3totp;2p;1p;4p;3p;7p;8g001Xj23Tg003Pj2>Tg004IR0j2ITg00Efj14Tg0024j22Tg00T2j1=Tg002Qj2ATg00U=j1TTg0000j1:Tg000Uj10Tg001:j19Tg00VKj2FTg005\j2LTg00Vhj4YTg00WIj3XTg00SIj2KTg006=j1BTg006\j2<Tg00Pij2JTg008Wj2VTg009oj1UTg00:Oj3STg00:oj1RTg00;Oj2ETg00;mj1QTg00<Kj4?Tg00<ij1PTg00=Gj1OTg00>2j2NTg00>Uj27Tg00B1j1MTg00?8j3GTg00?[j3@Tg00@>j4HTg00Wjj3cTg00BSj2bTg00C5j2aTg00COj2`Tg00D;j3_Tg00DUj3ZTg00E4j4[Tg00QRj3\Tg007nj3WTg00G1j7]Tg00H9j8^Tf2R1f1R2'Af0R3'3p=5%:3#:p=6g00H]R4?\23p=1AW423p=8P4P2g00NdP3CHp=CP2g00I;R5g00IZR6P6g00J:R7P3g00JZF]p=;f3R8P5P6P6P7P1P2P3G^p=Dg00PKR5/38R91>81,I9f5R9#4,28%=9'Ag00XMR:;51f6R;#Tg00K:R<#:R=#:R>#6R?#0#6#6#6#6R@#9RA%4;RB'3%9=RC/2;%6?#0#0#:#0#0#6#9R?;5B'IP0f7RB#4RD,3A12CB?5?Df8RD#=%4D,2B,F975:P3f9RD#4,3Af:RE,2C%4E75?P0135E1>EDf<R0#=f;%40'2,FD75:P;1350f=RD/>0g00K_R0P4%9<,L4R?P<1L45CY9X4>,K4g00LKRC#BRF,<4'1%0@#9,J41K4?R?%BFRF#B,<4R@'1'11J4ARG1<4FRF,1?'111@@11@F1<4CRC,1@11GC'8'8'8'8'8'8g00Lj'V%U03S%R0P4P4f4R0,E4P1%Q4C?P2P41E49P81E4;C?C?%P4%O4RC1N4A%0=,74RG'C,;C%M6R6PC%0<R@#0,74RF=G4G174<R<5@4174=R=5@4174@R@'C,;CP6PCP4174>R>g00MVPFCH,;CP6A@4<=AG4>G9c4@'C,;CCDCDCD1bC7P3P1g00OKRCg00OkR7'a1`31=_C7dAZ452C[b>b?b@X14X24X34X44X54X6413A012;9/A2?5181>9B12;B,F99580[[[^14^24^34^44^54^64P3f>f@R0#4f?PDP:%=0P;PEP2O9b=W7W0P2P3O2n2001000000121000000W<W8P2P3O2n2001000000121000000b0W;W9W:XC4XD4XA4XB4o"). Qed.

End WithLayout.
