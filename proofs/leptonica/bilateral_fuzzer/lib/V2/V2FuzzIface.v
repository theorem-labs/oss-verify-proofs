(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel VmLedger FPSteps.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Room.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2FuzzIface () := "K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c5ARocqVerifyHarness?AgentSubmission2V2;V2FuzzIface:FUZZ_CALLSK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05c5ARocqVerifyHarness?AgentSubmission2V2;V2FuzzIface;fuzz_marginI47Corelib4Init5Logic4True00c5ARocqVerifyHarness?AgentSubmission2V2;V2FuzzIface9FUZZ_BMAXK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Room7room_k0C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Room7room_b0K46Stdlib9micromega7EnvRing5PExpr03C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure9ROOM_KMAXC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure9ROOM_BCAP".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition LEPT_STACK : Z := 16384.          (* [comment removed for export] *)
Definition PC_FUZZ : Z := 0x17d08.           (* [comment removed for export] *)
Definition A_LEPT_SEV : Z := 0x45f08.        (* [comment removed for export] *)
Definition A_LEPT_HANDLER : Z := 0x45f10.    (* [comment removed for export] *)
Definition A_LEPT_PMM : Z := 0x45f18.        (* [comment removed for export] *)
Definition A_EMPTY : Z := 0x56180.           (* [comment removed for export] *)
Definition A_GOT_LO : Z := 0x44e40.          (* [comment removed for export] *)
Definition A_GOT_HI : Z := 0x44ee0.

(* [comment removed for export] *)
Definition FUZZ_CALLS : Z := 1024.
Definition fuzz_margin (size : Z) : Z := 2^31 - 2^26.      (* [comment removed for export] *)
Definition FUZZ_BMAX : Z := 2^31 - 2^26.

Lemma fuzz_calls_nonneg : 0 <= FUZZ_CALLS.
Proof.
ltac2:(KReplay.run1 (kr_t_V2FuzzIface ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3g0000j1ATg000Pj1@Tg0010j1;Tg001Nj14Tg001lj1?Tg002Wj21Tg003:j1:Tg003Xj45Tg004Cj76Tg004gj27Tg005Ij28Tg005cj29Tg006Oj3>Tg006ij3=Tg007Hj4<Tg008:j22Tg008Vj13Tf0R0#3#3p=0g009;R1#A%@1g009gR1#;%41%?1R2g00:Eg00:dR3P3g00;DR3P1g00;dR4,11g00<Bg00<i#0#0#0#0#0#:R5,11C5g00=NF61723P0f2R3g00=nR2g00>NR6'81903=>26df19=14C<b1b2b31245P0b0g00>n,24eo"). Qed.
Lemma fuzz_margin_bound : forall size, 0 <= size < 2^26 -> 0 <= fuzz_margin size <= FUZZ_BMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_V2FuzzIface ()) [] "h02Hah11Hh22H0h37__arithh44__ffh56__sat0h66__sat1h76__sat2h86__sat3h98__varmaph:5__with;4sizep;1p;2p;3p;4p;7g008Vj16Tg003:j13Tg00?lj12Tg00@Qj2>Tg00@nj21Tg00AJR0j25Tg00Aej2<Tg00BMj3=Tg00C1j2ATg008:j24Tg0000j1@Tg000Pj1?Tg0010j1NTg001Nj1MTg001lj1LTg002Wj2;Tg00CNj17Tg00Clj38Tg00DOj3FTg003Xj4:Tg00E2j7DTg004gj2CTg005Ij2ETg005cj2BTg006Oj3GTg006ij3HTg007Hj4ITg00EVj1JTg004Cj7KTg00;dR1f0R2'4p=0f1R3g00:ER4g00:dR5P5g00;DR6P2g00=NFKp=9g009gR7%02g00<iR8#6#3R9%28R8#6#2#6R:#3R;'>R<,12'5%28#2#2R8#3R=,<91119R>%0=1>9=R?,11[[%09R@g00FURAA=9=3UW0%0?\A^0@1<9;%0;111<[\>A=9;3VAX0@%0<\A^0@P0f5R0#0110<1A?<R?#014??'5R?f4f7#0f8/1<g009;R<#@%?<%N7%M7%L7R<P4P5P5P6P71;71g00<BR51;79R9%78587%7:98795F7R9C:,9<P7P9P5P9C:,9<FD1C<6P2f2R<g00=nR6g00>NR9'E1B2<=G69dAH713CIb4b9b:P?P2b3W2W1P3P2O2n2001000000121000000b5b6b7b8%J3R3#0g00G1,43'5eW1W;o"). Qed.
(* [comment removed for export] *)
Lemma fuzz_room_fits : room_k0 FUZZ_CALLS <= ROOM_KMAX /\ room_b0 FUZZ_BMAX <= ROOM_BCAP.
Proof.
ltac2:(KReplay.run1 (kr_t_V2FuzzIface ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h57__sat10h67__sat11h77__sat12h87__sat13h96__sat2h:6__sat3h;6__sat4h<6__sat5h=6__sat6h>6__sat7h?6__sat8h@6__sat9hA8__varmaphB5__witp;1p;2p;3p;4p;7g008Vj11Tg003:j13Tg00?lj10Tg00Aej25Tg00@Qj27Tg00BMj38Tg0000j1NTg000Pj1JTg0010j1HTg001Nj1GTg001lj1FTg00Gnj3@Tg003Xj4ETg00CNj19Tg00DOj3CTg00E2j7WTg004gj2VTg005Ij2UTg005cj2MTg006Oj3LTg006ij3KTg007Hj4ITg00HQj2?Tg00Hnj26Tg008:j2>Tg00C1j2ATg00AJj2BTg00IKj1OTg00JMj1PTg00@nj2QTg002Wj2RTg00KOj3STg004Cj7TTg00Clj3XTg00;dR0f0R1'Qp=41>01p=2g009gR2/R1p==%11#1p=<f1R3=S21p=:P3g00:ER4g00:dR5P5g00;DR6P1g00=NFTp=DAX231p=;g00<iR7#1R8#3R9%18R:#1R;#1R<#0R=#3R>'5%49R?%2>179>R@#4[[%29RAg00FURBA89>3UW0%2@\B^0A%0;R;#3R>,59%2>179>RC#4[\?A89>3VBX0A%2C\B^0A%3<R>,59%2>179>RD#4[\?A89>3VBX0A%2D\B^0A%08R8#0#1R>#3RE,59%2E179ERF#4[\?A89E3VBX0A%2F\B^0A%07R7#0#0#0RE#3RG,59%2G179GRH#4[\?A89G3VBX0A%2H\B^0A%17R7#0RG#0RI#3RJ,59%2J179JRK#4[\?A89J3VBX0A%2K\B^0A%1GRG#3RJ,59%2J179JRL#4[\?A89J3VBX0A%2L\B^0Ag009;RA#N%JA%H2%G2%F2RAP4P5P5P6P2%17R7#3R5#=%3:R:#=R4%<<#<#<#3RB#=5@2':g00<BRJ%07#0#1#0#1#<#0#1#0#1#<#<#3R7#=CE,DAP2%=9R9%9<';%9>,;9R>':%9I,;9%9;,;95C2%18#3R8#==@2>':':%9G,;9RG/:>':%9E,;9=C2G9@24':PJ%9=,;9CE,DAFW1VA6P1f2RAg00=nR6g00>NR9'U1M1A=L69dAK203CIb2bAbB1?:B,65/>716DF1AKC1?8F'6'616LF'61AHL,?:'6/>@'BP1b1b3b4b9b:b;b<b=b>b?b@b5b6b7b8g00>n#Og00L2'>g00G1#Pg00M:'>'Beo"). Qed.

Section WithLayout.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.

Definition fuzz_call_contract : Prop :=
  forall (fx : FPState) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word)
         (dptr : word) (size : Z) (payload : list byte) (ret sp0 : word) (argv envp : list (list byte)) (S : TSet),
    (* [comment removed for export] *)
    frm_zero (@fp_csr fx) ->
    ainv A m (m_vmmaps md) -> md_pure md -> al_env sp0 argv envp m ->
    (* [comment removed for export] *)
    getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 size -> size = Z.of_nat (length payload) -> size < 2 ^ 26 ->
    (0 < size -> live A dptr = Some size) ->
    (forall i, 0 <= i < size -> m (Z_to_bv 64 (bv_unsigned dptr + i)) = Some (nth (Z.to_nat i) payload (Z_to_bv 8 0))) ->
    (size = 0 -> dptr = Z_to_bv 64 A_EMPTY /\ forall a : word, A_EMPTY <= bv_unsigned a < A_EMPTY + 16 -> m a = None) ->
    bv_unsigned dptr mod 16 = 0 ->
    (* [comment removed for export] *)
    getr regs 1 = ret -> ret_ok ret -> getr regs 3 = Z_to_bv 64 0x10800 -> getr regs 4 = al_gp ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    alloc_top (m_vmmaps md) + 8192 + LEPT_STACK <= bv_unsigned (getr regs 2) ->
    bv_unsigned (getr regs 2) <= bv_unsigned sp0 -> bv_unsigned sp0 <= sp_window_hi ->
    init_sp_win (m_vmmaps md) ->
    (forall a : word, bv_unsigned (getr regs 2) - LEPT_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                      m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
    (* [comment removed for export] *)
    (forall a : word, A_LEPT_SEV <= bv_unsigned a < A_LEPT_SEV + 8 -> m a = None) ->
    (forall a : word, A_LEPT_PMM <= bv_unsigned a < A_LEPT_PMM + 16 -> m a = None) ->
    store_ok al_segs m (Z_to_bv 64 A_LEPT_HANDLER) 8 = true ->
    (forall a : word, A_GOT_LO <= bv_unsigned a < A_GOT_HI -> m a = None) ->
    (* [comment removed for export] *)
    forall (k b : Z), aroom A (m_vmmaps md) k b -> FUZZ_CALLS <= k -> fuzz_margin size <= b ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) A' m' vm' regs',
        frm_zero (@fp_csr fx') ->
        ainv A' m' vm' ->
        (forall q, live A' q = live A q) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        (forall r, callee_saved r -> getr regs' r = getr regs r) ->
        (* [comment removed for export] *)
        (forall a : word, ~ (al_grantable a /\ bv_unsigned a < alloc_top (m_vmmaps md)) -> ~ al_globals a ->
                          ~ al_errno_slot a ->
                          ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8) ->
                          ~ (bv_unsigned (getr regs 2) - LEPT_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                          m' a = m a) ->
        (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
        (forall a : word, m a <> None ->
                          bv_unsigned a < al_image_hi \/ (al_grantable a /\ bv_unsigned a < alloc_top (m_vmmaps md))
                          \/ m' a <> None) ->
        vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
        vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
        aroom A' vm' (k - FUZZ_CALLS) (b - fuzz_margin size) ->
        realizes al_segs (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
    realizes al_segs (mkCfg (@mkst fx regs (Z_to_bv 64 PC_FUZZ) m al_rom) md) S.
End WithLayout.
