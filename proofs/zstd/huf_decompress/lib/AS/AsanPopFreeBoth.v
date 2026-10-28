(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanPopFreeAsan () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_both1M?loaded_segmentsc5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBothAasan_popfree_headC5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW0I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW1C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW2K47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW3C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW4C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW5C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW6C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree3PW7C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFreeDpopfree_spec_of_codeC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF0c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF1c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF2c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF3c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF4c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF5c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF6c5ARocqVerifyHarness?AgentSubmission2AS?AsanPopFreeBoth3PF7K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission2AS;AsanPopFree@popfree_loop_run".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition asan_popfree_head : Z := 0x36a5c.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS (Z_to_bv 64 asan_popfree_head) = Some PW0.
Proof. vm_refl. Qed.
Lemma PF1 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1.
Proof. vm_refl. Qed.
Lemma PF2 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2.
Proof. vm_refl. Qed.
Lemma PF3 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3.
Proof. vm_refl. Qed.
Lemma PF4 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4.
Proof. vm_refl. Qed.
Lemma PF5 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5.
Proof. vm_refl. Qed.
Lemma PF6 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6.
Proof. vm_refl. Qed.
Lemma PF7 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7.
Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments asan_popfree_head.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p;;g0000j10Tg00<Mj12Tg00Cnj2?Tg00DVj24Tg00E2j23Tg00ENj2NTg00Ekj3GTg00FOj1>Tg00Foj1=Tg00GOj1<Tg00Gmj1;Tg00HKj1:Tg00?6j11Tg00I6j25Tg00IYj49Tg00JDj3MTg000Uj1LTg00Jgj3KTg00KJj7FTg00Knj2@Tg0069j2ATg00LPj2BTg004Bj3CTg00M<j3DTg00M[j4ETg00<kj26Tg00NMj27Tg00Nhj7ITg00OLl;JTf1R0g00PTR1g00Q3R2P2g00QSR3f0R4g00R3FIp=8g008>g009MR5P4g00RSg00SNg00TIg00UDg00V?g00W:g00X5g00Y0M;Jp=Hg007YR6#0R7#2R8%07#0#0#0R7#0R9#2R:'?g00YkR;/4813;:1N8:R<,4;[[13;8R=g00ZIR>AG8:0UW013;<\>^0=g00ZeR=#>%==g00[QR=#<%;=%:=R>P1P2P2P3P=%16R6#1#0#0#2R2,5=g00[o%06#1#1#0#1#0#1#0#1#1#0#0#1#0#0#0#2R6,5=R1C9,8>P=%27R7,5=9M=1g00\V15=8%L95K=C9,8>FF1@>3P4f2R>g00;MR3g00;mR9'A1B4>=C39dAD=;0CEb2b5b613261667/4<'7P4b1b3b413251657/4<'7e#Ho"). Qed.

(* [comment removed for export] *)
Theorem asan_popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok ASEGS mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps ASEGS (mkst regs (Z_to_bv 64 asan_popfree_head) mem rom)
                (mkst regs' (Z_to_bv 64 (asan_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p;;g0000j10Tg00<Mj12Tg00Cnj2?Tg00DVj24Tg00E2j23Tg00ENj2NTg00Ekj3GTg00FOj1>Tg00Foj1=Tg00GOj1<Tg00Gmj1;Tg00HKj1:Tg00?6j11Tg00I6j25Tg00IYj49Tg00JDj3MTg000Uj1LTg00Jgj3KTg00KJj7FTg00Knj2@Tg0069j2ATg00LPj2BTg004Bj3CTg00M<j3DTg00M[j4ETg00<kj26Tg00NMj27Tg00Nhj7ITg00]=l;JTf1R0g00PTR1g00Q3R2P2g00QSR3f0R4g00R3FIp=8g008>g009MR5P4g00RSg00SNg00TIg00UDg00V?g00W:g00X5g00Y0M;Jp=Hg007YR6#0R7#2R8%07#0#0#0R7#0R9#2R:'?g00YkR;/4813;:1N8:R<,4;[[13;8R=g00ZIR>AG8:0UW013;<\>^0=g00ZeR=#>%==g00[QR=#<%;=%:=R>P1P2P2P3P=%16R6#1#0#0#2R2,5=g00[o%06#1#1#0#1#0#1#0#1#1#0#0#1#0#0#0#2R6,5=R1C9,8>P=%27R7,5=9M=1g00\V15=8%L95K=C9,8>FF1@>3P4f2R>g00;MR3g00;mR9'A1B4>=C39dAD=;0CEb2b5b613261667/4<'7P4b1b3b413251657/4<'7e#Ho"). Qed.
