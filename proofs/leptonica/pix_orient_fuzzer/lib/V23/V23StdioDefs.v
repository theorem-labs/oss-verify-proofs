(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require StdioDefs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Export V23ExitBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23StdioDefs () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00i5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs7sw_post00C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs9swp_agreeC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7rdn_extC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs9swp_growsC5ARocqVerifyHarness?AgentSubmission6Common7StoreOk=store_ok_mono".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x126c00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x158440))
  /\ rdn RSEGS mem (Z_to_bv 64 0x158440) 8%nat = Some (word_to_le_bytes 8 can).

(* [comment removed for export] *)
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

(* [comment removed for export] *)
Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
  sw_post mem su f bufp bufsz mem' ->
  rdn RSEGS mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
  rdn RSEGS mem' a n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StdioDefs ()) ["VP1"] "h04__x1h14__x2h24__x3h34__x4h47__arithh54__ffh66__sat4h76__sat5h88__varmaph95__with:4cstrh;2Hah<2D1h=2D2h>2D3h?1Hh@3HnwhA2HxhB1PhC1ahD2bshE4bufphF5bufszhG1fhH3memhI4mem'hJ1nhK1ohL2suhM1xp;1p;6p;4p;2p;3p;;p;7p;8g0000j10Tg000Uj1TTg0013j1OTg001Vj1KTg0028j1UTg002Xj6gTg003Wj4ITg004Oj2PTg0051j3GTg005Kj26Tg0065j17Tg006Uj1<Tg0073j2VTg007Pj1STg0085j2JTg008Rj21Tg008nj2;Tg009Hj24Tg009ej25Tg00:Aj2:Tg00:\j1]Tg00;Aj2\Tg00;ij3[Tg00<Mj1BTg00<lj2=Tg00=Uj3DTg00>>j2NTg00>jj1ZTg00?Jj3ATg00?jj2MTg00@Hj1YTg00@fj4LTg00ADj1XTg00Abj1WTg00BMj2@Tg00C0j3>Tg00CSj1lTg00D5j29Tg00DXj3kTg00E;j2jTg00E]j2iTg00F7j2fTg00Fcj3eTg00GBj4dTg00H4l;cTg00I3j7bTg00Ioj6aTg00JMj4QTg00K8j7RTg00K\j7`Tg00L@j7_Tg00Ldj6^Tg00MHj8hTf2R0f1R1'4f0R2'1p=2P0g00MlR3g00NKR4P4g00NkR5g00OKR6P1g00OiP2CQg00PPR7FRp=3P6P1g00Q0P2CQp=?P1P3P4P4P5P2P7FRp=CP0P3P4P4P5P1P2F`p=EP0P3P4P4P5P1P2F_p=FP1P3P4P4P5P2E^p=Hf3R7P3P4P4P5P0P1P2Ghp=8g00QWR3#0R8#0R9#0R:#0#0R;#0R<#TR=#OR>%T:#OR:#K[R?g00R<%U:R:f8R@f7RAf6RBf5RCf4RDP7Eg%K:REg00R[RFf9RGP7P0CI1P:13G16=D%77%<8RH%<<R<'VRI3216=CRJ%7Df:RK%S3RL#S#0#0#0RM#0#<RN'J3211KJ';16=BRO%7C%<;R;,4K32%0L#0#0#0#<RP=2KO';16=ARO%7Bf;RK%<MRM'432A2K<O';PEPFf>ROP@PACI1P:A9GE2XKEPDPFPGP@PACIPFPAPGPOP@P716=GRF16=2RE'1%7@,4F,5E':f@f?POf=REf<PKPAP1%]GRKg00TBRF%7G'1RG1\H<R:15FH11F<15FI[[RQ11FHRRg00T`RSA[H<1UW;RH11FI\S^;RRRg00U<RSg00UhRI#BRT#BRU#BRV,=61=6URU1=6T5D65D6g00VGRT'NRW%BV,=61=6I9D6U5D6/NTRT%ZSRU5AS3ARI%USRVP6P61M6DP0%Y6CLP11M67CLRX%X6RY%W6RZ1@6LRL1@68R853Z1@69R99>6LR[,?8,CZ5EZR\%l4R4PZ1@63R3196N5k6R]93Z[A3Z3L5FZP4A3Z]81?83,CZ5EZ,HZC8C81jZ5R5P2P0g00W3R]g00WSR^'i1f20=G]^dAe6F1CdR^b5b8b9X06X16X26X3611011407,51':R]147DR_1J1N'11117';1J0N/171570':g00X3RN[[[^06^16^26^36P2%7ERE16=OROPJfCPDP@O6b4b6b7b:PKPGP:PQPHPRAASWU9ASTPVPXPYPZ196F=3Z9P4PZP\P4PZ196;9>63R993Z[196P9>63RT=3ZL5FZP4A3Z981?8T,CZ5EZ,HZC8C8C8P5P^b5b8b9X06X16X26X3611F71170150_':140;92DCA20PD';A27;D147P,5D':PN[[[[^06^16^26^36P2PEPOPJfBRPP7PDPAO7b4b6b7b:PKPGP:PQPHPRPIPVPXPYPZP\P4PZ196M9>63R\93Z[196<9>63R3=3ZL5FZP4A3Z\81?83,CZ5EZ,HZC8C8P5P^b5b8b9X06X16X26X36141M,1_A21<7';A20M7140<,57':PN[[\]^06^16^26^36P2PEPOPJPPPDPBO6b4b6b7b:M;cWAXM>FbEaW>W=W<W@W?WBWDWJXC>XI?XF>XE>XG6XL6WHo"). Qed.
End VP1.

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StdioDefs ()) ["VP2"] "h01Hh11Ph21ah34bufph45bufszh51fh63memh74mem'h81nh92sup;1p;6p;4p;3p;7g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg002Xj68Tg00XPj47Tg0051j36Tg00YPj74Tg00ZOj75Tg00QW#0#0#0R0#0#0#0#2#1R1%20#1#3[R0g00OKR2g00R<f7R3f6R4f5R5f4R6f3R7f2R8E8g00W3g00R[R9f8R:P8f1R;C7g00WS36P9P8f9R8P6P7P8P:P3P4P5P6P;F4f0F5W0W1W8X21X70X41X31X52W9W6o"). Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition atexit_state (mem : word -> option byte) (v : StdioDefs.foe_variant) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x15821c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ match v with
     | StdioDefs.FOE_none =>
         rdn RSEGS mem (Z_to_bv 64 0x158228) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | StdioDefs.FOE_one =>
         rdn RSEGS mem (Z_to_bv 64 0x158228) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x158230))
         /\ rdn RSEGS mem (Z_to_bv 64 0x158220) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
         /\ rdn RSEGS mem (Z_to_bv 64 0x158230) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0x158238) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10e48c))
         /\ rdn RSEGS mem (Z_to_bv 64 0x158338) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x63568))
         /\ rdn RSEGS mem (Z_to_bv 64 0x137f14) 1%nat = Some [Z_to_bv 8 0]
     end.

(* [comment removed for export] *)
Ltac atexit_solve tac :=
  first [ solve [ exists StdioDefs.FOE_none; cbv beta iota delta [atexit_state]; split; tac ]
        | exists StdioDefs.FOE_one; cbv beta iota delta [atexit_state]; repeat split; tac ].
(* [comment removed for export] *)

Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  (* [comment removed for export] *)
  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x158438) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x126c08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1236a0));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x126c10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123698));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x123698) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x630b0));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x127f08) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x126a40) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10e3c4));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x126a48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_dso  : exists dso : word, rdn RSEGS mem (Z_to_bv 64 0x127c38) 8%nat = Some (word_to_le_bytes 8 dso);
  (* [comment removed for export] *)
  ec_atexit : exists v : StdioDefs.foe_variant, atexit_state mem v;
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0x127cc0 wp2 rp2
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1139cc));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x127db0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x158448 <= wb < wp /\ wp <= 0x159000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= 2 ^ 30)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x127db0 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
