(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts SymExec Hoare.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require StdioDefs LibStdioCall.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2ExitBase V2StdioDefs V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocMusl.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LibStdioCall () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall>know_ok_frame3C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall>kimg_cut_soundK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs7sw_post00I5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs7sw_post00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6Common7StoreOk9mem_growsI47Corelib4Init9Datatypes4list00C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission6Common8PropExec5v_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01K5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs7sw_post01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun7vals_evK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX23env01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7regs_okC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7know_okC47Corelib4Init9Datatypes6lengthC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26edenotC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_spC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive9junk_valsC47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_srC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_knC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall7sc_bufpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall8sc_bufszC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00c5ARocqVerifyHarness?AgentSubmission2V2>V2LibStdioCall9sw_post_LC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCallCstdio_call_sound_frC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_emitI47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX23env00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_dataI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocSites8v2_sitesC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocMusl5v2_rwc5ARocqVerifyHarness?AgentSubmission2V2>V2LibStdioCallCstdio_call_sound_fr".
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation SC_KEPT := LibStdioCall.SC_KEPT.
Notation stdio_res := LibStdioCall.stdio_res.
Notation SCR_ := LibStdioCall.SCR_.
Notation sc_f := LibStdioCall.sc_f.
Notation sc_fd := LibStdioCall.sc_fd.
Notation sc_ret := LibStdioCall.sc_ret.
Notation sc_wb := LibStdioCall.sc_wb.
Notation sc_wp := LibStdioCall.sc_wp.
Notation sc_bufp := LibStdioCall.sc_bufp.
Notation sc_bufsz := LibStdioCall.sc_bufsz.
Notation sc_s := LibStdioCall.sc_s.
Notation sc_l := LibStdioCall.sc_l.
Notation sc_sp := LibStdioCall.sc_sp.
Notation sc_sr := LibStdioCall.sc_sr.
Notation sc_kn := LibStdioCall.sc_kn.
Notation lit_even_ret := LibStdioCall.lit_even_ret.
Notation kimg_cut1 := LibStdioCall.kimg_cut1.
Notation kimg_cut := LibStdioCall.kimg_cut.
Notation stdio_call := (@LibStdioCall.stdio_call v2_reloc v2_data).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation inr := LibStdioCall.inr.
Notation inr_spec := LibStdioCall.inr_spec.
Notation inr_false := LibStdioCall.inr_false.
Notation Forall_one' := LibStdioCall.Forall_one'.
Notation u_lit0 := LibStdioCall.u_lit0.
Notation flat_abs0 := LibStdioCall.flat_abs0.
Notation split_lit_denot := LibStdioCall.split_lit_denot.
Notation split_lit_vars := LibStdioCall.split_lit_vars.
Notation kindex_some := LibStdioCall.kindex_some.
Notation ridx_lit := LibStdioCall.ridx_lit.
Notation sr_get_nat := LibStdioCall.sr_get_nat.
Notation length_sr_upd := LibStdioCall.length_sr_upd.
Notation nth_sr_upd_same := LibStdioCall.nth_sr_upd_same.
Notation nth_sr_upd_other := LibStdioCall.nth_sr_upd_other.
Notation length_sr_after_call_j := LibStdioCall.length_sr_after_call_j.

Lemma know_ok_frame3 : forall E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M kn ->
  flat E (SA b1 o1) n1 -> flat E (SA b2 o2) n2 -> flat E (SA b3 o3) n3 ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LibStdioCall ()) [] "p;1p10000p4p70p1000^p4p7210p8g001:j10Tg002F#0o"). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LibStdioCall ()) [] "p;1g003>j10Tg002F#0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post v2_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LibStdioCall ()) [] "p'0h01Hh14bufph25bufszh31fh42f1h52f2h62f3h72f4h82f5h93memh:4mem'h;2suh<1xi009swp_agreei019swp_growsi029swp_wbasei038swp_wendi048swp_wposp;1p;7p;6p;2p;3p;4p;;g004Jj11Tg004oj1ATg005Mj1@Tg0060j1BTg006RR0j7JTg007Vj6GTg008Sj1>Tg0098j14Tg009Vj2CTg00:3j26Tg00:]j29Tg00;9j2:Tg00;Uj2?Tg00<0j1<Tg00<Ij23Tg00<fj35Tg00=@j2ITg00>=j1HTg00>]j1FTg00?\j28Tg00@Bj10Tg00@aj47Tg00AYj2ETg00BSj2=Tg00C[j2;Tg00D=l;DTf0R1#1#1p=2g00E:R2#1R3#2R4#2R5#1R6#AR7#@R8%A4#@R4#BR9[R:g00E_R;g002FR<f5R=f4R>f3R?f2R@f1RAP1FJP0P<f6R0P=P>P?P@PAf7RBP0P=P>P?P@EGP1f;R=%>2R2#>#1#2R0#1#4'C1671RC'91:C='?#<%45,3=R5167ARC'9%22#2#4,3=,:C'?#<f<RC%40R0'3167@R2'9%46,3C,:2'?#<f:R2P?O1f?R6P?O1559[[[^<81ICB%H4R4#BRB%F<R<f81875g00F=#0#0#0#0#0#0#0#0R5C7f9R9,E2,=5,;435P<P9%>3#1#2#4,3C,87P5C71=5=,;455BP<P2f=R2/30,87P5C71=5C,;455Bf@P6f>P2PCP=P>P?P@PAP1M;DW8W7W6W5W4P>P?P@PAP1O5n700000001000000151100101103104102W0X::X28X18X3;W;W9o"). Qed.

Section VP17.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem stdio_call_sound_fr :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->   (* [comment removed for export] *)
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M (bv_unsigned (edenot E (sc_sp res))) (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3e37c) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LibStdioCall ()) ["VP17"] "h02M'h12R'h21Ah31Bh41Eh52H1h63H10h73H11h83H12h93H13h:3H14h;3H15h<2H2h=2H3h>2H4h?2H5h@2H6hA2H7hB2H8hC2H9hD5HCONThE2HKhF2HRhG2HchH1KhI1MhJ1PhK1RhL3RLThM3ebshN5extrahO2knhP1lhQ5modelhR7pendinghS3reshT1shU2srhV2suhW4valshX2wbhY2wpp;1p;2p;3p;4p;5p;6p;7p;Tg004Jj10Tg004oj1DTg005Mj1PTg00>=j1;Tg008Sj12Tg00F\j2aTg0060j19Tg00GHj17Tg00HLj26Tg00ITj3ETg00Jdj4ITg00L4j28Tg00LTj5pTg00C[j2CTg00<fj35Tg00M\j1eTg00N_j21Tg00:3j23Tg00Ohj1`Tg00Pkj1_Tg00Qmj1^Tg00Roj1?Tg00:]j24Tg0098j1:Tg009Vj2FTg00T2j1@Tg00<Ij2>Tg00TRj2]Tg00Toj2MTg00?\j2ATg00@aj4LTg00UIj1\Tg00V=j1KTg00W@j2[Tg00X8j1ZTg00Y0j1YTg00Ygj1XTg00ZIj2oTg00Zij1nTg00[aj1WTg00\Aj1VTg00]Ij3=Tg00]fj1UTg00^ij1TTg00_lj1JTg00`nj1GTg00b3j1HTg007Vj6dTg00c9j1cTg00d=j1QTg00e9j5OTg00f2j2RTg00fgj3STg00>]j1bTg006Rj7fTg00gfj7gTg00hflThTg00j7j2iTg00k7j2jTg00l1j1kTg000^j4lTg00lgj2mTf0R0#0#0p=B%00#0#0#0#0#0#0#0p=<%00#0#0#0p=Ng00E:R1#0R2#BR3#BR4#0R5#DR6#PR7#;g00mb%D3#PR3#;R8[g00nA#;g00oJ#;%22R9#D/a7R:%93\7R;g010Ug011KR<g012Tf:R=#7f9R>'6g013Mf7R?9E0>g014UR@f1RAP?P>CI%9<g002FRBg015gRCf=RD,87f;REP=Dpf6RF,C<35f3R<%e?'1,36g00E_RGf4RHf8RI#`'1,36PGf5RJ%_>'1P7%^=,1FP7%?E,1?,36PG14H<%05#<#<#<#<#<#:R5,4H1FJF183D#@RK55G136H=5GKf?RK,83#@RGf>RL,83#@'>%:2%21#2R1#2#0#:']R2'4f@,83#@/>G/42%N1#:R1,FF,4>14F='M136>R2136I'>1F?1'414?2'M136=/>2/45%98R5P@fGR21A6DfDR1,83RGCL1C81R135P@fHRMf<RNPGCL=551g016aR1#9%\M%K2,A6RM'[%ZM,C135%97fIR1#Y%X7351o77RM#;fJR5#n%WM35P2g017YRM#WO1fTRG%VARO5=7#7fSRP'6fMRQ#U;EAP@fURRf2RS#VRT5=7#7/6GPAfNRU#TCIfQRVfKRWfORX#?'1,36%JX%GX,1W%HX,1WPSEdp,2fxRYPHfPRZ#c,A6P<%Q@DO/RV=S@Q[[[^0;^1:PYPBg018Og019JPCg01:GPPfRRCPVPZPXPUPQfLR@PWP5P1P2fFfEPKPLPDPNPEP=P>PIP?PFPJPHP<PSPAA=7RO#7/6G%UU;EA%bBRGfVRO==7T#7/6RPA%TXCIPBPCfWRC#7/6ORO%?Z'1,36%JZ%GZ,1O%HZ,1OPSFfPJPHP<PSPAPPfX#7/6CRC%?V'1,36%JV%GV,1C%HV,1CP<P0FgO5WJW3W2X0;X1:MThPYPX%24#2#2#0#2,iB%29#2#2#0#B#2#2#B#N#:'jPU%QGDO/RQP3PM%K@,A6#kA=3W5Cl/m15SGP0bLWDW;W:W9W8W7W6WCWBWAW@W?W>W=W<W5bVbPbTbYbXWGWEWFb4WHXN8XR8WSWQWIWKWOWUWMWWo"). Qed.

(* [comment removed for export] *)
Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3e37c) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LibStdioCall ()) ["VP17"] "h02M'h12R'h21Eh32HKh43HK'h52HRh63HR'h72Hch81Kh91Mh:1Rh;2_Hh<3ebsh=5extrah>2knh?1lh@5modelhA7pendinghB3reshC1shD2srhE2suhF4valshG2wbhH2wpp;1p;2p;3p;4p;5p;6p;Ng004Jj10Tg004oj1BTg005Mj1HTg00>=j1:Tg008Sj1>Tg00F\j2ZTg0060j19Tg00GHj15Tg00HLj26Tg00ITj3ATg00Jdj4@Tg00L4j27Tg00LTj5hTg00C[j2DTg00<fj33Tg00M\j1^Tg00N_j22Tg00:3j24Tg00Ohj1YTg00Pkj1XTg00Qmj1WTg00Roj1ITg00:]j21Tg0098j1;Tg009Vj2CTg00T2j1?Tg00<Ij2=Tg00TRj2VTg00Toj2GTg00?\j2ETg00@aj4FTg00UIj1QTg00V=j1PTg00W@j2RTg00X8j1OTg00Y0j1STg00Ygj1TTg00ZIj2gTg00Zij1fTg00[aj1MTg00\Aj1LTg00]Ij3<Tg00]fj1JTg00^ij1KTg00c9j1eTg00d=j1dTg00e9j5]Tg00f2j2_Tg00fgj3`Tg00_lj1\Tg00`nj1aTg00b3j1bTg007Vj6[Tg01;@lNcTf0R0#0#0p=N%00#0#0#0#0#0#0#0p=8%00#0#0#0p=Ug00E:R1#0R2#NR3#0#NR4#BR5#HR6#:g00mb%B3#HR3#:R7[g00nA#:g00oJ#:%>2#B/Z6R8%93\6R9g010Ug011KR:g012Tf:R;#5f9R<'6g013Mf7R=9A0<g014UR0f1R>P=P<C@%9:g002Fg015gf=R?,76f;R@P;Dhf6RA,D:33f3R:%^='2,45g00E_RBf4RCf8RD#Y'2,45PBf5RE%X<'2P6%W;,2AP6%I@,2=,45PB11C:%04#8#8#8#8#8#;R4,1C1CEA173?#?R@53B145C=3B@f?R@,73#?RBf>RF,73#?'=%;2%>1#>R1#>#0#;'VR2'1f@,73#?/=B/12%U1#;R1,CA,1<11A;'G145<R2145D'=1C=1'111=2'G145;/=2/14%97R4P0fGR21E5?fDR1,73R3CF1D71R133P0fHRBf<RGP3CF=341g016aR1#9%QB%P2,E5RB'R%OB,D133%96fIR1#S%T6331g66RB#:fJR4#f%MB33P2g017Y#MO1fTRB%L>R35<6#5fSRH'6fMRI#J;A>P0fURJf2RK#LRL5<6#5/6BP>fNRM#KC@p,2fxP:fORN#e,E5PK%d0D]fPRO'_fLRP5`0[[^09^18PHfRRHfQPOPNPMPIPPfKP4P1P2fFfEP@PFP?PGP;P;P<PDP=PAPEPCP:PKP>A<6J3#5/6B%JM;A>P0fVR0=<6L#5/6JP>%KNC@PHfW#5/60R0%IO'2,45%\O%aO,20%bO,20PKE[PEPCP:PKP>O4W;W4W6X09X18MNcUUUUUUUUUUUUUUUUbEb?bCbHbGW7W3W5b2W8X=7XA7WBW@W9W:W>WDW<WFo"). Qed.
End VP17.
