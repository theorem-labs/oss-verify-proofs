(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from O2/O2LibStdioCall.v (whole file): stdio_call_sound restated over the budget carrier rzb; the KReplay name table gains entries for the twinned globals and the proof scripts are repointed at them, otherwise byte for byte. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise of stdio_call_sound_fr and stdio_call_sound). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts SymExec Hoare.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require StdioDefs LibStdioCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2ExitBase O2StdioDefs O2Reloc O2RelocCode O2RelocSites O2RelocImg O2RelocMusl.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.BudgetWit Require Import Rzb LibStdioCallB.
Ltac2 kr_t_O2LibStdioCallB () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common4Musl<LibStdioCall>know_ok_frame3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall>kimg_cut_soundC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I69OSSVerify5KrLib6Common4Musl9StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib2O2;O2StdioDefs7sw_post01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall7sc_bufpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall8sc_bufszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2LibStdioCall9sw_post_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCallCstdio_call_sound_frC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib2O2;O2RelocCode7o2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2RelocSites8o2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocMusl5o2_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2LibStdioCallCstdio_call_sound_frC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib9BudgetWit3Rzb3rzb00c59OSSVerify5KrLib9BudgetWit?O2LibStdioCallB9sw_post_LC59OSSVerify5KrLib9BudgetWit=LibStdioCallBEstdio_call_sound_fr_bc59OSSVerify5KrLib9BudgetWit?O2LibStdioCallBCstdio_call_sound_fr".
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

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
Notation stdio_call := (@LibStdioCall.stdio_call o2_reloc o2_data).

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
ltac2:(KReplay.run1 (kr_t_O2LibStdioCallB ()) [] "p;1p10000p4p70p1000^p4p7210p8g001:j10Tg002F#0o"). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
ltac2:(KReplay.run1 (kr_t_O2LibStdioCallB ()) [] "p;1g003>j10Tg002F#0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post o2_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LibStdioCallB ()) [] "p'0h01Hh14bufph25bufszh31fh42f1h52f2h62f3h72f4h82f5h93memh:4mem'h;2suh<1xi009swp_agreei019swp_growsi029swp_wbasei038swp_wendi048swp_wposp;1p;7p;6p;2p;3p;4p;;g004Jj11Tg004oj1ATg005Mj1@Tg0060j1BTg006RR0j7JTg007Vj6GTg008Sj1>Tg0098j14Tg009Vj2CTg00:3j26Tg00:]j29Tg00;9j2:Tg00;Uj2?Tg00<0j1<Tg00<Ij23Tg00<fj35Tg00=@j2ITg00>=j1HTg00>]j1FTg00?\j28Tg00@Bj10Tg00@aj47Tg00AYj2ETg00BSj2=Tg00C[j2;Tg00D=l;DTf0R1#1#1p=2g00E:R2#1R3#2R4#2R5#1R6#AR7#@R8%A4#@R4#BR9[R:g00E_R;g002FR<f5R=f4R>f3R?f2R@f1RAP1FJP0P<f6R0P=P>P?P@PAf7RBP0P=P>P?P@EGP1f;R=%>2R2#>#1#2R0#1#4'C1671RC'91:C='?#<%45,3=R5167ARC'9%22#2#4,3=,:C'?#<f<RC%40R0'3167@R2'9%46,3C,:2'?#<f:R2P?O1f?R6P?O1559[[[^<81ICB%H4R4#BRB%F<R<f81875g00F=#0#0#0#0#0#0#0#0R5C7f9R9,E2,=5,;435P<P9%>3#1#2#4,3C,87P5C71=5=,;455BP<P2f=R2/30,87P5C71=5C,;455Bf@P6f>P2PCP=P>P?P@PAP1M;DW8W7W6W5W4P>P?P@PAP1O5n700000001000000151100101103104102W0X::X28X18X3;W;W9o"). Qed.

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
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M (bv_unsigned (edenot E (sc_sp res))) (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     rzb RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  rzb RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31958) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Hrd H13 H14 H15 HCONT.
  rl_tail (@LibStdioCallB.stdio_call_sound_fr_b _ o2_reloc o2_code o2_sites o2_data o2_rw
             vals ebs sr kn R M model res pending extra K HR HK Hc
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Hrd H13 H14 H15
             (fun R' M' A B P => HCONT R' M' A B (sw_post_L _ _ _ _ _ _ P))).
Qed.

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
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     rzb RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  rzb RSEGS (mkCfg (mkst R (Z_to_bv 64 0x31958) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.
