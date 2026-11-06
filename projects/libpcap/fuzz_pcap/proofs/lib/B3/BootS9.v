(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanMemIsZero. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKn2__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn7a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS5 BootS6 BootS7. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS8. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW4.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots9_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac arith_goal := lazymatch goal with
  | |- ?G =>
    let rec chk G := lazymatch G with
      | (_ <= _)%Z => idtac | (_ < _)%Z => idtac | (_ >= _)%Z => idtac | (_ > _)%Z => idtac | @eq Z _ _ => idtac
      | (_ <= _)%nat => idtac | (_ < _)%nat => idtac | @eq nat _ _ => idtac
      | ?A /\ ?B => chk A; chk B | ?A \/ ?B => chk A; chk B | ~ ?A => chk A | False => idtac
      end in chk G
  end.
(* [comment removed for export] *)
Ltac lia_p := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Ltac arith_lia := arith_goal; lia_p.





(* [comment removed for export] *)

(* [comment removed for export] *)
Definition STv (sp : word) : Z := (bv_unsigned sp + 3935) / 4096 * 4096.          (* [comment removed for export] *)
Definition XQv (sp : word) : Z := (STv sp - 8388608) / 8.                         (* [comment removed for export] *)
Definition PBv (sp : word) : Z := (XQv sp + CSH + 4095) / 4096 * 4096.            (* [comment removed for export] *)
Definition PEv (sp : word) : Z := (XQv sp + CSH + 2 ^ 20) / 4096 * 4096.          (* [comment removed for export] *)
Definition TSH (a : word) : Z := (bv_unsigned a + 2048) / 8 + CSH.                (* [comment removed for export] *)
Definition TPG (a : word) : Z := TSH a / 4096 * 4096.                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition H9a (sp p8 sb p10 p12 : word) : word -> bool := hhide (H8 sp p8 sb p10 p12) (XQv sp + CSH) NSW.
Definition HWLO (sp : word) : Z := (XQv sp + CSH) / 4096 * 4096.
Definition A9a (sp sb p12 : word) : list (Z * Z) := (HWLO sp, HWLO sp + (NSW + 4096)) :: A8 sp sb p12.
Definition H9 (sp p8 sb p10 p12 a : word) : word -> bool := hcut (H9a sp p8 sb p10 p12) (TSH a) 60.
Definition A9 (sp sb p12 a : word) : list (Z * Z) := (TPG a, TPG a + 4096) :: A9a sp sb p12.
(* [comment removed for export] *)
Definition LZ30 (sp p8 sb p10 p15 : word) : list (word * word) := LZ24 p8 sb p10 p15.

Lemma x9_facts : forall sp : word, bv_unsigned sp mod 16 = 0 -> 0x7fff80000000 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 47 ->
  STv sp mod 4096 = 0 /\ bv_unsigned sp - 160 <= STv sp /\ STv sp <= bv_unsigned sp + 3920
  /\ 0x7fff80000000 <= STv sp /\ STv sp <= 2 ^ 47
  /\ STv sp = 8 * XQv sp + 8388608 /\ XQv sp mod 512 = 0 /\ XLO <= XQv sp /\ XQv sp <= XHI
  /\ PBv sp mod 4096 = 0 /\ XQv sp + CSH <= PBv sp /\ PBv sp <= XQv sp + CSH + 3584
  /\ PEv sp mod 4096 = 0 /\ PEv sp = PBv sp + 2 ^ 20 - (if XQv sp mod 4096 =? 0 then 0 else 4096)
  /\ (XQv sp mod 4096 = 0 -> PBv sp = XQv sp + CSH).
Proof.
  intros sp Hal Hlo Hhi. unfold PEv, PBv, XQv, STv, XLO, XHI, CSH.
  pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as D16. set (u := bv_unsigned sp) in *.
  pose proof (Z.div_mod (u + 3935) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (u + 3935) 4096 ltac:(lia)) as M.
  set (q := (u + 3935) / 4096) in *.
  assert (Q : 34359214080 <= q <= 34359738368) by lia.
  replace ((q * 4096 - 8388608) / 8) with (512 * q - 1048576) by (apply Z.div_unique with (r := 0); lia).
  pose proof (Z.div_mod q 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as M8. set (q8 := q / 8) in *. set (r := q mod 8) in *.
  assert (E1 : (512 * q - 1048576 + 2147450880 + 4095) / 4096 = q8 + 524024 + (if r =? 0 then 0 else 1)).
  { symmetry. apply Z.div_unique with (r := if r =? 0 then 4095 else 512 * r - 1); destruct (Z.eqb_spec r 0); lia. }
  assert (E2 : (512 * q - 1048576 + 2147450880 + 2 ^ 20) / 4096 = q8 + 524280).
  { symmetry. apply Z.div_unique with (r := 512 * r); lia. }
  assert (E3 : (512 * q - 1048576) mod 4096 = 512 * r).
  { symmetry. apply Z.mod_unique with (q := q8 - 256); lia. }
  rewrite E1, E2, E3.
  repeat split; try (destruct (Z.eqb_spec r 0); lia); try lia;
    try (first [apply Z_mod_mult | rewrite Z.mul_comm; apply Z_mod_mult]).
  - replace (512 * q - 1048576) with ((q - 2048) * 512) by lia. apply Z_mod_mult.
  - destruct (Z.eqb_spec (512 * r) 0); destruct (Z.eqb_spec r 0); lia.
Qed.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation at_E16r' := (at_E16r sp brk mbase draw lim inp).
  #[using="brk mbase draw inp VI VE"] Lemma SA16' : usp mod 16 = 0. Proof. exact (SA16 sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SLo' : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SHi' : usp <= 2 ^ 47. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s9_b24a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR24 KN24 L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR24a KN24a L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_stacktop_site) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_munmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K HB HK.
    change SR24 with SR_E16r in HB. change KN24 with KN_E16r in HB.
    rg_block VI VE HB HK run24a_eq car24a_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s9_fresh : forall a tid c pl js p8 sb p10 p12 p15 R M mdl, length js = 46%nat ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR24a KN24a L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ [Z_to_bv 64 (STv sp)]) SR25 KN25 L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl Hjs HB.
    assert (LEN : length (VB' a tid c pl js) = 62%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & _).
    assert (G10 : getr R 10%bv = Z_to_bv 64 (STv sp)).
    { destruct HB as [HR _ _ _ _ _ _ _ _ _ _ _]. rewrite (HR 10%bv), STX_eq. apply bv_eq.
      unfold STX. change (bv_unsigned (mul_div M_MUL (Z_to_bv 64 4096) (alu64 ALU_SRL (edenot (EB' a tid c pl js) (EAlu ALU_ADD (EVar 0) (ELit 3935))) (Z_to_bv 64 12))) = bv_unsigned (Z_to_bv 64 (STv sp))).
      rewrite u_mul64, u_srl64. change (edenot (EB' a tid c pl js) (EAlu ALU_ADD (EVar 0) (ELit 3935))) with (alu64 ALU_ADD (ev (EB' a tid c pl js) 0) (Z_to_bv 64 3935)).
      rewrite u_add64, ev_EB_sp, !u_lit64, two64_eq. unfold STv. change (4096 mod 2 ^ 64) with 4096. change (3935 mod 2 ^ 64) with 3935. change (2 ^ (12 mod 2 ^ 64 mod 64)) with 4096.
      fold usp. rewrite (Z.mod_small (usp + 3935)) by lia. unfold STv in X4, X5. fold usp in X4, X5. rewrite !Z.mod_small by lia. lia. }
    unfold SR25, KN25. rewrite <- LEN. apply (bs_fresh sp brk mbase draw lim inp _ _ a tid c pl js SR24a KN24a L24 _ _ R M mdl 10%bv (Z_to_bv 64 (STv sp)) KF62 HB G10).
    - rewrite LEN. vmeq_refl.
    - rewrite LEN. vmeq_refl.
    - rewrite LEN. vmeq_refl.
    - assert (Hev : edenot (EB' a tid c pl (js ++ [Z_to_bv 64 (STv sp)])) (EVar (length (VB' a tid c pl js))) = Z_to_bv 64 (STv sp)).
      { rewrite EB_app. cbn [edenot ev]. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      unfold KF62. rewrite LEN in Hev. constructor; [| constructor; [| constructor]]; cbn [kentry_ok]; rewrite Hev, u_small by lia.
      + split; [lia | exact X1].
      + lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s9_b25a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K,
    ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR25 KN25 L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR25a KN25a L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memset) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_stacktop_site) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K E62 HB HK.
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & _).
    pose proof (u64_range sp) as Usp.
    assert (E0 : ev (EB' a tid c pl js) 0 = sp) by apply ev_EB_sp.
    assert (V62 : bv_unsigned (ev (EB' a tid c pl js) 62) = STv sp) by (rewrite E62; apply u_small; lia).
    assert (MW : forall x k, 0 <= k -> k <= x -> x < 2 ^ 64 -> (x + (2 ^ 64 - k)) mod 2 ^ 64 = x - k)
      by (intros x k Hk Hkx Hx; replace (x + (2 ^ 64 - k)) with (x - k + 1 * 2 ^ 64) by lia; rewrite Z_mod_plus_full; apply Z.mod_small; lia).
    rg_block_sc VI VE HB HK run25a_eq car25a_eq
      ltac:(first
        [ (* [comment removed for export] *)
          cbn [branch_taken edenot]; rewrite E0, E62; unfold bv_ltu;
          first [ apply negb_false_iff; apply Z.ltb_lt | apply Z.ltb_ge ];
          rewrite !u_add64, !u_lit64, !two64_eq; fold usp;
          change ((-312) mod 2 ^ 64) with (2 ^ 64 - 312); try change ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608);
          rewrite (Z.mod_small (STv sp)) by lia; rewrite !MW by lia; lia
        | (* [comment removed for export] *)
          cbn [branch_taken]; unfold bv_ltu; apply Z.ltb_lt;
          change (bv_unsigned (edenot (EB' a tid c pl js) (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (XQ 62)) (YQ 62)) (ELit 1)))
                  < bv_unsigned (edenot (EB' a tid c pl js) (ELit 18446744073709551615)));
          rewrite (s0_val (EB' a tid c pl js) 62) by (rewrite V62; first [exact X1 | lia]);
          cbn [edenot]; rewrite u_lit64; reflexivity ]).
  Qed.
  (* [comment removed for export] *)
  Definition WSW : list word := [Z_to_bv 64 (XQv sp); Z_to_bv 64 (PBv sp)] ++ repeat (Z_to_bv 64 0) 6.

  (* [comment removed for export] *)
  #[using="brk mbase VI VE usp"] Lemma re_facts : forall a tid c pl js ws, length js = 47%nat ->
    ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) ->
    nth 0 ws (Z_to_bv 64 0) = Z_to_bv 64 (XQv sp) -> nth 1 ws (Z_to_bv 64 0) = Z_to_bv 64 (PBv sp) ->
    let E := EB' a tid c pl (js ++ ws) in
    bv_unsigned (ev E 62) = STv sp /\ ev E 63 = Z_to_bv 64 (XQv sp) /\ ev E 64 = Z_to_bv 64 (PBv sp)
    /\ bv_unsigned (ev E 63) = XQv sp /\ bv_unsigned (ev E 64) = PBv sp.
  Proof.
    intros a tid c pl js ws Hjs E62 W0 W1 E.
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & _).
    unfold XLO, XHI, CSH in *.
    assert (E62' : ev E 62 = Z_to_bv 64 (STv sp)) by (unfold E; rewrite ev_EB_app by (rewrite Hjs; lia); exact E62).
    assert (E63 : ev E 63 = Z_to_bv 64 (XQv sp)).
    { unfold E. replace 63%nat with (16 + 47)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 47), app_nth2, Hjs, Nat.sub_diag by lia. exact W0. }
    assert (E64 : ev E 64 = Z_to_bv 64 (PBv sp)).
    { unfold E. replace 64%nat with (16 + 48)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 48), app_nth2, Hjs by lia. replace (48 - 47)%nat with 1%nat by reflexivity. exact W1. }
    rewrite E62', E63, E64, !u_small by lia. repeat split; reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s9_re : forall a tid c pl js p8 sb p10 p12 p15 R M mdl, length js = 47%nat ->
    ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR25a KN25a L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ WSW) SRrW KNrW L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl Hjs E62 HB.
    assert (LEN : length (VB' a tid c pl js) = 63%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
    unfold XLO, XHI, CSH in *.
    destruct (re_facts a tid c pl js WSW Hjs E62 eq_refl eq_refl) as (V62 & E63 & E64 & V63 & V64).
    set (E := EB' a tid c pl (js ++ WSW)) in *.
    assert (Hlo : 0x7fff80000000 <= bv_unsigned (ev E 62)) by lia.
    assert (Hhi : bv_unsigned (ev E 62) <= 2 ^ 47) by lia.
    assert (Hal : bv_unsigned (ev E 62) mod 4096 = 0) by (rewrite V62; exact X1).
    assert (XQE : xq E 62 = XQv sp) by (unfold xq, XQv; rewrite V62; reflexivity).
    unfold KNrW.
    apply (bs_fresh2 sp brk mbase draw lim inp _ _ a tid c pl js SR25a KN25a L24 _ _ R M mdl WSW SRrW KF_W HB);
      rewrite ?LEN; [vmeq_refl | vmeq_refl | vmeq_refl | |].
    - intros HR'. fold E in HR' |- *. rewrite <- SRrW_eq. unfold sr_upds, RD_W. cbn [fold_left fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
      assert (NZr : forall r : reg, In r [10; 12; 13]%bv -> r <> 0%bv)
        by (intros r Hr X; subst r; cbn in Hr; repeat (destruct Hr as [Hr|Hr]; [apply (f_equal bv_unsigned) in Hr; discriminate Hr|]); exact Hr).
      eapply (regs_ok_upd1 E _ R R 13%bv); [ | apply NZr; cbn; tauto | | intros; reflexivity ].
      1: eapply (regs_ok_upd1 E _ R R 12%bv); [ | apply NZr; cbn; tauto | | intros; reflexivity ].
      1: eapply (regs_ok_upd1 E _ R R 10%bv); [ exact HR' | apply NZr; cbn; tauto | | intros; reflexivity ].
      all: rewrite HR'; apply bv_eq.
      + change (bv_unsigned (edenot E (EAlu ALU_ADD (XQ 62) (ELit 2147450880))) = bv_unsigned (edenot E (EAlu ALU_ADD (EVar 63) (ELit 2147450880)))).
        rewrite (xq_add E 62 Hlo Hhi Hal), lin1_val, XQE, V63 by lia. reflexivity.
      + change (bv_unsigned (edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (XQ 62)) (YQ 62)) (ELit 1))) = bv_unsigned (edenot E (ELit 1048576))).
        rewrite (s0_val E 62 Hlo Hhi Hal). reflexivity.
      + change (bv_unsigned (edenot E (XQ 62)) = bv_unsigned (ev E 63)). rewrite (xq_val E 62 Hlo Hhi), XQE, V63. reflexivity.
    - fold E. unfold KF_W, XLO, XHI, CSH. constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]; cbn [kentry_ok].
      + change (edenot E (EVar 63)) with (ev E 63). rewrite V63. split; [lia | exact X7].
      + change (edenot E (EVar 63)) with (ev E 63). rewrite V63. lia.
      + change (edenot E (EVar 64)) with (ev E 64). rewrite V64. split; [lia | exact X10].
      + change (edenot E (EVar 64)) with (ev E 64). rewrite V64. lia.
  Qed.
  #[using="usp"] Lemma p10_factsG : forall L pre H A a tid c pl js sr kn hc lz R M mdl p10,
    l_maps L = pre ++ l_maps L20 ->
    bootS' H A a tid c pl js sr kn L hc lz R M mdl -> ev (EB' a tid c pl js) 36 = p10 ->
    bv_unsigned p10 + N_PA <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p10.
  Proof.
    intros L pre H A a tid c pl js sr kn hc lz R M mdl p10 HL HB E36.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (EV36 : edenot (EB' a tid c pl js) (EVar 36) = p10) by exact E36.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. rewrite HL in AP. unfold dl in AP. rewrite List.map_app in AP. apply ivs_apart_app_r in AP.
    fold (dl (EB' a tid c pl js) (l_maps L20)) in AP.
    unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP.
    cbn [l_maps dl List.map fst snd ivs_apart] in AP. rewrite EV36 in AP. destruct AP as (_ & _ & AP & _).
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *.
    unfold N_PA, SHB_HI in *. rewrite !u_small in X2 by lia. lia.
  Qed.

  #[using="sp usp"] Lemma HI_in_LZ24 : forall p8 sb p10 p15,
    SHB_HI <= bv_unsigned p8 -> bv_unsigned p8 <= bv_unsigned sb ->
    (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15) ->
    In (HI_A, HI_N) (LZ24 p8 sb p10 p15).
  Proof.
    intros p8 sb p10 p15 H8 Hsb H15. pose proof HI_A_val as VA. pose proof HI_N_val as VN. unfold SHB_HI in *.
    unfold LZ24. apply maps_subtract_keeps; [lia | rewrite VN; lia | | rewrite VA, VN; lia].
    unfold LZ18. right. unfold LZ17. apply maps_subtract_keeps; [lia | rewrite VN; lia | | rewrite VA, VN; unfold RI; lia].
    unfold LZ16. right. unfold LZ5. left. reflexivity.
  Qed.

  #[using="sp usp"] Lemma page_base_in : forall (x : word) lo n, lo mod 4096 = 0 -> n mod 4096 = 0 -> lo <= bv_unsigned x < lo + n ->
    lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= lo + n.
  Proof.
    intros x lo n Hlo Hn Hx. pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
    pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
    rewrite u_small by lia. pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)). nia.
  Qed.

  #[using="sp usp"] Lemma hc6_zero_or_apart : forall p8 p10 d m,
    17594333495296 <= bv_unsigned p8 -> (bv_unsigned p10 + 8388608 <= 2201439137792 \/ 17594333495296 <= bv_unsigned p10) ->
    0x2008fff7000 <= d -> d + m <= 17594333495296 ->
    forall r, In r (hc6 p8 p10) -> snd r = Some (Z_to_bv 8 0) \/ snd (fst r) <= d \/ d + m <= fst (fst r).
  Proof.
    intros p8 p10 d m P2 P10 Hd Hm r Hr. unfold hc6, hc3, HC5 in Hr. cbn [In] in Hr.
    destruct Hr as [E|[E|[E|[E|[]]]]]; subst r; cbn [fst snd]; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, N_PA, SHB_HI, SHB_LO.
    all: try (left; reflexivity); right; lia.
  Qed.

  #[using="Type"] Lemma hhide_hcut : forall H d m, hhide (hcut H d m) d m = hhide H d m.
  Proof.
    intros H d m. apply functional_extensionality. intros x. unfold hhide, hcut.
    destruct (H x), (d <=? bv_unsigned x), (bv_unsigned x <? d + m); reflexivity.
  Qed.

  #[using="Type"] Lemma in_kn_of_b : forall K kn, existsb (APC.kentry_eqb K) kn = true -> In K kn.
  Proof. intros K kn Hb. apply existsb_exists in Hb as (k & Hk & He). apply KNA.kentry_eqb_eq in He. subst k. exact Hk. Qed.

  #[using="Type"] Lemma off_img : forall x : word, IMG_HI <= bv_unsigned x -> find_segment SEGS (bv_unsigned x) 1 = None.
  Proof.
    intros x Hx. exact (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                        ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy) x ltac:(apply Z.leb_le; exact Hx)).
  Qed.

  (* [comment removed for export] *)
  #[using="sp usp"] Lemma kwr_defined : forall E H M kn b k len (x : word),
    know_ok SEGS E (mrestrict H M) kn -> In (KWr (SA b k) (ELit len)) kn -> 0 <= len < 2 ^ 64 ->
    bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + len -> IMG_HI <= bv_unsigned x ->
    H x = false -> M x <> None.
  Proof.
    intros E H M kn b k len x HK Hin Hlen Hx Himg Hh.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KO. cbn [kentry_ok] in KO. destruct KO as [Hfl Hst].
    unfold flat, estart, elenZ in Hfl, Hst. cbn [a_base a_off edenot] in Hfl, Hst. rewrite u_small in Hfl, Hst by lia.
    pose proof (Hst 0 (Z.to_nat len) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as ST. rewrite Z.add_0_r in ST.
    assert (W0 : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) + Z.of_nat (Z.to_nat len) <= 2 ^ 64). { rewrite u_small by lia. rewrite Z2Nat.id by lia. lia. }
    pose proof (store_ok_all SEGS _ _ _ W0 ST x) as W. rewrite u_small, Z2Nat.id in W by lia. specialize (W ltac:(lia)).
    unfold wview, mrestrict in W. rewrite Hh in W. rewrite (off_img x Himg) in W. destruct (M x); [discriminate | exact W].
  Qed.

  (* [comment removed for export] *)
  #[using="brk mbase VI VE usp"] Lemma H8_visible_defined : forall a tid c pl js p8 sb p10 p12 kn M (x : word),
    know_ok SEGS (EB' a tid c pl js) (mrestrict (H8 sp p8 sb p10 p12) M) kn ->
    ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned sb = SBV p8 ->
    SHB_HI <= bv_unsigned p8 -> bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= bv_unsigned sp - stack_max_size -> IMG_HI <= bv_unsigned p12 -> bv_unsigned p12 + 65536 <= bv_unsigned sp - stack_max_size ->
    (bv_unsigned p10 + N_PA <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p10) ->
    In (KWr (SA (EAlu ALU_SRL (EVar 38) (ELit 3)) 2147450880) (ELit 8192)) kn ->
    In (KWr (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 29) (ELit 137438953472)) (ELit 3)) 2147450880) (ELit 512)) kn ->
    In (KWr (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-800))) (ELit 3)) 2147450880) (ELit 39)) kn ->
    0x2008fff7000 <= bv_unsigned x < SHB_HI -> H8 sp p8 sb p10 p12 x = false -> M x <> None.
  Proof.
    intros a tid c pl js p8 sb p10 p12 kn M x HK E29 E38 Hsb P2 P3 Q2 Q3 P10 I38 I29 I0 Hx Hh.
    pose proof SLo' as SLo. pose proof SHi' as SHi. unfold SHB_HI, IMG_HI, N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, stack_max_size, SBV in *.
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    assert (Himg : IMG_HI <= bv_unsigned x) by (unfold IMG_HI; lia).
    pose proof Hh as Hh8. unfold H8 in Hh. unfold hcut in Hh. apply andb_false_iff in Hh as [Hh|Hin].
    2:{ (* [comment removed for export] *) apply negb_false_iff in Hin. apply andb_prop in Hin as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
        eapply (kwr_defined _ _ M kn _ _ 39 x HK I0); [lia | | exact Himg | exact Hh8].
        rewrite (shx_val_gen _ 0 (-800)) by (rewrite ev_EB_sp; lia). rewrite ev_EB_sp. unfold SHK in A1, A2. replace (bv_unsigned sp + -800) with (bv_unsigned sp - 800) by lia. lia. }
    unfold H7, hcut in Hh. apply andb_false_iff in Hh as [Hh|Hin].
    2:{ apply negb_false_iff in Hin. apply andb_prop in Hin as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
        eapply (kwr_defined _ _ M kn _ _ 8192 x HK I38); [lia | | exact Himg | exact Hh8].
        rewrite shx_val0. change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38). rewrite E38. unfold SH12 in A1, A2. lia. }
    unfold H6, hjoin in Hh. apply orb_false_iff in Hh as [Hh _].
    unfold H5, hcut in Hh. apply andb_false_iff in Hh as [Hh|Hin].
    2:{ apply negb_false_iff in Hin. apply andb_prop in Hin as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
        eapply (kwr_defined _ _ M kn _ _ 512 x HK I29); [lia | | exact Himg | exact Hh8].
        rewrite (shx_val _ 29 137438953472) by (change (ev (EB sp draw inp a tid c pl js) 29) with (ev (EB' a tid c pl js) 29); rewrite ?E29; lia).
        change (ev (EB sp draw inp a tid c pl js) 29) with (ev (EB' a tid c pl js) 29). rewrite E29. unfold SHRI, RI in A1, A2. change (2 ^ 37) with 137438953472 in A1, A2. lia. }
    unfold H4, hcut in Hh. apply andb_false_iff in Hh as [Hh|Hin].
    2:{ apply negb_false_iff in Hin. apply andb_prop in Hin as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. unfold RI in A1, A2. exfalso. lia. }
    unfold H3, hjoin in Hh. apply orb_false_iff in Hh as [Hh _]. rewrite H2_in in Hh; [discriminate|]. unfold SHB_LO, SHB_HI. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s9_stack : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K, 2 ^ 25 <= lim -> length js = 55%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    bv_unsigned sb = SBV p8 -> (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15) ->
    ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SRrW KNrW L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H9a sp p8 sb p10 p12) (A9a sp sb p12) a tid c pl (js ++ junk_c R' memset_clob) SR27i KN27i L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 RET26) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K Hlim Hjs E28 E29 E36 E38 Hsb AP15 E63 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 71%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15). unfold XLO, XHI, CSH in *.
    pose proof (p8_factsG sp brk mbase draw lim inp L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (p10_factsG L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E36) as P10.
    pose proof (p12_factsG sp brk mbase draw lim inp L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    pose proof (shk_facts sp SA16' SLo' SHi') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
    assert (E63v : bv_unsigned (edenot (EB sp draw inp a tid c pl js) (EVar 63)) = XQv sp).
    { change (edenot _ (EVar 63)) with (ev (EB' a tid c pl js) 63). rewrite E63. apply u_small. lia. }
    pose proof (rdown_facts (XQv sp + 2147450880) ltac:(lia)) as [R1 R2].
    destruct (bs_expose_wr sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SRrW KNrW L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl
                (EVar 63) 2147450880 1048576 (HWLO sp) 1052672 0x2008fff7000 17594333495296 HB) as [HB1 _]; rewrite ?E63v; unfold HWLO, CSH.
    - exact R2.
    - reflexivity.
    - clear; lia.
    - clear - R1 X8. lia.
    - clear - R1 X9 SLo. unfold stack_max_size. lia.
    - clear - R1. lia.
    - clear; lia.
    - clear - R1. lia.
    - intros x Hx Hh. destruct HB as [_ HKN _ _ _ _ _ _ _ _ _ _].
      eapply (H8_visible_defined a tid c pl js p8 sb p10 p12 KNrW M x HKN E29 E38 Hsb); try assumption; try (clear - X8 X9 Hx; unfold SHB_HI; lia).
      + apply in_kn_of_b. vmeq_refl.
      + apply in_kn_of_b. vmeq_refl.
      + apply in_kn_of_b. vmeq_refl.
    - unfold hc6, hc3, HC5, SHB_HI. cbn [In]. do 2 right. left. reflexivity.
    - clear - X8. lia.
    - clear - X9. lia.
    - cbn [l_eager L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop A_bytes A8 A7 A5 fst snd].
      assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
      { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
      clear - Hlim Y8 B12. lia.
    - rewrite E63v in HB1.
      change (KWr {| a_base := EVar 63; a_off := 2147450880 |} (ELit 1048576) :: kn_keep MGrow KNrW KNrW (EVar 63) 2147450880 (ELit 1048576)) with (xpose_sw KNrW) in HB1.
      rewrite KN26x_eq in HB1.
      pose proof (cross_musl_memset_cc sp brk mbase draw lim inp VI VE memset_clob 0%nat (hcut (H8 sp p8 sb p10 p12) (XQv sp + 2147450880) 1048576)
                  ((HWLO sp, HWLO sp + 1052672) :: A8 sp sb p12) a tid c pl js SRrW KN26x L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl
                  (EVar 63) 2147450880 0%nat 2147450880 1048576 0 1048576 RET26 (EVar 63) 2147450880 1048576 K HB1) as X.
      cbv zeta in X. rewrite LEN, E63v in X. apply X; clear X.
      + reflexivity.
      + clear - X8. lia.
      + clear. lia.
      + clear. lia.
      + clear. lia.
      + intros r Hr. exact Hr.
      + cbn. intros Hx0. repeat (destruct Hx0 as [Hx0|Hx0]; [discriminate|]). exact Hx0.
      + unfold memset_clob. repeat (constructor; [cbn; intros Hx0; repeat (destruct Hx0 as [Hx0|Hx0]; [discriminate|]); exact Hx0|]). constructor.
      + vmeq_refl.
      + vmeq_refl.
      + vmeq_refl.
      + reflexivity.
      + vmeq_refl.
      + vmeq_refl.
      + clear. lia.
      + replace (sr_get SRrW 12%bv) with (ELit 1048576) by (vmeq_refl). reflexivity.
      + clear. lia.
      + vmeq_refl.
      + apply bv_eq. vmeq_refl.
      + vmeq_refl.
      + clear. lia.
      + clear. lia.
      + clear. lia.
      + clear - X8. lia.
      + clear - X9 SHi SLo. lia.
      + intros R' M' mdl' HB' _ Hfi.
        assert (E63' : bv_unsigned (edenot (EB sp draw inp a tid c pl (js ++ junk_c R' memset_clob)) (EVar 63)) = XQv sp).
        { change (edenot _ (EVar 63)) with (ev (EB' a tid c pl (js ++ junk_c R' memset_clob)) 63). rewrite ev_EB_app by (rewrite Hjs; lia). rewrite E63. apply u_small. lia. }
        pose proof (bs_hide sp brk mbase draw lim inp VI VE 1%nat _ _ a tid c pl (js ++ junk_c R' memset_clob) _ _ L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R' M' mdl'
                      (XQv sp + 2147450880) 1048576 (ELit 0x2008fff7000) 0xdfff0001000 (EVar 63) 2147450880 1048576 HB') as Y.
        cbv zeta in Y. rewrite E63' in Y. rewrite skipn_cons, !skipn_O, !edenot_lit in Y. rewrite u_small in Y by (clear; lia).
        change 2147450880 with CSH in Y. change 1048576 with NSW in Y. rewrite hhide_hcut, KN26m_eq, KN27i_eq, SR27i_eq in Y. unfold CSH, NSW in Y. apply HK.
        unfold H9a, A9a, CSH, NSW. change (2 ^ 20 + 4096) with 1052672. change (2 ^ 20) with 1048576. apply Y; clear Y.
        * unfold IMG_HI. clear - X8. lia.
        * clear. lia.
        * clear - X9 SLo. unfold stack_max_size. lia.
        * exact Hfi.
        * apply (hc6_zero_or_apart p8 p10 _ _); [unfold SHB_HI in P2; exact P2 | unfold N_PA, SHB_HI in P10; exact P10 | clear - X8; lia | clear - X9; lia].
        * cbn [app l_maps L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop List.tl]. repeat (try (left; reflexivity); right).
        * clear - X8. lia.
        * clear - X9. lia.
        * intros x Hx. apply (proj2 (page_in_ranges_true _ _)). exists (HI_A, HI_N). split; [apply HI_in_LZ24; [exact P2 | unfold SBV in Hsb; clear - Hsb MP; lia | exact AP15] |].
          cbn [fst snd]. rewrite HI_A_val, HI_N_val. unfold page_size.
          exact (page_base_in x 2201439137792 15392894357504 eq_refl eq_refl ltac:(clear - Hx X8 X9; lia)).
        * clear - X8. lia.
        * clear. lia.
        * clear. lia.
        * clear. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s9_b28W : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K,
    bootS' (H9a sp p8 sb p10 p12) (A9a sp sb p12) a tid c pl js SR27i KN27i L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H9a sp p8 sb p10 p12) (A9a sp sb p12) a tid c pl js SR28W KN28W L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memset) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET26) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K HB HK.
    rg_block VI VE HB HK run28W_eq car28W_eq.
  Qed.
  #[using="VI VE usp"] Theorem s9_tls : forall sr kn knx knm srm ret a tid c pl js p8 sb p10 p12 p15 R M mdl K, 2 ^ 25 <= lim ->
    length js = 61%nat ->
    xpose_tls kn = knx -> mset_tls knx = knm -> sr_after_call_c sr memset_clob 77 = srm ->
    sr_vars_lt 77 sr = true -> kn_vars_lt 77 kn = true -> kn_vars_lt 77 knx = true ->
    sr_get sr 10%bv = ELit TSHL -> sr_get sr 11%bv = ELit 0 -> sr_get sr 12%bv = TLS_A2X -> sr_get sr 1%bv = ELit ret -> ret_ok (Z_to_bv 64 ret) ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned sb = SBV p8 ->
    bootS' (H9a sp p8 sb p10 p12) (A9a sp sb p12) a tid c pl js sr kn L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl (js ++ junk_c R' memset_clob) srm knm L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros sr kn knx knm srm ret a tid c pl js p8 sb p10 p12 p15 R M mdl K Hlim Hjs HXp HMs HSr Hsr Hkn Hknx S10 S11 S12 S1 Hret E28 E36 E38 Hsb HB HK.
    assert (LEN : length (VB' a tid c pl js) = 77%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15). unfold XLO, XHI, CSH in *.
    assert (T4 : bv_unsigned a = A_builtin_tls) by (destruct HB as [_ _ _ _ _ _ _ _ _ HT _ _]; exact (proj2 (proj2 (proj2 HT)))).
    pose proof (p8_factsG sp brk mbase draw lim inp L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (p12_factsG sp brk mbase draw lim inp L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia_p)) as MP.
    (* The TLS block is builtin_tls: its shadow window and shadow page are constants. *)
    assert (TSHc : TSH a = 2148221982) by (unfold TSH, CSH; rewrite T4; reflexivity).
    assert (TPGc : TPG a = 2148220928) by (unfold TPG; rewrite TSHc; reflexivity).
    assert (G3 : TPG a mod 4096 = 0) by (rewrite TPGc; reflexivity).
    assert (TSHv : bv_unsigned (edenot (EB' a tid c pl js) (ELit 0)) + TSHL = TSH a) by (rewrite TSHc; reflexivity).
    assert (TSHLc : TSHL = 2148221982) by reflexivity.
    unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_LO, SHB_HI, stack_max_size, IMG_HI, SBV in *.
    assert (HID : forall x : word, TSH a <= bv_unsigned x < TSH a + 60 -> H9a sp p8 sb p10 p12 x = true).
    { intros x Hx. rewrite TSHc in Hx. unfold H9a. apply hhide_old. unfold H8, H7, H6, H5, H4, H3.
      apply (proj2 (hcut_true _ _ _ _)). split.
      2:{ left. unfold SHK. pose proof (Z.div_le_mono (0x7fff80000000 - 800) (bv_unsigned sp - 800) 8 ltac:(lia_p) ltac:(unfold usp in *; lia_p)) as DL.
          change ((0x7fff80000000 - 800) / 8) with 17591917608860 in DL. lia_p. }
      apply (proj2 (hcut_true _ _ _ _)). split.
      2:{ left. unfold SH12. pose proof (Z.div_le_mono 6303744 (bv_unsigned p12) 8 ltac:(lia_p) ltac:(lia_p)) as DL. change (6303744 / 8) with 787968 in DL. lia_p. }
      apply hjoin_old. apply (proj2 (hcut_true _ _ _ _)). split.
      2:{ left. unfold SHRI, RI. pose proof (Z.div_le_mono (2 ^ 37) (bv_unsigned sb + 2 ^ 37) 8 ltac:(lia_p) ltac:(lia_p)) as DL. change (2 ^ 37 / 8) with 17179869184 in DL. lia_p. }
      apply (proj2 (hcut_true _ _ _ _)). split; [| unfold RI; lia_p].
      apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI. lia_p. }
    assert (A2v : edenot (EB' a tid c pl js) TLS_A2X = Z_to_bv 64 60) by reflexivity.
    pose proof (p12_factsG sp brk mbase draw lim inp L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (_ & _ & _ & Q4' & _).
    destruct (bs_expose_wr sp brk mbase draw lim inp VI VE (H9a sp p8 sb p10 p12) (A9a sp sb p12) a tid c pl js sr kn L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
                (ELit 0) TSHL 60 (TPG a) 4096 2147446784 (2147446784 + 2 ^ 28) HB) as [HB1 _];
      rewrite ?TSHv; [arith_lia | | arith_lia | arith_lia | | arith_lia | arith_lia | arith_lia | | | | | | ].
    - reflexivity.
    - unfold usp, stack_max_size in *. lia_p.
    - intros x Hx0 Hh. rewrite (HID x Hx0) in Hh. discriminate.
    - unfold hc6, hc3, HC5. cbn [In]. unfold SHB_LO, SHB_HI. do 3 right; left; reflexivity.
    - lia_p.
    - lia_p.
    - cbn [l_eager L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop]. unfold A9a. cbn [A_bytes A8 A7 A5 fst snd].
      pose proof (shk_facts sp SA16' SLo' SHi') as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
      assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
      { clear - Q1 Q4' Q2 Q3 SHi. destruct Q4' as [HL|HH]; [pose proof (sh12_L p12 Q1 ltac:(unfold IMG_HI; lia_p) HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia_p))]; lia_p. }
      unfold NSW. clear - Hlim Y8 B12. lia_p.
    - change (KWr {| a_base := ELit 0; a_off := TSHL |} (ELit 60) :: kn_keep MGrow kn kn (ELit 0) TSHL (ELit 60)) with (xpose_tls kn) in HB1.
      rewrite HXp, TSHv in HB1. unfold H9, A9.
      pose proof (cross_musl_memset_cc sp brk mbase draw lim inp VI VE memset_clob 0%nat (hcut (H9a sp p8 sb p10 p12) (TSH a) 60) ((TPG a, TPG a + 4096) :: A9a sp sb p12) a tid c pl js sr knx L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
                    (ELit 0) TSHL 0%nat TSHL 60 0 60 ret (ELit 0) TSHL 60 K HB1) as X.
      cbv zeta in X. rewrite LEN, TSHv in X. apply X; clear X; try reflexivity; try arith_lia.
      + intros r Hr. exact Hr.
      + cbn. intros Hx0. repeat (destruct Hx0 as [Hx0|Hx0]; [discriminate|]). exact Hx0.
      + unfold memset_clob. repeat (constructor; [cbn; intros Hx0; repeat (destruct Hx0 as [Hx0|Hx0]; [discriminate|]); exact Hx0|]). constructor.
      + exact Hsr.
      + exact Hknx.
      + rewrite S10. reflexivity.
      + exact S11.
      + rewrite S12. exact A2v.
      + exact S1.
      + exact Hret.
      + rewrite <- HXp. reflexivity.
      + intros R' M' mdl' HB' _ _. apply HK. rewrite <- HMs, <- HSr. unfold mset_tls. cbn [skipn] in HB'. exact HB'.
  Qed.
  (* [comment removed for export] *)
  Definition at_E18 (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 : word) (js : list word) R M mdl : Prop :=
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR_E18A KN_E18 L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp).

  #[using="VI VE"] Theorem s9_b29W : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15) ->
    ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) -> ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) -> ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp) ->
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR28Wm KN28Wm L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', at_E18 a tid c pl p8 sb p10 p12 p15 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET28W) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K Hsb E28 E29 E36 E38 AP15 E62 E63 E64 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR_E18A KN_E18 L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [exact HB' | repeat split; assumption]. }
    clear HK. rg_block VI VE HB HK' run29W_eq car29W_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s9 : forall a tid c pl p8 sb p10 p12 p15 js R M mdl K, 2 ^ 25 <= lim -> length js = 46%nat ->
    at_E16r' a tid c pl p8 sb p10 p12 p15 js R M mdl ->
    (forall ks R' M' mdl', length ks = 21%nat -> at_E18 a tid c pl p8 sb p10 p12 p15 (js ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_munmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 js R M mdl K Hlim Hjs HE HK. pose proof HE as (HB0 & Hsb & E28 & E29 & E36 & E38 & AP15).
    apply (s9_b24a a tid c pl js p8 sb p10 p12 p15 R M mdl K HB0). intros R1 M1 m1 H1.
    pose proof (s9_fresh a tid c pl js p8 sb p10 p12 p15 R1 M1 m1 Hjs H1) as H1f.
    set (js1 := js ++ [Z_to_bv 64 (STv sp)]) in *.
    assert (L1 : length js1 = 47%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    assert (E62 : ev (EB' a tid c pl js1) 62 = Z_to_bv 64 (STv sp)).
    { unfold js1. replace 62%nat with (16 + 46)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 46), app_nth2, Hjs by lia. reflexivity. }
    assert (F1 : ev (EB' a tid c pl js1) 28 = p8 /\ ev (EB' a tid c pl js1) 29 = sb /\ ev (EB' a tid c pl js1) 36 = p10 /\ ev (EB' a tid c pl js1) 38 = p12).
    { unfold js1. rewrite !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    destruct F1 as (F28 & F29 & F36 & F38).
    apply (s9_b25a a tid c pl js1 p8 sb p10 p12 p15 R1 M1 m1 K E62 H1f). intros R2 M2 m2 H2.
    assert (LJ : forall R0, length (junk_c R0 memset_clob) = 6%nat) by (intros; reflexivity).
    pose proof (s9_re a tid c pl js1 p8 sb p10 p12 p15 R2 M2 m2 L1 E62 H2) as H3.
    destruct (re_facts a tid c pl js1 WSW L1 E62 eq_refl eq_refl) as (V62 & E63 & E64 & _ & _).
    set (js2 := js1 ++ WSW) in *.
    assert (L2 : length js2 = 55%nat) by (unfold js2, WSW; rewrite !length_app, L1; reflexivity).
    assert (G : ev (EB' a tid c pl js2) 28 = p8 /\ ev (EB' a tid c pl js2) 29 = sb /\ ev (EB' a tid c pl js2) 36 = p10 /\ ev (EB' a tid c pl js2) 38 = p12
                /\ ev (EB' a tid c pl js2) 62 = Z_to_bv 64 (STv sp)).
    { unfold js2. rewrite !ev_EB_app by (rewrite L1; lia). repeat split; assumption. }
    destruct G as (G28 & G29 & G36 & G38 & G62).
    apply (s9_stack a tid c pl js2 p8 sb p10 p12 p15 R2 M2 m2 K Hlim L2 G28 G29 G36 G38 Hsb AP15 E63 H3). intros R4 M4 m4 Hc.
    set (js3 := js2 ++ junk_c R4 memset_clob) in *.
    assert (L3 : length js3 = 61%nat) by (unfold js3; rewrite length_app, L2, LJ; reflexivity).
    assert (G' : ev (EB' a tid c pl js3) 28 = p8 /\ ev (EB' a tid c pl js3) 29 = sb /\ ev (EB' a tid c pl js3) 36 = p10 /\ ev (EB' a tid c pl js3) 38 = p12
                /\ ev (EB' a tid c pl js3) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js3) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js3) 64 = Z_to_bv 64 (PBv sp)).
    { unfold js3. rewrite !ev_EB_app by (rewrite L2; lia). repeat split; assumption. }
    destruct G' as (I28 & I29 & I36 & I38 & I62 & I63 & I64).
    apply (s9_b28W a tid c pl js3 p8 sb p10 p12 p15 R4 M4 m4 K Hc). intros R5 M5 m5 Hd.
    apply (s9_tls SR28W KN28W KN28Wx KN28Wm SR28Wm RET28W a tid c pl js3 p8 sb p10 p12 p15 R5 M5 m5 K Hlim L3 KN28Wx_eq KN28Wm_eq SR28Wm_eq
             ltac:(vmeq_refl) ltac:(vmeq_refl) ltac:(vmeq_refl)
             ltac:(vmeq_refl) ltac:(vmeq_refl) ltac:(vmeq_refl) ltac:(vmeq_refl)
             ltac:(apply bv_eq; vmeq_refl) I28 I36 I38 Hsb Hd). intros R6 M6 m6 Hf.
    set (js4 := js3 ++ junk_c R6 memset_clob) in *.
    assert (G3 : ev (EB' a tid c pl js4) 28 = p8 /\ ev (EB' a tid c pl js4) 29 = sb /\ ev (EB' a tid c pl js4) 36 = p10 /\ ev (EB' a tid c pl js4) 38 = p12
                /\ ev (EB' a tid c pl js4) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js4) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js4) 64 = Z_to_bv 64 (PBv sp)).
    { unfold js4. rewrite !ev_EB_app by (rewrite L3; lia). repeat split; assumption. }
    destruct G3 as (N28 & N29 & N36 & N38 & N62 & N63 & N64).
    apply (s9_b29W a tid c pl js4 p8 sb p10 p12 p15 R6 M6 m6 K Hsb N28 N29 N36 N38 AP15 N62 N63 N64 Hf). intros R7 M7 m7 Hg.
    apply (HK ((([Z_to_bv 64 (STv sp)] ++ WSW) ++ junk_c R4 memset_clob) ++ junk_c R6 memset_clob) R7 M7 m7).
    - rewrite !length_app, !LJ. reflexivity.
    - unfold js4, js3, js2, js1 in Hg. rewrite <- !app_assoc in Hg. rewrite <- !app_assoc. exact Hg.
  Qed.
End Theorems.
