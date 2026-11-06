From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm SlotAgree SlotAgreeV.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PInvCF UCut PSlotCF.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free run of the ubsan slot from its entry (UEntry.v with Hcut_o -> PInvCF.Hcut_cf): the front (E, A, B,
   C), the walk and the tail, chained through the cuts of UCut.v. The cut-free glue lemmas are the hypotheses; each
   is its original's statement with Hcut_o -> Hcut_cf and UGlueT.HCT -> HCT_cf, written here as Hcut_cf with no
   output (fun _ => []), the same proposition. *)

Section ECF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* UGlueR7.ug_R7. *)
Hypothesis ug_R7_cf : Hcut_cf B APIf ra (Inv_K1310c B APIf ra empty) (fun _ => []).
(* UGlueT.ug_tail. *)
Hypothesis ug_tail_cf : Hcut_cf B APIf ra (Inv_K1310c B APIf ra empty) (fun _ => []) ->
  Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0.
(* UGlueW.ug_K12e3c. *)
Hypothesis ug_K12e3c_cf : Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0 ->
  Hcut_cf B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24).
(* UGlueF.ug_C. *)
Hypothesis ug_C_cf : Hcut_cf B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24) ->
  Hcut_cf B APIf ra (Inv_K12e14 B APIf ra empty) (fun g => uwalk g 24 ++ uC0 g).
(* UGlueF.ug_B. *)
Hypothesis ug_B_cf : Hcut_cf B APIf ra (Inv_K12e14 B APIf ra empty) (fun g => uwalk g 24 ++ uC0 g) ->
  Hcut_cf B APIf ra (Inv_K1310c B APIf ra empty) (fun _ => []) ->
  Hcut_cf B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)).
(* UGlueA.ug_A. *)
Hypothesis ug_A_cf : Hcut_cf B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)) ->
  Hcut_cf B APIf ra (Inv_K12d28 B APIf ra empty) (fun g => PW.OUT (g_in g)).
(* UGlueE.ug_E. *)
Hypothesis ug_E_cf : Hcut_cf B APIf ra (Inv_K12d28 B APIf ra empty) (fun g => PW.OUT (g_in g)) ->
  Hcut_cf B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => PW.OUT (g_in g)).

(* From the cut after the first answer (0x12e04) to the end. *)
Lemma ue_K12e3c_cf : Hcut_cf B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24).
Proof. exact (ug_K12e3c_cf (ug_tail_cf ug_R7_cf)). Qed.

(* From the cut after the open (0x12d38) to the end. *)
Lemma ue_K12d70_cf : Hcut_cf B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof. exact (ug_B_cf (ug_C_cf ue_K12e3c_cf) ug_R7_cf). Qed.

(* The whole run from the entry. *)
Lemma ue_entry_cf : Hcut_cf B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof. exact (ug_E_cf (ug_A_cf ue_K12d70_cf)). Qed.

(* The cut-free slot contract (PSlotCF.slot_lib_cgo with f = PW.OUT) for a shape that writes PW.OUT. *)
Context {LS : lib_shape}.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HLIBK : forall pl fs K, @LIBK LS pl fs K = wr ch_stderr (PW.OUT pl) (K (LL 0 fs (PW.OUT pl))).
Hypothesis HDELTA : forall n b, @lib_delta LS n b = b.
Hypothesis HROOM : forall b n, @lib_room LS b n ->
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Lemma ue_slot_cgo : forall j,
  lib_contract_cgo (LS:=LS) B (APIf rc) PW.OUT frame_G frame_RELRO GI j ENTRY ra empty SLOT_STACK.
Proof.
  intros j. exact (slot_lib_cgo B APIf ra empty FF PW.OUT HLIBK HDELTA HROOM PW.OUT_big ue_entry_cf j).
Qed.

End ECF.
