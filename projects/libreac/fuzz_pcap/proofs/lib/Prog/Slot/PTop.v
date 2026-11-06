From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct
  pcap_source_struct_next pcap_source_open_c pcap_source_close_c pcap_source_next_c bcmp_c memcpy_c fclose_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_open pcap_source_close
  pcap_source_next libreac_fuzz_fopen fmemopen fclose fflush mseek mclose __unlist_locked_file __ofl_add
  __ofl_lock __ofl_unlock __lock __unlock strcmp strchr memset fread_ro memmove_ro memcpy bcmp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PWalkDef PWalk PCut PGlueD PLink.
From OSSVerify.libreac.fuzz_pcap Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* The top of the plain slot proof: the walk loop (seg_loop), the chain of the cuts from Inv_ENTRY (entry_holds),
   the callee contracts from their _holds lemmas, and Statements.plain_halts (plain_halts_holds_of_glue). *)

Section Top.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* The glue lemmas of the cuts (PCut.v), in the backward form: the run from a cut, given the runs from the next
   cuts. Their callee premises are the contracts of top_contracts. *)
Definition top_glue : Prop :=
  (Hcut_o B APIf ra (Inv_K1 B APIf ra empty) oOUT -> Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) oOUT) /\
  (Hcut_o B APIf ra (Inv_K2g B APIf ra empty) oOUT -> Hcut_o B APIf ra (Inv_K2r B APIf ra empty) oOUT ->
     Hcut_o B APIf ra (Inv_K1 B APIf ra empty) oOUT) /\
  (Hcut_o B APIf ra (Inv_K3 B APIf ra empty) oOUT -> Hcut_o B APIf ra (Inv_K2g B APIf ra empty) oOUT) /\
  (Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K2r B APIf ra empty) oOUT) /\
  (Hcut_o B APIf ra (Inv_KD B APIf ra empty) oKD -> Hcut_o B APIf ra (Inv_K3 B APIf ra empty) oOUT) /\
  (forall i p, 0 <= i ->
     Hcut_o B APIf ra
       (fun g => Inv_KL2 B APIf ra empty (i + 1) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g)
       (fun g => oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g) ->
     Hcut_o B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p)) /\
  (Hcut_o B APIf ra (Inv_K6 B APIf ra empty) out24 -> forall p, Hcut_o B APIf ra (Inv_K5 B APIf ra empty p) out24) /\
  (Hcut_o B APIf ra (Inv_K7 B APIf ra empty) out24 -> Hcut_o B APIf ra (Inv_K6 B APIf ra empty) out24) /\
  (Hcut_o B APIf ra (Inv_K8 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K7 B APIf ra empty) out24) /\
  (Hcut_o B APIf ra (Inv_K9 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K8 B APIf ra empty) oNil) /\
  (Hcut_o B APIf ra (Inv_K10 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K9 B APIf ra empty) oNil) /\
  (Hcut_o B APIf ra (Inv_K11 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K10 B APIf ra empty) oNil) /\
  (Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K11 B APIf ra empty) oNil) /\
  Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil.

(* The callee contracts that the glue lemmas take. *)
Definition top_contracts : Prop :=
  (forall fx : YK11.FPState, @pcap_source_open_contract fx rc B (APIf rc)) /\
  (forall fx : YK11.FPState, @pcap_source_close_contract fx rc B (APIf rc)) /\
  (forall fx : YK11.FPState, @pcap_source_next_contract fx) /\
  bcmp_contract /\ memcpy_contract.

Hypothesis FF : frame_facts B APIf SH SK ra empty.

(* The walk loop: every loop head K4 i p runs to the end, by downward induction on the record index i. Each record
   takes 17 bytes or more of the file (24 + 17 i <= p, PCut.P_K4), and the file has less than 2^26 bytes (PInv.GV),
   so i < 2^22 at a loop head. *)
Lemma seg_loop :
  (forall i p, 0 <= i ->
     Hcut_o B APIf ra
       (fun g => Inv_KL2 B APIf ra empty (i + 1) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g)
       (fun g => oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g) ->
     Hcut_o B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p)) ->
  (forall p, Hcut_o B APIf ra (Inv_K5 B APIf ra empty p) out24) ->
  forall i p, 0 <= i -> Hcut_o B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p).
Proof.
  intros HL HK5.
  assert (D : forall k : nat, forall i p, 0 <= i -> 2 ^ 22 - Z.of_nat k <= i ->
            Hcut_o B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p)).
  { induction k as [|k IH]; intros i p Hi Hk.
    - intros g c (b & h & buf & km & fx' & L & A & regs & mem & md & _ & _ & HFR & _ & HP). exfalso.
      destruct HFR as ((Hgn & _) & _).
      destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HiP & HK & _).
      assert (Hq : p <= gq g p) by apply psn_q_ge.
      destruct (kind_fit (gsw g) (gF g) (gcap g) (gq g p) HK) as (_ & _ & _ & HQ & HI).
      assert (Hl : gn g <= g_n g) by (unfold gn, gF, g_n; destruct (g_in g); cbn [tl length]; lia).
      change (flen (gF g)) with (gn g) in HQ. lia.
    - apply HL; [exact Hi|]. intros g c HC.
      apply (seg_L2 B APIf ra empty FF i _ Hi); [apply IH; lia | apply HK5 | exact HC]. }
  intros i p Hi. apply (D (Z.to_nat (2 ^ 22 - i))); lia.
Qed.

(* The callee contracts, each from its _holds lemma down to lemmas without premises; the allocator's facts and the
   pinned symbols come from frame_facts. *)
Lemma top_contracts_holds : top_contracts.
Proof.
  destruct FF as (SEGS & _ & MPC & FPC & _ & _ & ERR & GUARD & GOTG & CTX & LOCK & LIBC & SIZEC & SMALLC & MEDC &
    DEBR & TP & ERRNO & _ & _ & _ & _ & _ & _ & _ & _ & _ & HALLOC & VML & DBL).
  pose proof (__ofl_lock.__ofl_lock_holds __lock.__lock_holds) as HOL.
  pose proof (__ofl_unlock.__ofl_unlock_holds __unlock.__unlock_holds) as HOU.
  assert (HFC : forall fx : YK11.FPState, @fclose_contract fx rc B (APIf rc)).
  { intros fx. destruct (HALLOC rc fx) as (_ & HFREE & HFREE0 & _ & _ & _ & _ & _ & _ & HBW & _ & _ & _ & HAX & _).
    exact (fclose.fclose_holds B (APIf rc) FPC GUARD GOTG CTX LOCK LIBC SIZEC SMALLC MEDC DEBR TP ERRNO VML DBL
      HFREE HFREE0 HAX HBW (fflush.fflush_holds mseek.mseek_holds) mclose.mclose_holds
      __unlist_locked_file.__unlist_locked_file_holds HOL HOU). }
  split; [|split; [|split; [|split]]].
  - intros fx. destruct (HALLOC rc fx) as (HMAL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNL & HAX & _).
    exact (pcap_source_open.pcap_source_open_holds B (APIf rc) (ERR rc) HAX
      (libreac_fuzz_fopen.libreac_fuzz_fopen_holds B (APIf rc) strcmp.strcmp_holds
        (fmemopen.fmemopen_holds B (APIf rc) SEGS MPC TP ERRNO CTX LOCK LIBC GOTG GUARD DEBR SIZEC SMALLC MEDC VML DBL
          HMAL HNL HAX strchr.strchr_holds memset.memset_holds (__ofl_add.__ofl_add_holds HOL HOU)))
      fread_ro.fread_ro_holds (HFC fx)).
  - intros fx. exact (pcap_source_close.pcap_source_close_holds B (APIf rc) (ERR rc) (HFC fx)).
  - intros fx. exact (pcap_source_next.pcap_source_next_holds fread_ro.fread_ro_holds
      (memmove_ro.memmove_ro_holds memcpy.memcpy_holds)).
  - exact bcmp.bcmp_holds.
  - exact memcpy.memcpy_holds.
Qed.

Section Chain.
Hypothesis seg_E : Hcut_o B APIf ra (Inv_K1 B APIf ra empty) oOUT ->
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) oOUT.
Hypothesis seg_A : Hcut_o B APIf ra (Inv_K2g B APIf ra empty) oOUT ->
  Hcut_o B APIf ra (Inv_K2r B APIf ra empty) oOUT -> Hcut_o B APIf ra (Inv_K1 B APIf ra empty) oOUT.
Hypothesis seg_B_good : Hcut_o B APIf ra (Inv_K3 B APIf ra empty) oOUT ->
  Hcut_o B APIf ra (Inv_K2g B APIf ra empty) oOUT.
Hypothesis seg_B_ref : Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K2r B APIf ra empty) oOUT.
Hypothesis seg_C : Hcut_o B APIf ra (Inv_KD B APIf ra empty) oKD -> Hcut_o B APIf ra (Inv_K3 B APIf ra empty) oOUT.
Hypothesis seg_L : forall i p, 0 <= i ->
  Hcut_o B APIf ra
    (fun g => Inv_KL2 B APIf ra empty (i + 1) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g)
    (fun g => oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g) ->
  Hcut_o B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p).
Hypothesis seg_W : Hcut_o B APIf ra (Inv_K6 B APIf ra empty) out24 ->
  forall p, Hcut_o B APIf ra (Inv_K5 B APIf ra empty p) out24.
Hypothesis seg_R1 : Hcut_o B APIf ra (Inv_K7 B APIf ra empty) out24 ->
  Hcut_o B APIf ra (Inv_K6 B APIf ra empty) out24.
Hypothesis seg_R2 : Hcut_o B APIf ra (Inv_K8 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K7 B APIf ra empty) out24.
Hypothesis seg_R3 : Hcut_o B APIf ra (Inv_K9 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K8 B APIf ra empty) oNil.
Hypothesis seg_R4 : Hcut_o B APIf ra (Inv_K10 B APIf ra empty) oNil -> Hcut_o B APIf ra (Inv_K9 B APIf ra empty) oNil.
Hypothesis seg_R5 : Hcut_o B APIf ra (Inv_K11 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K10 B APIf ra empty) oNil.
Hypothesis seg_R6 : Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K11 B APIf ra empty) oNil.
Hypothesis seg_R7 : Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil.

(* The chain of the cuts: the end (K12 .. K5), the walk (K4 0 24 by seg_loop), then KD .. ENTRY. *)
Lemma entry_holds : Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) oOUT.
Proof.
  pose proof (seg_W (seg_R1 (seg_R2 (seg_R3 (seg_R4 (seg_R5 (seg_R6 seg_R7))))))) as H5.
  pose proof (seg_D B APIf ra empty FF (seg_loop seg_L H5 0 24 ltac:(lia)) (H5 24)) as HD.
  exact (seg_E (seg_A (seg_B_good (seg_C HD)) (seg_B_ref seg_R7))).
Qed.

End Chain.

Lemma entry_of_glue : top_glue -> Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) oOUT.
Proof.
  intros (E & A & Bg & Br & C & L & W & R1 & R2 & R3 & R4 & R5 & R6 & R7).
  exact (entry_holds E A Bg Br C L W R1 R2 R3 R4 R5 R6 R7).
Qed.

End Top.

(* Statements.plain_halts from the glue lemmas: the callee contracts are discharged by top_contracts_holds, the
   output function is PWalk.OUT, which is [] on payloads of 2^26 bytes or more (OUT_big). *)
Theorem plain_halts_holds_of_glue :
  (forall (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
          (SH : sink_head) (SK : sink_syms) (ra empty : Z),
     frame_facts B APIf SH SK ra empty -> top_contracts B APIf -> top_glue B APIf ra empty) ->
  OSSVerify.libreac.fuzz_pcap.Statements.plain_halts.
Proof.
  intros HG. apply (plain_halts_of_entry_o OUT); [|exact OUT_big].
  intros fx rc B APIf SH SK ra empty FF _ _.
  exact (entry_of_glue B APIf ra empty FF (HG rc B APIf SH SK ra empty FF (top_contracts_holds B APIf ra empty FF))).
Qed.
