From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import fmemopen_cf_c fclose_cf_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require bcmp memcpy fread_ro memmove_ro strcmp
  pcap_source_open_cf pcap_source_close_cf pcap_source_next_cf libreac_fuzz_fopen_cf fmemopen_cf fclose_cf
  fflush mseek mclose __unlist_locked_file __ofl_lock __ofl_unlock __ofl_add __lock __unlock strchr memset.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PInvCF PTac PWalkDef PWalk PCut
  PContractCF PGlueECF PGlueACCF PGlueBCF PGlueDCF PGlueLCF PGlueRCF PGlueRNCF PSlotCF.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SlotAgreeV.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

Module PW := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.

(* The cut-free stdio contracts of the reader's calls (fmemopen, fclose), from their proofs and the frame's facts
   (UCall.uc_fmemopen / uc_fclose with the cut-free allocator contracts). *)
Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis MALCF : @malloc_contract_cf fx rc B (APIf rc).
Hypothesis FREECF : @free_contract_cf fx rc B (APIf rc).
Hypothesis FREE0CF : free_null_contract_cf (fx := fx) B.

Lemma utc_fclose_cf : @fclose_contract_cf fx rc B (APIf rc).
Proof.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (ALLOC rc fx) as (HMAL & HFREE & HFREE0 & _ & _ & _ & _ & _ & _ & HBW & _ & _ & _ & HAX & _).
  apply fclose_cf.fclose_cf_holds; try assumption.
  - apply fflush.fflush_holds. exact mseek.mseek_holds.
  - exact mclose.mclose_holds.
  - exact __unlist_locked_file.__unlist_locked_file_holds.
  - apply __ofl_lock.__ofl_lock_holds. exact __lock.__lock_holds.
  - apply __ofl_unlock.__ofl_unlock_holds. exact __unlock.__unlock_holds.
Qed.

Lemma utc_fmemopen_cf : @fmemopen_contract_cf fx rc B (APIf rc).
Proof.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (ALLOC rc fx) as (HMAL & HFREE & HFREE0 & _ & _ & _ & _ & _ & _ & HBW & _ & _ & HNL & HAX & _).
  apply fmemopen_cf.fmemopen_cf_holds; try assumption.
  - exact strchr.strchr_holds.
  - exact memset.memset_holds.
  - apply __ofl_add.__ofl_add_holds.
    + apply __ofl_lock.__ofl_lock_holds. exact __lock.__lock_holds.
    + apply __ofl_unlock.__ofl_unlock_holds. exact __unlock.__unlock_holds.
Qed.

End C.

(* The cut-free (agreement) slot of the fuzz_pcap plain build: the chain of the cut-free glue lemmas
   (PGlue*CF.v) from the entry, and lib_contract_cgo for every j with every callee contract discharged by its
   cut-free _holds theorem. The premises are the frame's own: frame_facts, the cut-free allocator contracts, the run
   limit law LIMLAW (SRC_LIM_MIN) and the agreement shape's LIBK / lib_delta / lib_room. *)

Section Chain.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis HFREECF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis HCLOSECF : forall fx : YK11.FPState, @pcap_source_close_contract_cf fx rc B (APIf rc).
Hypothesis HOPENCF : forall fx : YK11.FPState, @pcap_source_open_contract_cf fx rc B (APIf rc).
Hypothesis HNEXTCF : forall fx : YK11.FPState, @pcap_source_next_contract_cf fx.

(* The walk loop (PTop.seg_loop in the cut-free form). *)
Lemma seg_loop_cf :
  (forall i p, 0 <= i ->
     Hcut_cf B APIf ra
       (fun g => Inv_KL2 B APIf ra empty (i + 1) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g)
       (fun g => oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g) ->
     Hcut_cf B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p)) ->
  (forall p, Hcut_cf B APIf ra (Inv_K5 B APIf ra empty p) out24) ->
  forall i p, 0 <= i -> Hcut_cf B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p).
Proof.
  intros HL HK5.
  assert (D : forall k : nat, forall i p, 0 <= i -> 2 ^ 22 - Z.of_nat k <= i ->
            Hcut_cf B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p)).
  { induction k as [|k IH]; intros i p Hi Hk.
    - intros g c _ (b & h & buf & km & fx' & L & A & regs & mem & md & _ & _ & HFR & _ & HP). exfalso.
      destruct HFR as ((Hgn & _) & _).
      destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HiP & HK & _).
      assert (Hq : p <= gq g p) by apply psn_q_ge.
      destruct (kind_fit (gsw g) (gF g) (gcap g) (gq g p) HK) as (_ & _ & _ & HQ & HI).
      assert (Hl : gn g <= g_n g) by (unfold gn, gF, g_n; destruct (g_in g); cbn [tl length]; lia).
      change (flen (gF g)) with (gn g) in HQ. lia.
    - apply HL; [exact Hi|]. intros g c HCAP HC.
      apply (seg_L2_cf B APIf ra empty FF i _ Hi); [apply IH; lia | apply HK5 | exact HCAP | exact HC]. }
  intros i p Hi. apply (D (Z.to_nat (2 ^ 22 - i))); lia.
Qed.

(* The chain of the cuts (PTop.entry_holds in the cut-free form). *)
Lemma entry_cf : Hcut_cf B APIf ra (Inv_ENTRY B APIf ra empty) oOUT.
Proof.
  pose proof (seg_R7_cf B APIf ra empty FF) as R7.
  pose proof (seg_W_cf B APIf ra empty FF HCLOSECF (seg_R1_cf B APIf ra empty FF LIMLAW HOPENCF
    (seg_R2_cf B APIf ra empty FF HNEXTCF (seg_R3_cf B APIf ra empty FF HCLOSECF
      (seg_R4_cf B APIf ra empty FF HNEXTCF (seg_R5_cf B APIf ra empty FF HFREECF
        (seg_R6_cf B APIf ra empty FF HFREECF R7))))))) as H5.
  pose proof (seg_D_cf B APIf ra empty FF
    (seg_loop_cf (fun i p Hi H => seg_L_cf B APIf ra empty FF HNEXTCF i p Hi H) H5 0 24 ltac:(lia)) (H5 24)) as HD.
  exact (seg_E_cf B APIf ra empty FF HMALCF LIMLAW
    (seg_A_cf B APIf ra empty FF LIMLAW HOPENCF
      (seg_B_good_cf B APIf ra empty FF HMALCF LIMLAW (seg_C_cf B APIf ra empty FF HNEXTCF HD))
      (seg_B_ref_cf B APIf ra empty FF HFREECF R7))).
Qed.

End Chain.

Section Top.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis HFREECF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis HFREE0CF : forall fx' : YK11.FPState, free_null_contract_cf (fx := fx') B.
Hypothesis HLIBK : forall pl fs K, @LIBK LS pl fs K = wr ch_stderr (PW.OUT pl) (K (LL 0 fs (PW.OUT pl))).
Hypothesis HDELTA : forall n b, @lib_delta LS n b = b.
Hypothesis HROOM : forall b n, @lib_room LS b n ->
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Let ERRNO : errno_addr B + 4 <= alloc_ceiling := ss_errc B APIf ra empty FF.

Let HFMCF : forall fx' : YK11.FPState, @fmemopen_contract_cf fx' rc B (APIf rc) :=
  fun fx' => @utc_fmemopen_cf fx' rc B APIf SH SK ra empty FF (HMALCF fx').

Let HFCCF : forall fx' : YK11.FPState, @fclose_contract_cf fx' rc B (APIf rc) :=
  fun fx' => @utc_fclose_cf fx' rc B APIf SH SK ra empty FF (HFREECF fx') (HFREE0CF fx').

Let HOPENCF : forall fx0 : YK11.FPState, @pcap_source_open_contract_cf fx0 rc B (APIf rc) :=
  fun fx0 => @pcap_source_open_cf.pcap_source_open_cf_holds fx0 rc B (APIf rc) ERRNO
    (@ss_ax fx0 rc B APIf SH SK ra empty FF)
    (@libreac_fuzz_fopen_cf.libreac_fuzz_fopen_cf_holds fx0 rc B (APIf rc) strcmp.strcmp_holds (HFMCF fx0))
    fread_ro.fread_ro_holds (HFCCF fx0).

Let HCLOSECF : forall fx0 : YK11.FPState, @pcap_source_close_contract_cf fx0 rc B (APIf rc) :=
  fun fx0 => @pcap_source_close_cf.pcap_source_close_cf_holds fx0 rc B (APIf rc) ERRNO (HFCCF fx0).

Let HNEXTCF : forall fx0 : YK11.FPState, @pcap_source_next_contract_cf fx0 :=
  fun fx0 => @pcap_source_next_cf.pcap_source_next_cf_holds fx0 fread_ro.fread_ro_holds
    (memmove_ro.memmove_ro_holds memcpy.memcpy_holds).

Theorem pcap_plain_slot_cgo : forall j,
  lib_contract_cgo (LS:=LS) B (APIf rc) PW.OUT frame_G frame_RELRO GI j ENTRY ra empty SLOT_STACK.
Proof.
  apply (slot_lib_cgo B APIf ra empty FF PW.OUT HLIBK HDELTA HROOM PW.OUT_big).
  exact (entry_cf B APIf ra empty FF HMALCF HFREECF LIMLAW HCLOSECF HOPENCF HNEXTCF).
Qed.

End Top.
