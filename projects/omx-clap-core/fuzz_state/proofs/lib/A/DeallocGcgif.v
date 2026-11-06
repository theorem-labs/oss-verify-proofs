(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DeallocGcgif.v (a working branch 84ee52cd012, file sha256 e04412f10be3) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): fs C5 - the two definitions state the trace premise at fs's FS_U, In tr (as_universe B) \/ st_nev S < EV_MAX (as FSRealloc_rmodel.FS_U), instead of In tr (as_universe B); new lemma dealloc_pre_admit: dealloc_pre at FS_U, with its length conjunct, gives dealloc_pre at tr_admit (as_universe B) S tr, the trace premise of the DIface / DIfaceR instance (YG0d.tr_admit_call's script). *)
(* The cgif_file instance of the generic Deallocate statement (DeallocG.v): its image (tfibsegs, Deallocate at
   0x31be0), model (free) and predicates.  DeallocG.v itself is image-free; consumers relocate it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Export AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Export DeallocG.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The default instantiation: cgif_file's image, model and predicates.  Deallocate does not run the free
   interceptor's internal-allocator initialization, which YG00.free's entry step models: the state must already
   have it ([st_internal_inited S = true]; asan_free's walk and Reallocate's caller establish it before the
   call), so that the entry step leaves the state as it is. *)
Definition rpre_dealloc_cgif (S : astate) (n : Z) : Prop := aregime S /\ qmeter S /\ st_internal_inited S = true.
Definition fpre_cgif (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (p : sptr) (n : Z) : Prop :=
True.
Definition adealloc_realizes_cgif (B : asyms) : Prop :=
adealloc_realizes tfibsegs B (fun tr S => In tr (as_universe B) \/ st_nev S < EV_MAX) free (ARX_cgif B) (aowned B) rpre_dealloc_cgif qtight fpre_cgif 0x31be0 1.
(* The raw twin (DeallocG.adealloc_realizes_raw at the same instantiation). *)
Definition adealloc_realizes_cgif_raw (B : asyms) : Prop :=
adealloc_realizes_raw tfibsegs B (fun tr S => In tr (as_universe B) \/ st_nev S < EV_MAX) free (ARX_cgif B) (aowned B) rpre_dealloc_cgif qtight fpre_cgif 0x31be0 1.
(* fs C5: the trace premise FS_U, with dealloc_pre's length conjunct [(1 <= length tr <= 30)%nat], gives the
   instance's trace premise [tr_admit (as_universe B) S tr] (YG0d.tr_admit_call's script, with the length from that
   conjunct in place of call_trace_len).  Generic over the image. *)
Lemma dealloc_pre_admit : forall segs B ARX rpre fpre atp inst so bp ly S W regs mem md p n tr,
  dealloc_pre segs B (fun tr S => In tr (as_universe B) \/ st_nev S < EV_MAX) ARX rpre fpre atp
    inst so bp ly S W regs mem md p n tr ->
  dealloc_pre segs B (fun tr S => tr_admit (as_universe B) S tr) ARX rpre fpre atp
    inst so bp ly S W regs mem md p n tr.
Proof.
intros segs B ARX rpre fpre atp inst so bp ly S W regs mem md p n tr PRE.
unfold dealloc_pre in PRE |- *.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 &
  Hr14 & Hr15 & Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
assert (L : (length tr <= kUnwindMax)%nat) by (unfold kUnwindMax; lia).
do 27 (split; [assumption|]).
split; [|exact (conj Hp0 HFP)].
cbv beta in Htr |- *. unfold tr_admit.
destruct Htr as [H|H]; [left; exact H | right; exact (conj L H)].
Qed.
End a.
