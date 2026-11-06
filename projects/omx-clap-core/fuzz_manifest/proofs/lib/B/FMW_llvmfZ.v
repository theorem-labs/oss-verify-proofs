(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_llvmfZ.v at a working branch 79d8c0f1b8f, relocated A->B:
   imports per a Theorem Labs lane's core rule (a working branch 305d8b1527f: lib.A AXxx -> lib.ReusableB YXxx when listed in its
   ReusableB list, other lib.A -> lib.B, FMupoison stays lib.A); every image numeral re-derived from B's listing
   (fuzz_manifest.objdump.txt / nm.txt of the asan-ubsan pin). *)
(* LLVMFuzzerTestOneInput 0x8097c (fuzz_manifest.c:293-321): the walk, assembled from its segments (FMW_llvmfS0.v ..
   FMW_llvmfS7.v, FMW_llvmfSR.v) over the points of FMW_llvmfP.v: entry -> 0x809e0 -> 0x80a50 -> (tn > 4 MiB: 0x80b74)
   0x80a6c -> 0x80ac0 -> 0x80b0c -> 0x80b38 -> 0x80b5c -> 0x80b74 -> ret. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE2k YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0 FMW_llvmfP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_llvmfS0 FMW_llvmfS1 FMW_llvmfS2 FMW_llvmfS3 FMW_llvmfS4 FMW_llvmfS5 FMW_llvmfS6 FMW_llvmfS7 FMW_llvmfSR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The Section's hypotheses are exactly the union of the segments' own (lib/B/FMW_llvmfS0.v .. FMW_llvmfSR.v): the
   segment(s) taking each one are named beside it. *)
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis FB : FmB B.                                                               (* S0 S3 S4 S7 *)
Hypothesis IMG : fm_img_facts tfibsegs B.                                            (* S1 S5 S6 *)
Hypothesis UNIV : fm_univ B.                                                         (* S3 S4 S7 *)
Hypothesis AMALLOC : amalloc04_rule tfibsegs B ameter_triv.                          (* S3 S4 *)
Hypothesis AFREE : afree04_rule tfibsegs B ameter_triv.                              (* S7 *)
Hypothesis MEMCHR : amemchr_realizes tfibsegs B PC_memchr.                           (* S1 *)
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy FM_asan_memcpy.                  (* S3 S4 *)
Hypothesis CNO : check_no_overread_spec tfibsegs B CTX_check_no_overread.            (* S2 *)
Hypothesis ALIVE : fuzz_alloc_live_spec tfibsegs B.                                  (* S5 *)
Hypothesis APRESET : fuzz_alloc_peak_reset_spec tfibsegs B.                          (* S5 *)
Hypothesis APEAK : fuzz_alloc_peak_spec tfibsegs B.                                  (* S5 *)
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.              (* S5 *)
Hypothesis CBA : check_bounded_alloc_spec tfibsegs B.                                (* S5 *)
Hypothesis CAW : check_as_written_spec tfibsegs B.                                   (* S6 *)
Hypothesis CRC : check_reject_clean_spec tfibsegs B.                                 (* S6 *)
Hypothesis STARVED : check_reject_clean_starved_spec tfibsegs B CTX_check_reject_clean_starved.  (* S6 *)
Hypothesis CRT : check_round_trip_spec tfibsegs B CTX_check_round_trip.              (* S7 *)

(* llvmf_pre gives the walk's context (EV_LIB = 2100 covers EV_LLVMF = 2060) *)
Lemma lf_base_of_pre : forall regs ly S W mem md p n pl M live cnt,
  llvmf_pre B regs ly S W mem md p n pl M live cnt ->
  exists peak, n = Z.of_nat (length pl) /\ lf_base B (mkLX ly S W regs mem md p pl live peak cnt).
Proof.
intros regs ly S W mem md p n pl M live cnt (HX & [peak HG] & Hc0 & Hc1 & Hlv).
destruct HX as (HAP & Hra & H10 & H11 & Hpn & Hlen & Hg & Hfr & Hev & Hbb & Haro & _).
exists peak. split; [exact Hlen|]. subst n.
unfold lf_base, lx_n, lx_dl. cbn [lx_ly lx_S lx_W lx_regs lx_mem lx_md lx_p lx_pl lx_live lx_peak lx_cnt].
split; [exact HAP|]. split; [exact Hra|]. split; [exact H10|]. split; [exact H11|]. split; [exact Hpn|].
split; [exact Hg|]. split; [exact Hfr|].
(* the A file's `unfold EV_LLVMF, ..., EV_names, ..., EV_check_round_trip, EV_LIB in *; lia` left the EV_names atoms that
   unfolding EV_check_no_overread / EV_check_round_trip brings back after EV_names (A's Z never compiled: A's S3 is open);
   state the two closed values instead *)
split; [assert (E1 : EV_LLVMF = 2060) by reflexivity; assert (E2 : EV_LIB = 2100) by reflexivity; clear - Hev E1 E2; lia|].
split; [exact Hbb|]. split; [exact Haro|]. split; [exact HG|]. split; [exact Hc0|]. split; [exact Hc1 | exact Hlv].
Qed.

Lemma llvmf_walk : forall regs ly S W mem md p n pl M live cnt,
  llvmf_pre B regs ly S W mem md p n pl M live cnt ->
  SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) (llvmf_post B regs ly S W mem md p n live cnt).
Proof.
intros regs ly S W mem md p n pl M live cnt HPRE.
destruct (lf_base_of_pre regs ly S W mem md p n pl M live cnt HPRE) as (peak & -> & HB).
set (cx := mkLX ly S W regs mem md p pl live peak cnt) in HB.
change (SRr tfibsegs (lx_W cx) (cfg_at tfibsegs A_LLVMF (lx_regs cx) (lx_mem cx) (lx_md cx)) (lf_post B cx)).
apply (lf_seg0 B) with (cx := cx); try assumption.
intros ly0 S0 W0 regs0 mem0 md0 k0 HP0.
(* ly and S occur only in each segment's resume-point premise, so name them (A's Z never compiled: A's S3 is open) *)
apply (lf_seg1 B) with (ly := ly0) (S := S0) (k := k0); try assumption.
intros ly1 S1 W1 regs1 mem1 md1 k1 HP1.
apply (lf_seg2 B) with (ly := ly1) (S := S1) (k := k1); try assumption.
2:{ intros lyR SR WR regsR memR mdR kR HR. apply (lf_segR B) with (ly := lyR) (S := SR) (k := kR); assumption. }
intros ly2 S2 W2 regs2 mem2 md2 k2 HP2.
apply (lf_seg3 B) with (ly := ly2) (S := S2) (k := k2); try assumption.
intros ly3 S3 W3 regs3 mem3 md3 k3 u HP3.
apply (lf_seg4 B) with (ly := ly3) (S := S3) (k := k3) (u := u); try assumption.
intros ly4 S4 W4 regs4 mem4 md4 k4 t HP4.
apply (lf_seg5 B) with (ly := ly4) (S := S4) (k := k4) (u := u) (t := t); try assumption.
intros ly5 S5 W5 regs5 mem5 md5 k5 HP5.
apply (lf_seg6 B) with (ly := ly5) (S := S5) (k := k5) (u := u) (t := t); try assumption.
intros ly6 S6 W6 regs6 mem6 md6 k6 HP6.
apply (lf_seg7 B) with (ly := ly6) (S := S6) (k := k6) (u := u) (t := t); try assumption.
intros lyR SR WR regsR memR mdR kR HR. apply (lf_segR B) with (ly := lyR) (S := SR) (k := kR); assumption.
Qed.
End z.
