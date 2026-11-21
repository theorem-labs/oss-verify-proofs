(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import InfA_garmc. (* [U14] a worker 2026-11-12: a worker's garmC (t2 and slot 504 free) at LEN_ / LEN *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARMC cx ly Lb X := (garmc_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* [U14] at 1.4 the codelens DONE path reaches LEN_ with t2 clobbered and slot 504 = shadow(S+148) (a worker), so LEN_ / LEN take garmC; 0x908fc .. 0x90914 reads neither *)
  Theorem len__garm : forall cx ly, garmcf_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x90968 LEN -> garmcf_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x90950 LEN_.
  Proof.
    intros cx ly HLEN. unfold garmcf_stmtA, GARMCF_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (sinv_len_ cx st lf cf SI MODE) as (SI' & ME').
    inf_arm_open.
    st_norm SI'. st_norm ME'.
    Time zrunb [0x90968].
    eapply (HLEN (IST LEN last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
      [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change LEN with 16200; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
    (* [U14] v240 is a vestige binder at 1.4 (InfABase's inf_locals no longer holds it) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
