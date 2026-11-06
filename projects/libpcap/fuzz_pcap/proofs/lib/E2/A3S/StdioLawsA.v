(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA I_ahm I_fflush. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section StdioLaws.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type}.
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition stdio_ivA (FB : list cblk) (SP : Z) (iv : Z * Z) : Prop :=
    (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
    \/ (0xa9ab0 <= fst iv /\ snd iv <= 0xa9d80) \/ (0x601ca8 <= fst iv /\ snd iv <= 0x6024d0)
    \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160).

  Record gia_stdio_laws : Prop := mkGSL {
    (* [comment removed for export] *)
    gs_stdio : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> STDIOR (ps_libc s) FB m;
    (* [comment removed for export] *)
    gs_ssp   : forall L, exists canary : word, forall RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> ssp_cells m canary;
    gs_errno : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> exists e : word, rw_cells asegs m (ATP + -164) [C4 e];
    gs_env   : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> icptenv m;
    (* [comment removed for export] *)
    gs_ckpf  : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rw_cells asegs m 0x140178 [C8 (Z_to_bv 64 4294967296)];
    (* [comment removed for export] *)
    gs_libc  : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m 0x601849 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x60184b [C1 (Z_to_bv 8 0)];
    (* [comment removed for export] *)
    gs_rng0  : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rng0 RNG;
    (* [comment removed for export] *)
    gs_stack : forall L RNG s CL FB FL m lo hi, GIOA L RNG s CL FB FL m ->
                 ATOP + 4096 <= lo -> lo <= hi -> hi <= al_top L -> hi + 8 <= 2^47 ->   (* [comment removed for export] *)
                 sobj RNG m lo hi;
    (* [comment removed for export] *)
    gs_rodata : forall L RNG s CL FB FL m lo hi, GIOA L RNG s CL FB FL m -> rng_aimg RNG -> rng RNG 0x7fffa000 779776 ->
                 (0x10040 <= lo /\ hi <= 0x21000) \/ (0x22ca0 <= lo /\ hi <= 0x32000) -> lo <= hi -> sobj RNG m lo hi;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    gs_statics : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rng_aimg RNG -> rng RNG 0x7fffa000 779776 ->
                 sobj RNG m 0xa9ab0 0xa9d80 /\ sobj RNG m 0x601ca8 0x6024d0;
    (* [comment removed for export] *)
    gs_ahm : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 exists T, rt_ahm m T /\ T mod 8 = 0 /\ 0x603000 <= T /\ T + AHM_BYTES <= ATOP /\ rng RNG T AHM_BYTES /\ ahm_zero m T
                           (* [comment removed for export] *)
                           /\ (forall b, In b (CL ++ FB) -> cb_addr b + cb_size b <= T \/ T + AHM_BYTES <= cb_addr b);
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    gs_step : forall L RNG s CL FB FL m m' W WX SP l',
                 GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA FB SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX -> ATOP + 4096 <= SP ->
                 (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->   (* [comment removed for export] *)
                 STDIOR l' FB m' -> GIOA L RNG (set_libc l' s) CL FB FL m';
    gs_keeps : forall L RNG s CL FB FL m m' W WX SP,
                 GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA FB SP) W -> ATOP + 4096 <= SP ->
                 agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m m';
    (* [comment removed for export] *)
    gs_adopt : forall L RNG s CL FB FL m m' W SP l' (q : hptr) A,
                 GIOA L RNG s ((q, A, FILE_ALLOC) :: CL) FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA ((q, A, FILE_ALLOC) :: FB) SP) W -> ATOP + 4096 <= SP ->
                 (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
                 STDIOR l' ((q, A, FILE_ALLOC) :: FB) m' ->
                 GIOA L RNG (set_libc l' s) CL ((q, A, FILE_ALLOC) :: FB) FL m';
    gs_release : forall L RNG s CL F1 F2 FL m m' W SP l' (q : hptr) A,
                 GIOA L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA (F1 ++ (q, A, FILE_ALLOC) :: F2) SP) W -> ATOP + 4096 <= SP ->
                 ps_outfile s <> Some q ->
                 (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
                 STDIOR l' (F1 ++ F2) m' ->
                 GIOA L RNG (set_libc l' s) ((q, A, FILE_ALLOC) :: CL) (F1 ++ F2) FL m'
  }.
End StdioLaws.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section StdioLaws.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type}.
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition stdio_ivA (FB : list cblk) (SP : Z) (iv : Z * Z) : Prop :=
    (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
    \/ (0xa9e90 <= fst iv /\ snd iv <= 0xaa160) \/ (0x6020a8 <= fst iv /\ snd iv <= 0x6028d0)
    \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160).

  Record gia_stdio_laws : Prop := mkGSL {
    (* [comment removed for export] *)
    gs_stdio : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> STDIOR (ps_libc s) FB m;
    (* [comment removed for export] *)
    gs_ssp   : forall L, exists canary : word, forall RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> ssp_cells m canary;
    gs_errno : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> exists e : word, rw_cells asegs m (ATP + -164) [C4 e];
    gs_env   : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> icptenv m;
    (* [comment removed for export] *)
    gs_ckpf  : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rw_cells asegs m 0x140578 [C8 (Z_to_bv 64 4294967296)];
    (* [comment removed for export] *)
    gs_libc  : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m 0x601c49 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x601c4b [C1 (Z_to_bv 8 0)];
    (* [comment removed for export] *)
    gs_rng0  : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rng0 RNG;
    (* [comment removed for export] *)
    gs_stack : forall L RNG s CL FB FL m lo hi, GIOA L RNG s CL FB FL m ->
                 ATOP + 4096 <= lo -> lo <= hi -> hi <= al_top L -> hi + 8 <= 2^47 ->   (* [comment removed for export] *)
                 sobj RNG m lo hi;
    (* [comment removed for export] *)
    gs_rodata : forall L RNG s CL FB FL m lo hi, GIOA L RNG s CL FB FL m -> rng_aimg RNG -> rng RNG 0x7fffa000 780288 ->
                 (0x10040 <= lo /\ hi <= 0x21000) \/ (0x22ca0 <= lo /\ hi <= 0x32000) -> lo <= hi -> sobj RNG m lo hi;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    gs_statics : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rng_aimg RNG -> rng RNG 0x7fffa000 780288 ->
                 sobj RNG m 0xa9e90 0xaa160 /\ sobj RNG m 0x6020a8 0x6028d0;
    (* [comment removed for export] *)
    gs_ahm : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 exists T, rt_ahm m T /\ T mod 8 = 0 /\ 0x604000 <= T /\ T + AHM_BYTES <= ATOP /\ rng RNG T AHM_BYTES /\ ahm_zero m T
                           (* [comment removed for export] *)
                           /\ (forall b, In b (CL ++ FB) -> cb_addr b + cb_size b <= T \/ T + AHM_BYTES <= cb_addr b);
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    gs_step : forall L RNG s CL FB FL m m' W WX SP l',
                 GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA FB SP) W -> Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX -> ATOP + 4096 <= SP ->
                 (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->   (* [comment removed for export] *)
                 STDIOR l' FB m' -> GIOA L RNG (set_libc l' s) CL FB FL m';
    gs_keeps : forall L RNG s CL FB FL m m' W WX SP,
                 GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA FB SP) W -> ATOP + 4096 <= SP ->
                 agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m m';
    (* [comment removed for export] *)
    gs_adopt : forall L RNG s CL FB FL m m' W SP l' (q : hptr) A,
                 GIOA L RNG s ((q, A, FILE_ALLOC) :: CL) FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA ((q, A, FILE_ALLOC) :: FB) SP) W -> ATOP + 4096 <= SP ->
                 (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
                 STDIOR l' ((q, A, FILE_ALLOC) :: FB) m' ->
                 GIOA L RNG (set_libc l' s) CL ((q, A, FILE_ALLOC) :: FB) FL m';
    gs_release : forall L RNG s CL F1 F2 FL m m' W SP l' (q : hptr) A,
                 GIOA L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (stdio_ivA (F1 ++ (q, A, FILE_ALLOC) :: F2) SP) W -> ATOP + 4096 <= SP ->
                 ps_outfile s <> Some q ->
                 (exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e']) ->
                 STDIOR l' (F1 ++ F2) m' ->
                 GIOA L RNG (set_libc l' s) ((q, A, FILE_ALLOC) :: CL) (F1 ++ F2) FL m'
  }.
End StdioLaws.
End TwB.
