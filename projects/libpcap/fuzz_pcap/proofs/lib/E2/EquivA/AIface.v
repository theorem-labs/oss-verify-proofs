(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad MSafe HeapFull Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA RunConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface ATsafeX. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.MSafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section AIface.
Context {rc : runConstT}.
Variable NMAX : nat.
Variable site_frame : Pcap.stack_site -> option (Pcap.fframe * Z).
#[local] Notation PSA := (PState aheap hptr).
#[local] Notation HOA := (asan_ops (CE:=ceil_of_rc)).
#[local] Notation FOA := (asan_fo site_frame).
#[local] Notation nsP := (nsafePA NMAX).
(* [comment removed for export] *)
Definition NPKonly (npk : node -> option (machine_state -> resp)) : Prop :=
  forall n, match n with NPeek _ => True | _ => npk n = None end.

Record AHalves := mkAHalves {
  aG : gmap N Z -> N -> Z -> alw -> PSA -> Model -> Prop;
  aeq : PSA -> PSA -> Prop;                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  aG_heap : forall tm nx P g (s s' : PSA) mo, ps_heap s' = ps_heap s -> aG tm nx P g s mo -> aG tm nx P g s' mo;
  aG_step : forall tm nx P g s mo n rsp mo' evs,
      xnode n -> nstep n mo rsp mo' evs -> m_halted mo' = None -> aG tm nx P g s mo -> aG tm nx P (gstepA n rsp g) s mo';
  aG_fresh : forall tm nx P g s mo, aG tm nx P g s mo -> tm !! nx = None;
  aG_below : forall tm nx P g s mo k n, aG tm nx P g s mo -> tm !! k = Some n -> (k < nx)%N;
  aG_addr : forall tm nx P g s mo k n, aG tm nx P g s mo -> tm !! k = Some n ->
      0 <= ho_addr HOA (ps_heap s) k /\ ho_addr HOA (ps_heap s) k + n <= 2^62 /\ 0 <= n;
  aG_pot : forall tm nx P g s mo, aG tm nx P g s mo -> pot_ok P;
  aG_safe : forall tm nx P n g s mo, xnode n -> aG tm nx P g s mo -> nsafe n mo -> nsP n g mo;
  (* [comment removed for export] *)
  a_mallocG : forall tm nx P g s mo n, aG tm nx P g s mo -> pre_malloc tm P n ->
      gop nsP gstepA (ho_malloc HOA n) nx s g mo (gpost aG (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo);
  a_callocG : forall tm nx P g s mo m n, aG tm nx P g s mo -> pre_calloc tm P m n ->
      gop nsP gstepA (ho_calloc HOA m n) nx s g mo (gpost aG (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo);
  a_reallocG : forall tm nx P g s mo k n n', aG tm nx P g s mo -> pre_realloc tm P k n n' ->
      gop nsP gstepA (ho_realloc HOA k n') nx s g mo (gpost aG (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s mo);
  a_freeG : forall tm nx P g s mo k n, aG tm nx P g s mo -> pre_free tm k n ->
      gopu nsP gstepA (ho_free HOA k) s g mo (gpost aG (delete k tm) nx P s mo);
  (* [comment removed for export] *)
  a_mallocC : forall npk, NPKonly npk -> forall tm nx P g s mo n, aG tm nx P g s mo -> pre_malloc tm P n ->
      cop npk (ho_malloc HOA n) nx s mo (cpost (fun tm nx P s mo => exists g, aG tm nx P g s mo) (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo);
  a_callocC : forall npk, NPKonly npk -> forall tm nx P g s mo m n, aG tm nx P g s mo -> pre_calloc tm P m n ->
      cop npk (ho_calloc HOA m n) nx s mo (cpost (fun tm nx P s mo => exists g, aG tm nx P g s mo) (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo);
  a_reallocC : forall npk, NPKonly npk -> forall tm nx P g s mo k n n', aG tm nx P g s mo -> pre_realloc tm P k n n' ->
      cop npk (ho_realloc HOA k n') nx s mo (cpost (fun tm nx P s mo => exists g, aG tm nx P g s mo) (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s mo);
  a_freeC : forall npk, NPKonly npk -> forall tm nx P g s mo k n, aG tm nx P g s mo -> pre_free tm k n ->
      copu npk (ho_free HOA k) s mo (cpost (fun tm nx P s mo => exists g, aG tm nx P g s mo) (delete k tm) nx P s mo);
  (* [comment removed for export] *)
  aeq_refl : forall s, aeq s s;
  aeq_libc : forall s s', aeq s s' -> ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s;
  aeq_G : forall tm nx P g s s' mo, aeq s s' -> aG tm nx P g s mo -> aG tm nx P g s' mo;
  a_site : forall tm nx P g s mo site a, aG tm nx P g s mo -> fo_site FOA s site = Some a -> 0 <= a /\ a + 8192 <= 2^62;
  a_enter_path : forall A f (m : Monad.M PSA A) s g mo tr r g' mo',
      tpathX gstepA (fo_enter FOA A f m s) g mo tr r g' mo' -> exists s', aeq s s' /\ tpathX gstepA (m s') g mo tr r g' mo';
  a_enter_exit : forall A f (m : Monad.M PSA A) s mo tr,
      texit nstep nexit (fo_enter FOA A f m s) mo tr -> exists s', aeq s s' /\ texit nstep nexit (m s') mo tr;
  a_enter_safe : forall A f (m : Monad.M PSA A) tm nx Pt s g mo (P : exc (A * PSA) -> alw -> Model -> Prop),
      aG tm nx Pt g s mo ->
      (forall s', aeq s s' -> twfX nsP gstepA (m s') g mo P) -> twfX nsP gstepA (fo_enter FOA A f m s) g mo P;
  a_ret : forall A f (x : A) s, exists s', aeq s s' /\ fo_ret FOA A f x s = Ret (Ok (x, s'));
  a_enter_reach : forall npk, NPKonly npk -> forall A f (m : Monad.M PSA A) s mo W,
      (forall s', aeq s s' -> wreach npk nstep (m s') mo W) -> wreach npk nstep (fo_enter FOA A f m s) mo W;
  a_enter_wexit : forall npk, NPKonly npk -> forall A f (m : Monad.M PSA A) s mo T,
      (forall s', aeq s s' -> wexit npk nstep nexit (m s') mo T) -> wexit npk nstep nexit (fo_enter FOA A f m s) mo T
}.
End AIface.
