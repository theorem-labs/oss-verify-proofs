(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv ProgFullQ HeapFull Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition VOLMAX : Z := 2^32.
Definition LIVEMAX : Z := 2^29 + 2^27.
Definition LIVECNT : Z := 16.   (* [comment removed for export] *)
Definition NMAXA : Z := 2^28.
Definition pot_ok (v : Z) : Prop := 0 <= v <= VOLMAX.

(* [comment removed for export] *)
Definition n1 (n : Z) : Z := Z.max n 1.
(* [comment removed for export] *)
Definition live1 (tm : gmap N Z) : Z := zsum (map n1 (sizes tm)).

(* [comment removed for export] *)
Definition apre (tm : gmap N Z) (P : Z) (n' : Z) : Prop :=
  0 <= P /\ P + n' <= VOLMAX /\ n' <= NMAXA /\ live1 tm + n' <= LIVEMAX /\ zlen (sizes tm) + 1 <= LIVECNT.

Definition pre_malloc (tm : gmap N Z) (P : Z) (n : Z) : Prop :=
  0 <= n /\ size_overflows n = false /\ bigb n <= QMAX /\ ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE
  /\ apre tm P (n1 n).

Definition pre_calloc (tm : gmap N Z) (P : Z) (m n : Z) : Prop :=
  0 <= m /\ 0 <= n /\ (negb (n =? 0) && (SIZE_MAX / n <? m)) = false /\ size_overflows (m * n) = false /\ bigb (m * n) <= QMAX
  /\ ROOMN (sizes tm) P9 (m * n) /\ PHI P9 + R63N (sizes tm) + bigb (m * n) <= BLIVE
  /\ apre tm P (n1 (m * n)).

Definition pre_realloc (tm : gmap N Z) (P : Z) (k : N) (n n' : Z) : Prop :=
  tm !! k = Some n /\ 1 <= n' /\ size_overflows n' = false /\ n' + 3 * PGSZ < LEN_MAX /\ bigb n' <= QMAX
  /\ ROOMN (sizes tm) P9 n' /\ PHI P9 + R63N (sizes tm) + bigb n' <= BLIVE
  /\ apre tm P n'.

Definition pre_free (tm : gmap N Z) (k : N) (n : Z) : Prop :=
  tm !! k = Some n /\ PHI P9 + R63N (sizes tm) <= BLIVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HeapIface.
Context {G : Type}.
Variable nsafeP : node -> G -> Model -> Prop.
Variable gstepP : node -> resp -> G -> G.
Context {HG HC : Type}.
Variable HOG : HeapOps HG hptr.
Variable HOC : HeapOps HC hptr.
Variable npk : node -> option (machine_state -> resp).   (* [comment removed for export] *)

#[local] Notation PSG := (PState HG hptr).
#[local] Notation PSC := (PState HC hptr).
#[local] Notation etwfX := (MSafeX.etwfX nsafeP gstepP).

(* [comment removed for export] *)
Definition gpost (hiG : gmap N Z -> N -> Z -> G -> PSG -> Model -> Prop)
           (tm' : gmap N Z) (nx' : N) (P' : Z) (s : PSG) (mo : Model) (g' : G) (s' : PSG) (mo' : Model) : Prop :=
  hiG tm' nx' P' g' s' mo' /\ ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s /\ vm_only mo mo'.
Definition cpost (hiC : gmap N Z -> N -> Z -> PSC -> Model -> Prop)
           (tm' : gmap N Z) (nx' : N) (P' : Z) (s : PSC) (mo : Model) (s' : PSC) (mo' : Model) : Prop :=
  hiC tm' nx' P' s' mo' /\ ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s /\ vm_only mo mo'.

(* [comment removed for export] *)
Definition gop {A} (m : Monad.M PSG (option A)) (res : A) (s : PSG) (g : G) (mo : Model)
           (Q : G -> PSG -> Model -> Prop) : Prop :=
  etwfX (m s) g mo (fun r g' mo' => fst r = Some res /\ Q g' (snd r) mo')
  /\ (forall tr r mo', tpath nstep (m s) mo tr r mo' -> tr = [])
  /\ (forall tr, texit nstep nexit (m s) mo tr -> False).
Definition gopu (m : Monad.M PSG unit) (s : PSG) (g : G) (mo : Model) (Q : G -> PSG -> Model -> Prop) : Prop :=
  etwfX (m s) g mo (fun r g' mo' => Q g' (snd r) mo')
  /\ (forall tr r mo', tpath nstep (m s) mo tr r mo' -> tr = [])
  /\ (forall tr, texit nstep nexit (m s) mo tr -> False).
(* [comment removed for export] *)
Definition cop {A} (m : Monad.M PSC (option A)) (res : A) (s : PSC) (mo : Model) (Q : PSC -> Model -> Prop) : Prop :=
  wreach npk nstep (m s) mo (fun tr r mo' => tr = [] /\ exists s', r = Ok (Some res, s') /\ Q s' mo').
Definition copu (m : Monad.M PSC unit) (s : PSC) (mo : Model) (Q : PSC -> Model -> Prop) : Prop :=
  wreach npk nstep (m s) mo (fun tr r mo' => tr = [] /\ exists s', r = Ok (tt, s') /\ Q s' mo').

Record HeapSimI := mkHSI {
  (* [comment removed for export] *)
  hi_G : gmap N Z -> N -> Z -> G -> PSG -> Model -> Prop;
  hi_C : gmap N Z -> N -> Z -> PSC -> Model -> Prop;
  (* [comment removed for export] *)
  hi_G_heap : forall tm nx P g (s s' : PSG) mo, ps_heap s' = ps_heap s -> hi_G tm nx P g s mo -> hi_G tm nx P g s' mo;
  hi_C_heap : forall tm nx P (s s' : PSC) mo, ps_heap s' = ps_heap s -> hi_C tm nx P s mo -> hi_C tm nx P s' mo;
  hi_G_step : forall tm nx P g s mo n rsp mo' evs,
      xnode n -> nstep n mo rsp mo' evs -> m_halted mo' = None -> hi_G tm nx P g s mo -> hi_G tm nx P (gstepP n rsp g) s mo';
  hi_C_step : forall tm nx P s mo n rsp mo' evs,
      xnode n -> nstep n mo rsp mo' evs -> m_halted mo' = None -> hi_C tm nx P s mo -> hi_C tm nx P s mo';
  (* [comment removed for export] *)
  hi_G_fresh : forall tm nx P g s mo, hi_G tm nx P g s mo -> tm !! nx = None;
  hi_G_below : forall tm nx P g s mo k n, hi_G tm nx P g s mo -> tm !! k = Some n -> (k < nx)%N;
  (* [comment removed for export] *)
  hi_G_addr : forall tm nx P g s mo k n, hi_G tm nx P g s mo -> tm !! k = Some n ->
      0 <= ho_addr HOG (ps_heap s) k /\ ho_addr HOG (ps_heap s) k + n <= 2^62 /\ 0 <= n;
  hi_G_pot : forall tm nx P g s mo, hi_G tm nx P g s mo -> pot_ok P;
  (* [comment removed for export] *)
  hi_mallocG : forall tm nx P g s mo n, hi_G tm nx P g s mo -> pre_malloc tm P n ->
      gop (ho_malloc HOG n) nx s g mo (gpost hi_G (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo);
  hi_mallocC : forall tm nx P s mo n, hi_C tm nx P s mo -> pre_malloc tm P n ->
      cop (ho_malloc HOC n) nx s mo (cpost hi_C (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo);
  hi_callocG : forall tm nx P g s mo m n, hi_G tm nx P g s mo -> pre_calloc tm P m n ->
      gop (ho_calloc HOG m n) nx s g mo (gpost hi_G (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo);
  hi_callocC : forall tm nx P s mo m n, hi_C tm nx P s mo -> pre_calloc tm P m n ->
      cop (ho_calloc HOC m n) nx s mo (cpost hi_C (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo);
  hi_reallocG : forall tm nx P g s mo k n n', hi_G tm nx P g s mo -> pre_realloc tm P k n n' ->
      gop (ho_realloc HOG k n') nx s g mo (gpost hi_G (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s mo);
  hi_reallocC : forall tm nx P s mo k n n', hi_C tm nx P s mo -> pre_realloc tm P k n n' ->
      cop (ho_realloc HOC k n') nx s mo (cpost hi_C (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') s mo);
  hi_freeG : forall tm nx P g s mo k n, hi_G tm nx P g s mo -> pre_free tm k n ->
      gopu (ho_free HOG k) s g mo (gpost hi_G (delete k tm) nx P s mo);
  hi_freeC : forall tm nx P s mo k n, hi_C tm nx P s mo -> pre_free tm k n ->
      copu (ho_free HOC k) s mo (cpost hi_C (delete k tm) nx P s mo)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record FrameSimI (hi : HeapSimI) (FOG : FrameOps (H:=HG) (hptr:=hptr)) (FOC : FrameOps (H:=HC) (hptr:=hptr)) := mkFSI {
  fi_eqG : PSG -> PSG -> Prop;
  fi_eqC : PSC -> PSC -> Prop;
  fi_eqG_refl : forall s, fi_eqG s s;
  fi_eqC_refl : forall s, fi_eqC s s;
  fi_eqG_libc : forall s s', fi_eqG s s' -> ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s;
  fi_eqC_libc : forall s s', fi_eqC s s' -> ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s;
  fi_hiG : forall tm nx P g s s' mo, fi_eqG s s' -> hi_G hi tm nx P g s mo -> hi_G hi tm nx P g s' mo;
  fi_hiC : forall tm nx P s s' mo, fi_eqC s s' -> hi_C hi tm nx P s mo -> hi_C hi tm nx P s' mo;
  fi_siteG : forall tm nx P g s mo site a, hi_G hi tm nx P g s mo -> fo_site FOG s site = Some a -> 0 <= a /\ a + 8192 <= 2^62;
  (* [comment removed for export] *)
  fi_enterG_path : forall A f (m : Monad.M PSG A) s g mo tr r g' mo',
      tpathX gstepP (fo_enter FOG A f m s) g mo tr r g' mo' -> exists s', fi_eqG s s' /\ tpathX gstepP (m s') g mo tr r g' mo';
  fi_enterG_exit : forall A f (m : Monad.M PSG A) s mo tr,
      texit nstep nexit (fo_enter FOG A f m s) mo tr -> exists s', fi_eqG s s' /\ texit nstep nexit (m s') mo tr;
  fi_enterG_safe : forall A f (m : Monad.M PSG A) tm nx Pt s g mo (P : exc (A * PSG) -> G -> Model -> Prop),
      hi_G hi tm nx Pt g s mo ->
      (forall s', fi_eqG s s' -> MSafeX.twfX nsafeP gstepP (m s') g mo P) -> MSafeX.twfX nsafeP gstepP (fo_enter FOG A f m s) g mo P;
  fi_retG : forall A f (x : A) s, exists s', fi_eqG s s' /\ fo_ret FOG A f x s = Ret (Ok (x, s'));
  (* [comment removed for export] *)
  fi_enterC_reach : forall A f (m : Monad.M PSC A) s mo W,
      (forall s', fi_eqC s s' -> wreach npk nstep (m s') mo W) -> wreach npk nstep (fo_enter FOC A f m s) mo W;
  fi_enterC_exit : forall A f (m : Monad.M PSC A) s mo T,
      (forall s', fi_eqC s s' -> wexit npk nstep nexit (m s') mo T) -> wexit npk nstep nexit (fo_enter FOC A f m s) mo T;
  fi_retC : forall A f (x : A) s, exists s', fi_eqC s s' /\ fo_ret FOC A f x s = Ret (Ok (x, s'))
}.
End HeapIface.

Arguments HeapSimI {G} nsafeP gstepP {HG HC} HOG HOC npk.
Arguments FrameSimI {G nsafeP gstepP HG HC HOG HOC npk} hi FOG FOC.
Arguments gop {G} nsafeP gstepP {HG A} m res s g mo Q.
Arguments gopu {G} nsafeP gstepP {HG} m s g mo Q.
Arguments cop {HC} npk {A} m res s mo Q.
Arguments copu {HC} npk m s mo Q.
Arguments gpost {G HG} hiG tm' nx' P' s mo g' s' mo'.
Arguments cpost {HC} hiC tm' nx' P' s mo s' mo'.
Arguments hi_G {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_C {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_G_heap {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_C_heap {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_G_step {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_C_step {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_G_fresh {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_G_below {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_G_addr {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_G_pot {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_mallocG {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_mallocC {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_callocG {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_callocC {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_reallocG {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_reallocC {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_freeG {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments hi_freeC {G nsafeP gstepP HG HC HOG HOC npk} h.
Arguments fi_eqG {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_eqC {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_eqG_refl {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_eqC_refl {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_eqG_libc {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_eqC_libc {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_hiG {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_hiC {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_siteG {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_enterG_path {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_enterG_exit {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_enterG_safe {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_retG {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_enterC_reach {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_enterC_exit {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
Arguments fi_retC {G nsafeP gstepP HG HC HOG HOC npk hi FOG FOC} _.
