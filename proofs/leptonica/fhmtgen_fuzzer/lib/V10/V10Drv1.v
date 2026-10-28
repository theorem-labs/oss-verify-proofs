(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushU10.   (* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Room.
Module V10FuzzIface.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
(* [comment removed for export] *)
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition LEPT_STACK : Z := 16384.          (* [comment removed for export] *)
Definition PC_FUZZ : Z := 0x156ac.           (* [comment removed for export] *)
Definition A_LEPT_SEV : Z := 0x34e00.        (* [comment removed for export] *)
Definition A_LEPT_HANDLER : Z := 0x34e08.    (* [comment removed for export] *)
Definition A_LEPT_PMM : Z := 0x34e10.        (* [comment removed for export] *)
Definition A_EMPTY : Z := 0x45390.           (* [comment removed for export] *)
Definition A_GOT_LO : Z := 0x33d38.          (* [comment removed for export] *)
Definition A_GOT_HI : Z := 0x33dd8.
Definition A_SELNAMES : Z := 0x34e20.         (* [comment removed for export] *)
Definition SELNAMES_LEN : Z := 800.

(* [comment removed for export] *)
Definition FUZZ_CALLS : Z := 203.
Definition fuzz_margin (size : Z) : Z := 2^31 - 2^26.      (* [comment removed for export] *)
Definition FUZZ_BMAX : Z := 2^31 - 2^26.

Lemma fuzz_calls_nonneg : 0 <= FUZZ_CALLS.
Proof. unfold FUZZ_CALLS. lia. Qed.
Lemma fuzz_margin_bound : forall size, 0 <= size < 2^26 -> 0 <= fuzz_margin size <= FUZZ_BMAX.
Proof. intros size H. unfold fuzz_margin, FUZZ_BMAX. lia. Qed.
(* [comment removed for export] *)
Lemma fuzz_room_fits : room_k0 FUZZ_CALLS <= ROOM_KMAX /\ room_b0 FUZZ_BMAX <= ROOM_BCAP.
Proof. unfold room_k0, room_b0, DRV_CALLS, DRV_BYTES, FUZZ_CALLS, FUZZ_BMAX, ROOM_KMAX, ROOM_BCAP. lia. Qed.

Section WithLayout.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.

Definition fuzz_call_contract : Prop :=
  forall (fx : FPState) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word)
         (dptr : word) (size : Z) (payload : list byte) (ret sp0 : word) (argv envp : list (list byte)) (S : TSet),
    ainv A m (m_vmmaps md) -> md_pure md -> al_env sp0 argv envp m ->
    (* [comment removed for export] *)
    getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 size -> size = Z.of_nat (length payload) -> size < 2 ^ 26 ->
    (0 < size -> live A dptr = Some size) ->
    (forall i, 0 <= i < size -> m (Z_to_bv 64 (bv_unsigned dptr + i)) = Some (nth (Z.to_nat i) payload (Z_to_bv 8 0))) ->
    (size = 0 -> dptr = Z_to_bv 64 A_EMPTY /\ forall a : word, A_EMPTY <= bv_unsigned a < A_EMPTY + 16 -> m a = None) ->
    bv_unsigned dptr mod 16 = 0 ->
    (* [comment removed for export] *)
    getr regs 1 = ret -> ret_ok ret -> getr regs 3 = Z_to_bv 64 0x10800 -> getr regs 4 = al_gp ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    alloc_top (m_vmmaps md) + 8192 + LEPT_STACK <= bv_unsigned (getr regs 2) ->
    bv_unsigned (getr regs 2) <= bv_unsigned sp0 -> bv_unsigned sp0 <= sp_window_hi ->
    init_sp_win (m_vmmaps md) ->
    (forall a : word, bv_unsigned (getr regs 2) - LEPT_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                      m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
    (* [comment removed for export] *)
    (forall a : word, A_LEPT_SEV <= bv_unsigned a < A_LEPT_SEV + 8 -> m a = None) ->
    (forall a : word, A_LEPT_PMM <= bv_unsigned a < A_LEPT_PMM + 16 -> m a = None) ->
    store_ok al_segs m (Z_to_bv 64 A_LEPT_HANDLER) 8 = true ->
    (forall a : word, A_GOT_LO <= bv_unsigned a < A_GOT_HI -> m a = None) ->
    (forall a : word, A_SELNAMES <= bv_unsigned a < A_SELNAMES + SELNAMES_LEN -> m a = None) ->
    (* [comment removed for export] *)
    forall (k b : Z), aroom A (m_vmmaps md) k b -> FUZZ_CALLS <= k -> fuzz_margin size <= b ->
    (* [comment removed for export] *)
    (forall A' m' vm' regs',
        ainv A' m' vm' ->
        (forall q, live A' q = live A q) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        (forall r, callee_saved r -> getr regs' r = getr regs r) ->
        (* [comment removed for export] *)
        (forall a : word, ~ (al_grantable a /\ bv_unsigned a < alloc_top (m_vmmaps md)) -> ~ al_globals a ->
                          ~ al_errno_slot a ->
                          ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8) ->
                          ~ (bv_unsigned (getr regs 2) - LEPT_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                          m' a = m a) ->
        (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
        (forall a : word, m a <> None ->
                          bv_unsigned a < al_image_hi \/ (al_grantable a /\ bv_unsigned a < alloc_top (m_vmmaps md))
                          \/ m' a <> None) ->
        vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
        vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
        aroom A' vm' (k - FUZZ_CALLS) (b - fuzz_margin size) ->
        realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
    realizes al_segs (mkCfg (mkst regs (Z_to_bv 64 PC_FUZZ) m al_rom) md) S.
End WithLayout.
End V10FuzzIface.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SeqExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StreamSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SymExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AgentLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PortLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Frame.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymAux.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require RefPrintfLib.
Module V10PrintfBufBase.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymAux.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition PF_FR : Z := 1056.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : 0x66420 <= bv_unsigned sp;
  PspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Pstk   : stk_ok RSEGS mem sp PF_FR;
  Pimg   : forall i, 0x10000 <= i < 0x34000 -> mem (Z_to_bv 64 i) = None;
  Pflags : rdn RSEGS mem (Z_to_bv 64 0x35230) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  Pwend  : rdn RSEGS mem (Z_to_bv 64 0x35250) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65f50));
  Pwpos  : rdn RSEGS mem (Z_to_bv 64 0x35258) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  Pw     : 0x65b50 <= w <= 0x65f4e;
  Pbsz   : rdn RSEGS mem (Z_to_bv 64 0x35290) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  Plock  : rdn RSEGS mem (Z_to_bv 64 0x352bc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Plbf   : rdn RSEGS mem (Z_to_bv 64 0x352c0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Pcan   : rdn RSEGS mem (Z_to_bv 64 0x656e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Pcan64 : 0 <= can < 2 ^ 64 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pf_vals (regs : bvmap 5 word) (sp : word) (w can : Z) : list word :=
  [sp; Z_to_bv 64 w; Z_to_bv 64 can] ++ junk_vals regs.

Definition pfE (regs : bvmap 5 word) (sp : word) (w can : Z) : env :=
  Env (vals_ev (pf_vals regs sp w can)) (blobs_ev []).

Definition pf_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x155b8 | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition pf_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x66420 0x7fffffffffff;
   KWr (SA (EVar 0) (-1056)) 1056;
   KImg 0x10000 0x34000;
   KWord (SA (ELit 0) 0x35230) 4 (ELit 5);
   KWord (SA (ELit 0) 0x35250) 8 (ELit 0x65f50);
   KWord (SA (ELit 0) 0x35258) 8 (EVar 1);
   KRange (EVar 1) 0x65b50 0x65f4e;
   KWord (SA (ELit 0) 0x35290) 8 (ELit 1024);
   KWord (SA (ELit 0) 0x352bc) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x352c0) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x656e8) 8 (EVar 2);
   KWr (SA (ELit 0) 0x34000) 0x2000;
   KWr (SA (EVar 1) 0) 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allregs32 : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section VP1.
  Context {fx : FPState}.
Lemma nth_allregs32 : forall n, (n < 32)%nat -> nth n allregs32 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
End VP1.

Section VP2.
  Context {fx : FPState}.
Lemma regs_ok_by_idx : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i allregs32 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_allregs32 in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
End VP2.

Section Entry.
  Context {fx : FPState}.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x155b8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros i Hi. unfold E, pfE, pf_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 w; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = Z_to_bv 64 w. Proof. reflexivity. Qed.
  Lemma ev2 : ev E 2 = Z_to_bv 64 can. Proof. reflexivity. Qed.

  Lemma pf_regs_ok : regs_ok E pf_sr regs.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth pf_sr allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x34000) 204800 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma data_store_ok : forall m a n,
    0x34000 <= a -> a + Z.of_nat n <= 0x66000 -> store_ok RSEGS m (Z_to_bv 64 a) n = true.
  Proof.
    intros m a n Ha Hn.
    eapply (store_ok_window RSEGS m (Z_to_bv 64 0x34000) (Z_to_bv 64 a) 204800 n 0x34000 0x66000);
      [ apply u64_lit; lia | reflexivity | cbn; lia | apply wseg_data
      | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia ].
  Qed.

  Lemma pf_know_ok : know_ok RSEGS E mem pf_kn.
  Proof.
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold pf_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev0. lia.
    - apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1056); [apply ev0 | exact Pstk0 | unfold PF_FR; lia].
    - apply kimg_intro; [lia | lia | exact Pimg0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pflags0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwend0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwpos0].
    - apply krange_intro. cbn [edenot]. rewrite ev1, u64_lit by lia. lia.
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pbsz0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plock0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plbf0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev2 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pcan0].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite ev1, u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.
End Entry.
End V10PrintfBufBase.

Module V10PrintfBuf.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymAux.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import V10PrintfBufBase.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition pf_stops : list Z := [0x155b8].
Definition pf_fuel : nat := 3000.

(* [comment removed for export] *)
Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0x35230, 4); (SA (ELit 0) 0x35258, 8); (SA (EVar 1) 0, 2)].

(* [comment removed for export] *)
Section VP0.
  Context {fx : FPState}.
Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x15664) mem rom) (mkst regs' (Z_to_bv 64 0x155b8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x35230, 4);
                          (Z_to_bv 64 0x35258, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x35258) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x35230) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
End VP0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Package.
  Context {fx : FPState}.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x155b8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
  Proof.
    intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
    rewrite u64_lit by lia. f_equal; lia.
  Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
  Proof.
    intros k. destruct PH. unfold adenot. cbn [a_base a_off edenot].
    change (ev E 1) with (Z_to_bv 64 w). unfold v_addi. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x15664 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x155b8 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0x35258 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0x35230 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
  Proof.
    intros dirs ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
    pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
    pose proof (pf_know_ok regs mem sp w can PH) as HK.
    fold E in HR, HK.
    destruct (run_sound RSEGS pf_fuel pf_stops (SCR dirs [] []) 0x15664 pf_sr pf_kn 40 ss' scs scr' E mem rom regs
                Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite Hpc in Hms.
    assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Hw1 : ev E 1 = Z_to_bv 64 w) by reflexivity.
    exists R', (mem_denot E mem (s_log ss')).
    split; [exact Hms|]. split; [|split; [|split; [|split]]].
    - eapply (keeps_cs_of_same E); eassumption.
    - replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x35230, 4);
               (Z_to_bv 64 0x35258, 8); (Z_to_bv 64 w, 2)]
        with (map (rdenot E) pf_regions).
      2:{ unfold pf_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. rewrite Hw1, Z0, (u64_lit w) by lia.
          repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold pf_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
        try change (ev E 0) with sp; rewrite ?Hw1, ?Z0, ?(u64_lit w) by lia; lia.
    - pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 0 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
      pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 1 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
      rewrite adenot_var1 in B0, B1.
      apply rdn_2.
      + rewrite u64_lit by lia. lia.
      + rewrite Z.add_0_r in B0. apply B0.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
      + rewrite u64_lit by lia. apply B1.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x35258 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x35230 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sc_bool :=
  match goal with
  | Hw4 : ?w mod 4 = ?r |- _ =>
      first [ rewrite (mod4_shift w _ r Hw4); reflexivity
            | rewrite Hw4; reflexivity ]
  end.

Ltac sc_pf :=
  cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
  first
    [ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
    | apply bt_and3; [lia | cbv beta iota; sc_bool]
    | apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x15664 pf_sr [] pf_kn 40) [].

(* [comment removed for export] *)
Definition dirsA : list bool := [false; true; false; true; false].  (* [comment removed for export] *)
Definition dirsB : list bool := [true; false; true; true; true].    (* [comment removed for export] *)

Definition dirsC : list bool := [true; false; true; true; false].   (* [comment removed for export] *)
Definition dirsD : list bool := [true; false; true; false; false].  (* [comment removed for export] *)

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).

(* [comment removed for export] *)
Ltac run_case dirs res car :=
  lazymatch goal with
  | PH : pfH ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
      eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | let v := eval vm_compute in (snd (fst res)) in
        change (snd (fst res)) with v;
        destruct PH; split_scs; sc_pf ]
  end.

Section VP1.
  Context {fx : FPState}.
Lemma pf_caseA : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x155b8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.
End VP1.

Section VP2.
  Context {fx : FPState}.
Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x155b8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.
End VP2.

Section VP3.
  Context {fx : FPState}.
Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x155b8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.
Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x155b8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.
End VP4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP5.
  Context {fx : FPState}.
Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x155b8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x15664) mem rom) (mkst regs' (Z_to_bv 64 0x155b8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x35230, 4);
                          (Z_to_bv 64 0x35258, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x35258) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x35230) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
  intros regs mem rom sp w can PH R1 R2 R11.
  destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
  - exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
  - exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
  - exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
  - exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.
End VP5.
End V10PrintfBuf.

From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require FileSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ArgvEnv.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefLayout.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10Kit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10ExitR23.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require LibWritevG.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require FPSteps.
Module V10MainEntry.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import V10Kit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)








Import V10Kit.V10StartupDefs. Import V10Kit.V10Startup. Import V10Kit.V10StartupFacts.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1.
Lemma D_main_none : forall sp0 av ev hw drw tid (i : Z),
  valid_argv av -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 av ev hw drw tid (Z_to_bv 64 i) = None.
Proof.
  intros sp0 av ev hw drw tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht.
  unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
         end.
  repeat match goal with
         | H : range_disjoint_b _ _ _ = true |- _ =>
             apply range_disjoint_djw in H; cbn [fst snd] in H
         | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
         | H : true = true |- _ => clear H
         end.
  assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
  unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.
End VP1.

(* [comment removed for export] *)
Section VP2.
Lemma seg_rom_high : forall (a : word), (0x66000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.
End VP2.

(* [comment removed for export] *)
Section VP3.
Lemma rdn_pointwise_inv : forall segs m n (a : word) bs,
  (forall j, (j < n)%nat -> seg_rom segs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs m a n = Some bs ->
  forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs Hseg Hnw Hr j Hj; [lia|].
  cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
  pose proof (Hseg 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
  destruct (m a) as [b|] eqn:Hm.
  - destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    destruct j as [|j].
    + rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
    + cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
      replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
      apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
      intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
      apply Hseg. lia.
  - rewrite H0 in Hr. discriminate.
Qed.
End VP3.

(* [comment removed for export] *)
Lemma total_arg_bytes_firstn_S : forall k l, (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. cbn. lia.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth length] in *. rewrite !total_arg_bytes_cons.
    specialize (IH l' ltac:(lia)). lia.
Qed.

Section MainEntry.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr sp0 av ev 0.
  Definition p1 : word := cat_argv_ptr sp0 av ev 1.
  Definition auxvp : word := auxv_w sp0 av ev.
  Definition rnd : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; guard_bytes a_draw].   (* [comment removed for export] *)
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x2a9d4; spx (-48); ELit 0x10800; ELit 0x45480; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x1520c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=   (* [comment removed for export] *)
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
     KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 10);
     KWord (SA (EVar 3) 48) 8 (ELit 16); (* [comment removed for export] *)
     KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
     KWord (SA (EVar 3) 80) 8 (ELit 11); (* [comment removed for export] *)
     KWord (SA (EVar 3) 96) 8 (ELit 12); (* [comment removed for export] *)
     KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
     KWord (SA (EVar 3) 128) 8 (ELit 25); KWord (SA (EVar 3) 136) 8 (EVar 4);
     KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0)].

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x34000) 0x32000;
     KImg 0x10000 0x35330;
     KImg 0x35331 0x453b0; KImg 0x65488 0x654a8;
     KWord (SA (ELit 0) 0x453b8) 8 (ELit 0x453b8);
     KWord (SA (ELit 0) 0x453d8) 4 (EVar 5);
     KImg 0x453e4 0x45430; KImg 0x45438 0x45450; KImg 0x45458 0x45470;
     (* [comment removed for export] *)
     KImg 0x45480 0x45490; KImg 0x45498 0x65488; KImg 0x654c0 0x656e8;
     KBlob (SA (ELit 0) 0x656e8) (ELit 8) 2;   (* [comment removed for export] *)
     KImg 0x656f0 0x656f8;
     KImg 0x65709 0x65710; KWord (SA (ELit 0) 0x65710) 8 (EVar 3);
     KImg 0x65718 0x65720; KImg 0x65730 0x65738; KWord (SA (ELit 0) 0x65738) 8 (ELit 4096);
     KImg 0x65740 0x65770; (* [comment removed for export] *) KImg 0x65778 0x65b28; KImg 0x65b28 0x66000; (* [comment removed for export] *)
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000 (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section VP4.
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
End VP4.

Section VP5.
Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
End VP5.

Section MainEntryProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.

  Let E := E0 sp0 a0s path envv tid regs.

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.
  Let E := E0 sp0 a0s path envv tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ lazymatch goal with |- _ = edenot _ (spx ?k) =>
                    transitivity (Z_to_bv 64 (bv_unsigned sp0 + k)); [| symmetry; exact (spx_val sp0 a0s path envv tid regs k)] end
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.
  Let E := E0 sp0 a0s path envv tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
      pose proof (read_argc_w RSEGS RPH sp0 av envv a_uid a_hwcap a_draw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
      unfold wmem in Hr. rewrite Hr.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap a_draw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap a_draw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null RSEGS RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 160 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    pose proof (auxv_off_bound RPH sp0 a_draw av envv a_uid a_hwcap) as Hb.
    pose proof (lay_bsb_len RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve) as Hl.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) mod 8 = 0)%Z.
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve) as Hl.
    destruct (rnd_facts RSEGS RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    unfold rnd. subst av. repeat split; try assumption; try lia.
  Qed.

  Lemma auxv_word_at : forall j, (j < 20)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (rnd sp0 a0s path envv) a_uid a_hwcap) (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_draw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word RSEGS RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
    rewrite n_to_le_8_spec. unfold rnd. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
    - kw_auxv 6%nat. - kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat.
    - kw_auxv 12%nat. - kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat. - kw_auxv 18%nat. - kw_auxv 19%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main sp0 av envv a_hwcap a_draw tid) (Z_to_bv 64 0x65710) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x34000) 0x32000 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma range_disjoint_sub : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Lemma missb_sub : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo Hhi. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x66000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv a_hwcap a_draw tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x34000) (Z_to_bv 64 (0x34000 + d)) 0x32000 m 0x34000 0x66000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self sp0 av envv tid).
    - kw_mem (main_entry_tid sp0 av envv tid Hlo regs mem ME).
    - (* [comment removed for export] *)
      rewrite (u_small 8) by lia.
      split; [lia|]. split; [change (eb E 2) with (guard_bytes a_draw); rewrite length_guard_bytes; reflexivity|].
      intros i Hi. change (eb E 2) with (guard_bytes a_draw).
      rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      rewrite Z.add_0_l. apply (D_main_guard_at sp0 av envv tid). lia.
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize sp0 av envv tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma main_str_fits : forall k, (k < 2)%nat -> entry_stack_fits sp0 av envv ->
    (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
  Proof.
    intros k Hk Hfits. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    pose proof (u_cat_argv_ptr RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (total_arg_bytes_firstn_S k av Hk') as Hf.
    unfold entry_stack_fits, entry_stack_span, sp_window_hi, auxv_size in Hfits. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hfits.
    rewrite !total_arg_bytes_Z in Hfits. unfold cat_struct_size, auxv_size in Hu.
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat envv)). lia.
  Qed.

  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    pose proof (lay_bsb_nw RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_draw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      change (length (nth k av []) + 1)%nat with (length (nth k av []) + 1)%nat.
      apply rdn_app.
      + apply read_argv_str_k; [exact Hk' | exact Hnw].
      + pose proof (read_argv_byte_k RPH RSEGS sp0 av envv k (length (nth k av [])) a_uid a_hwcap a_draw Hk' ltac:(lia) Hnw) as Hb.
        rewrite app_nth2, Nat.sub_diag in Hb by lia. cbn [nth] in Hb. exact Hb.
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
End V10MainEntry.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MuslStrlen.
Module V10MainEntryN.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import V10Kit.
Import V10MainEntry.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)








Import V10Kit.V10StartupDefs. Import V10Kit.V10Startup. Import V10Kit.V10StartupFacts.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma total_arg_bytes_firstn_S : forall k l, (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. cbn. lia.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth length] in *. rewrite !total_arg_bytes_cons.
    specialize (IH l' ltac:(lia)). lia.
Qed.

Section MainEntryN.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.

  Definition p0N : word := cat_argv_ptr sp0 av envv 0.
  Definition auxvpN : word := auxv_w sp0 av envv.
  Definition rndN : word := at_random_ptr sp0 av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev [[]; []; guard_bytes a_draw]).   (* [comment removed for export] *)

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0x2a9d4; spx (-48); ELit 0x10800; ELit 0x45480; EVar 11; EVar 12; EVar 13;
     spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x1520c; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 8) 8 (EVar 1);
     KRange (EVar 1) 0x7fff80000000 0x800000400000].

  Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Lemma len_avN : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma evN_junk : forall i, (i < 32)%nat -> ev EN (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold EN. cbn [ev]. unfold valsN.
    change (6 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxN_val : forall k, edenot EN (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev EN 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac reg_caseN :=
    cbn [nth sr_mainN all_regs];
    first [ rewrite spxN_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot EN (EVar n)) with (ev EN n);
              first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma main_strN_fits : forall k, (k < length av)%nat -> entry_stack_fits sp0 av envv ->
    (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
  Proof.
    intros k Hk Hfits. pose proof Hlo. pose proof Hhi.
    pose proof (u_cat_argv_ptr RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk) as Hu.
    pose proof (total_arg_bytes_firstn_S k av Hk) as Hf.
    unfold entry_stack_fits, entry_stack_span, sp_window_hi, auxv_size in Hfits. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hfits.
    rewrite !total_arg_bytes_Z in Hfits. unfold cat_struct_size, auxv_size in Hu.
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat envv)). lia.
  Qed.

  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
  Proof.
    intros k Hk'. pose proof Hlo. pose proof Hhi.
    pose proof (lay_bsb_nw RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound RPH sp0 a_draw av envv a_uid a_hwcap Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_draw) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
      rewrite Hw by lia.
      apply rdn_app.
      + apply read_argv_str_k; [exact Hk' | exact Hnw].
      + pose proof (read_argv_byte_k RPH RSEGS sp0 av envv k (length (nth k av [])) a_uid a_hwcap a_draw Hk' ltac:(lia) Hnw) as Hb.
        rewrite app_nth2, Nat.sub_diag in Hb by lia. cbn [nth] in Hb. exact Hb.
    - exact B1.
    - lia.
    - exact Hlen.
    - destruct (read_word_stack RPH RSEGS sp0 av envv k (length (nth k av [])) a_uid a_hwcap a_draw Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
  Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
  Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
  Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
  Proof.
    pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
    destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap a_draw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main sp0 av envv a_hwcap a_draw tid) (Z_to_bv 64 0x65710) 8
    = Some (word_to_le_bytes 8 auxvpN).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
    unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0x34000) 0x32000 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma range_disjoint_subN : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Lemma missb_subN : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x66000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv a_hwcap a_draw tid i Hva); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

  Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x34000) (Z_to_bv 64 (0x34000 + d)) 0x32000 m 0x34000 0x66000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self sp0 av envv tid).
    - kw_memN (main_entry_tid sp0 av envv tid HLO regs mem ME).
    - (* [comment removed for export] *)
      rewrite (u_small 8) by lia.
      split; [lia|]. split; [change (eb EN 2) with (guard_bytes a_draw); rewrite length_guard_bytes; reflexivity|].
      intros i Hi. change (eb EN 2) with (guard_bytes a_draw).
      rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      rewrite Z.add_0_l. apply (D_main_guard_at sp0 av envv tid). lia.
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize sp0 av envv tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.

  Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  Lemma valsN_length : length valsN = 38%nat.
  Proof. unfold valsN. rewrite length_app, junk_vals_length. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma evN_argc : ev EN 16 = argcN av.
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10MainEntryN.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDriveH4.
Module V10OpenFail_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x3233c; 0x32740; 0x32900; 0x32270; 0x12a64; 0x12bf0; 0x2c8ec; 0x2aed0; 0x2d23c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
(* [comment removed for export] *)
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
(* [comment removed for export] *)
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x66000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x1520c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x32c60 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x2d61c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x2d61c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x2dfac srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x2d61c srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x2d61c srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x2d61c srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x2d90c srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0x2d90c srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS 0x2d61c srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x2d90c srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Section VP1.
Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0x2d23c%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x2dadc%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x111f2, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x2d23c%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x2aed0%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0x2d23c%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x2e4fc%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x2d23c%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x2aed0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.

Section VP2.
Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x32c5c%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x3233c%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x32900%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x3233c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x3233c%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x3233c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x2d23c%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x2aed0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP2.
End V10OpenFail_defs.

Module V10ReadErr_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS : list Z := [0x3233c; 0x32740; 0x32900; 0x32270; 0x12a64; 0x12bf0; 0x2c8ec; 0x2aed0; 0x2d23c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x66000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x45480; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=   (* [comment removed for export] *)
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0x34000) 0x32000;
   KImg 0x10000 0x35330; KImg 0x35331 0x35379; (* [comment removed for export] *) KImg 0x45379 0x453b0; KImg 0x65488 0x654a8;
   KWord (SA (ELit 0) 0x453b8) 8 (ELit 0x453b8);
   KWord (SA (ELit 0) 0x453d8) 4 (EVar 5);
   KImg 0x453e4 0x45430; KImg 0x45438 0x45450; KImg 0x45458 0x45470;
   KImg 0x45480 0x45490; KImg 0x45498 0x65488; KImg 0x654c0 0x656e8;
   KBlob (SA (ELit 0) 0x656e8) (ELit 8) 2;
   KImg 0x656f0 0x656f8; KImg 0x65709 0x65710; KImg 0x65718 0x65720; KImg 0x65730 0x65738;
   KWord (SA (ELit 0) 0x65738) 8 (ELit 4096);
   KImg 0x65740 0x65770;
   KImg 0x65b28 0x66000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x15438 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x2d61c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x2d61c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x2dfac srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x2d61c srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x2d61c srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x2d61c srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Section VP1.
Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x32900%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x3233c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x3233c%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x3233c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x2d23c%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x2aed0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10ReadErr_defs.

From Stdlib Require String.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require LibTail.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Nodes.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeLaws.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SpecConsts.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MmapSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LibWritev.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require ShapeLawsV2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Spec.
Module V10OpenFail_tail.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_segI : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x45480), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (283776 - 168)%Z with 0x453d8%Z.
        krd HK 0x453d8%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * left; unfold atexit_none; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PRE17 : list byte := s2b "cli: cannot open "%string.

  Lemma PRE17_words :
    word_to_le_bytes 8 (Z_to_bv 64 7953747406983097443)
    ++ word_to_le_bytes 8 (Z_to_bv 64 7954887939408031598)
    ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE17.
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma of_segH : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
    length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1%nat = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + (length path + 1))
                  = Some (msg_cannot_open path)).
    { unfold msg_cannot_open. change (s2b _) with PRE17.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 17 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 543 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_cannot_open path) = (17 + (length path + 1))%nat)
      by (unfold msg_cannot_open; rewrite !length_app; reflexivity).
    replace (W 2 (msg_cannot_open path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_cannot_open path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_le62 as (_ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scOF (msg_cannot_open path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scOF]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x111f2) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Lemma of_segG : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
    length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 63)%Z with (63 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x111f2) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x111f2 1) in exact i)
                 _ _ 0x111f2 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-543) 64) in exact i)
                    _ _ _ (-543 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 543 + P)%Z with (bv_unsigned sp0 + (-543 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x111f2) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x111f2) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x111f2) 1 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-543) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-543) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-543) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (of_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 543 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition atG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  Lemma of_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 63)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    atG0 path P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
    unfold PX in Psmall.
    (* [comment removed for export] *)
    run_blk_keep scrF 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-543) 63) in exact i)
                    _ _ _ (-543) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 543)%Z with (bv_unsigned sp0 + -543)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-543) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-543) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-543) BUF_HI IHI knF) with knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HG0 vals1); try eassumption.
    (* [comment removed for export] *)
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 543))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  Lemma of_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 62)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
    eapply (of_segF_gen path pp P _ vals); try eassumption; [lia|].
    intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (of_segG path P vals'); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition atF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
      rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    atF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 103%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x11758 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2dfac : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x2dfac : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 207104) with (0x32900 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2dfac : word) with (Z_to_bv 64 0x2dfac) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
    { subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
    { unfold knE0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
    clear HK3.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrE 135%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1033d) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1033d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1033d) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HF0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pre17_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x111df) 17 = Some PRE17.
  Proof. vm_compute. reflexivity. Qed.

  Lemma PRE17_len : length PRE17 = 17%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE17.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE17_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  Lemma of_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 38))%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    atF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c60) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 P38 Hpp1 Hpp2 HR HK0 Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    pose proof (u64_range (vals_ev vals 38)) as H38r.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (HK : know_ok RSEGS (ENV vals) M knB0).
    { unfold knB0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK0]].
      - apply krange_intro. cbn [edenot ev ENV]. rewrite P2. lia.
      - apply krange_intro. cbn [edenot ev ENV]. lia. }
    clear HK0. change (sr_upd srA (ridx 10) (EVar 38)) with srB0 in HR.
    (* [comment removed for export] *)
    run_blk_keep scrB 39%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite edenot_addw0_errno by (cbn [edenot ev ENV]; lia).
      cbn [edenot ev ENV]. unfold bv_ltu. rewrite (u_small 18446744073709547521) by lia.
      apply (proj2 (Z.ltb_ge _ _)). lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x111df) 17 = Some PRE17).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x111df 17) in exact i)
                 _ _ 0x111df 17 HK eq_refl) by (cbn; lia). apply pre17_img. }
    assert (Hdst : store_ok RSEGS M' dst 17 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 17) in exact i)
                    _ _ _ (-560) 17 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x111df) 17 PRE17).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x111df) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 17) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x111df) 17 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE17) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE17) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE17) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE17) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE17) in *. clearbody M1. clear M' dst.
    assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 71%nat.
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
        | cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
    clear EQM Hstr2 Ht82. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x111f0) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x111f0) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x111f0) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (of_segDE path pp P T t8 vals2); eassumption.
  Qed.

End Tail.
End V10OpenFail_tail.

Module V10Open_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS2 : list Z := (0x2b348 :: 0x2b208 :: 0x156ac :: STOPS)%Z.
Definition run2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS2 scr ss [].

(* [comment removed for export] *)
Definition o_srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition o_ssB0 : sym_state := SS 0x32c60 o_srB0 [] knA 38.
Definition o_rB := Eval vm_compute in run2 scr0 o_ssB0.
Definition o_srB : list expr := Eval vm_compute in s_regs (fst (fst o_rB)).
Definition o_knB : list kentry := Eval vm_compute in kn_after o_rB knA.

Section VP1.
Lemma o_itinB :
  (s_pc (fst (fst o_rB)), snd (fst o_rB)) = (0x2b348%Z, [])
  /\ (nth 10 o_srB (ELit 0), nth 1 o_srB (ELit 0), nth 2 o_srB (ELit 0), nth 3 o_srB (ELit 0))
     = (ELit 65536, ELit 0x15260, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800).
Proof. vm_compute. split; reflexivity. Qed.
End VP1.
End V10Open_defs.

Module V10ReadErr_tail.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10ReadErr_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma re_segI : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x45480), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (283776 - 168)%Z with 0x453d8%Z.
        krd HK 0x453d8%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * left; unfold atexit_none; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PRE19 : list byte := s2b "cli: read error on "%string.

  Lemma PRE19_words :
    word_to_le_bytes 8 (Z_to_bv 64 7018141077071293539)
    ++ word_to_le_bytes 8 (Z_to_bv 64 2338053693894893668)
    ++ word_to_le_bytes 2 (Z_to_bv 64 28271)
    ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE19.
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma re_segH : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1%nat = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-542)%Z 1%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 19 = Some PRE19).
    { rewrite <- PRE19_words. change 19%nat with (8 + (8 + (2 + 1)))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + apply rdn_app_Z; [ | | lia | lia].
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2.
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2)%Z with (bv_unsigned sp0 + -542)%Z by lia.
          exact Hw3. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (19 + (length path + 1))
                  = Some (msg_read_error path)).
    { unfold msg_read_error. change (s2b _) with PRE19.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19)%Z with (bv_unsigned sp0 - 541)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 541 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_read_error path) = (19 + (length path + 1))%nat)
      by (unfold msg_read_error; rewrite !length_app; reflexivity).
    replace (W 2 (msg_read_error path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_read_error path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_re as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRE]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (re_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11209) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Lemma re_segG : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 61)%Z with (61 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x11209) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x11209 1) in exact i)
                 _ _ 0x11209 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
                    _ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x11209) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11209) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x11209) 1 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-541) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (re_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 541 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  Lemma re_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 61)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    reG0 path P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
    unfold PX in Psmall.
    (* [comment removed for export] *)
    run_blk_keep scrF 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-541) 63) in exact i)
                    _ _ _ (-541) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541)%Z with (bv_unsigned sp0 + -541)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-541) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knF) with knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HG0 vals1); try eassumption.
    (* [comment removed for export] *)
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 541))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  Lemma re_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
    eapply (re_segF_gen path pp P _ vals); try eassumption; [lia|].
    intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (re_segG path P vals'); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition reF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
      rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 103%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x11758 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2dfac : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x2dfac : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 207104) with (0x32900 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2dfac : word) with (Z_to_bv 64 0x2dfac) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
    { subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
    { unfold knE0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
    clear HK3.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrE 135%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1033d) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1033d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1033d) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HF0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pre19_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x111f4) 19 = Some PRE19.
  Proof. vm_compute. reflexivity. Qed.

  Lemma PRE19_len : length PRE19 = 19%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma re_memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE19.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE19_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  Lemma re_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srRE0 R -> know_ok RSEGS (ENV vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15438) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x111f4) 19 = Some PRE19).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x111f4 19) in exact i)
                 _ _ 0x111f4 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
    assert (Hdst : store_ok RSEGS M' dst 19 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
                    _ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x111f4) 19 PRE19).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x111f4) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x111f4) 19 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE19) knC0).
    { subst dst. rewrite <- (re_memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE19) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE19) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE19) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE19) in *. clearbody M1. clear M' dst.
    assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 71%nat.
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
        | cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
    clear EQM Hstr2 Ht82. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x11207) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11207) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x11207) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (re_segDE path pp P T t8 vals2); eassumption.
  Qed.

End Tail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10ReadErr_tail.

Module V10Refused_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10ReadErr_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x15454 srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-548)) 2 (ELit 8253);
   SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
   SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x2d61c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x2d61c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x2d61c srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x2d61c srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x2d61c srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Section VP1.
Lemma itinerary_rf :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x2d23c%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x2aed0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10Refused_defs.

Module V10Usage_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10MainEntryN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.


Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x1520c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0x2d61c u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0x2d61c u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0x2dfac u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0x2d61c u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0x2d61c u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0x2d61c u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0x2d90c u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

(* [comment removed for export] *)
Definition u_scrF3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : sym_state := SS 0x2d90c u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : sym_state := SS 0x2d61c u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0x2d90c u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Section VP1.
Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0x3233c%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0x32900%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0x3233c%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0x3233c%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0x3233c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0x2d23c%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x2aed0%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0x2d23c%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0x2dadc%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x108c0, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0x2d23c%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x2aed0%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0x2d23c%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0x2e4fc%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0x3233c%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0x2d23c%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0x2d90c%Z, 0x35140%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x2aed0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10Usage_defs.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymCall.
Module V10Oom_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10Open_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition GLOB : list (Z * Z) := [(0x65778, 0x65b28); (0x453dc, 0x453e0); (0x1000, 0x10000)]%Z.
Definition A_SLO : Z := -128 - 1024.
Definition A_SHI : Z := -128.
Definition kn_acall (kn : list kentry) : list kentry := kn_call GLOB A_SLO A_SHI IHI 0x34000 kn.

(* [comment removed for export] *)
Definition KEPT_AL : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
End V10Oom_defs.

Module V10OpenFail_tail2.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac close_exit HR HK P0 Hh Hlazy sp0 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | left; unfold atexit_none; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Section Tail2.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segI3 : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srI30 R -> know_ok RSEGS (ENV BL vals) M knI30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  Lemma of_segH3 : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH30 R -> know_ok RSEGS (ENV BL vals) M knH30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2dadc) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
    - lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segG3 : forall (path : list byte), Z.of_nat (length path) = 63%Z ->
    atG0 sp0 BL model path 63 (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path HP vals R M HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG3 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * 63 + 63)%Z with 0%Z by lia.
      rewrite ltu_ZZ by lia. reflexivity. }
    assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x111f2) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x111f2 1) in exact i)
                 _ _ 0x111f2 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    pose proof itinerary_63_64 as (_ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
    - cbn [edenot]. exact Hnl.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma NL_word : word_to_le_bytes 1 (Z_to_bv 64 10) = [Z_to_bv 8 10].
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma of_segI4 : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srI40 R -> know_ok RSEGS (ENV BL vals) M knI40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  Lemma of_segH4 : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH40 R -> know_ok RSEGS (ENV BL vals) M knH40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite NL_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segFG4 : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (64 <= P <= 131071)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + P + 1 <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp3 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrF4 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      set (vals0 := vals) in P2, P113.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
      run_blk scr0 199%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x111f2) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x111f2 1) in exact i)
                   _ _ 0x111f2 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
                      _ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x111f2) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x111f2) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x111f2) 1 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
      eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem of_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 131071)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 38))%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 1 <= 0x800000000000)%Z ->
    regs_ok (ENV BL vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV BL vals) M knA ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c60) M (seg_rom RSEGS)) model)
               (t_die (msg_cannot_open path) (m_fs model)).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 P38 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
    unfold t_die.
    eapply (of_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
    - eapply (of_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
    - destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
      + assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
        eapply (of_segF_gen sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
        apply of_segG3. exact E63.
      + eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
  Qed.

End Tail2.
End V10OpenFail_tail2.

Module V10ReadErr.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10ReadErr_defs.
Import V10ReadErr_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10ExitBase. Import V10Kit.V10MemPreds.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition re_ivs : list (Z * Z) :=
  [(0x10000,0x35330); (0x35331,0x35379); (0x45379,0x453b0); (0x65488,0x654a8); (0x453e4,0x45430); (0x45438,0x45450);
   (0x45458,0x45470); (0x45480,0x45490); (0x45498,0x65488); (0x654c0,0x656e8); (0x656f0,0x656f8); (0x65709,0x65710);
   (0x65718,0x65720); (0x65730,0x65738); (0x65740,0x65770); (0x65b28,0x66000); (0, 0x1000)]%Z.

Section ReadErr.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15438) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x45480.
  Hypothesis Rs2 : getr R 18 = pp.
  (* [comment removed for export] *)
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x453d8 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x453b8 8 0x453b8.
  Hypothesis Mpagesz : cell M 0x65738 8 4096.
  (* [comment removed for export] *)
  Hypothesis HBL2 : length (nth 2 BL []) = 8%nat.
  Hypothesis Mguard : bytes_at M 0x656e8 (nth 2 BL []).
  (* [comment removed for export] *)
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

  Definition valsRE : list word :=
    [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].
  Let E : env := ENV BL valsRE.

  Lemma valsRE_len : length valsRE = 39%nat.
  Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
    change (6 + i)%nat with (length [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseRE :=
    cbn [nth srRE0 all_regs];
    first [ rewrite spxRE_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRE : regs_ok E srRE0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
  Qed.

  Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
  Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knRE0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - (* [comment removed for export] *) split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
      apply Mstack; lia.
    - change (edenot E (EVar 2)) with pp. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mself.
    - kcell Mtid.
    - kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
    - (* [comment removed for export] *)
      unfold elenZ, estart. cbn [a_base a_off edenot]. rewrite (u_small 8), (u_small 0) by lia.
      split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
      change (eb E 2) with (nth 2 BL []). split; [rewrite HBL2; reflexivity|].
      intros i Hi. rewrite Z.add_0_l. apply Mguard. rewrite HBL2. exact Hi.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mpagesz.
    - kimg. - kimg.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
    - kimg.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_read_error : forall (path : list byte) (t8 : list byte),
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15438) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof.
    intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
    eapply (re_tail path pp t8 valsRE R M); try eassumption.
    - apply valsRE_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okRE.
    - apply know_okRE. lia.
  Qed.

  Corollary ref_read_error_dot : forall (t8 : list byte),
    (bv_unsigned pp + 9 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0] ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15438) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros t8 Hpp2 Hstr Ht8.
    apply (ref_read_error dot_path t8).
    - cbn. intros [E0|[]]. apply (f_equal bv_unsigned) in E0. vm_compute in E0. lia.
    - cbn. lia.
    - cbn [length dot_path Z.of_nat Pos.of_succ_nat]. lia.
    - exact Hstr.
    - exact Ht8.
  Qed.
End ReadErr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10ReadErr.

Module V10DirRead_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10Open_defs.
Import V10Oom_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS3 : list Z := (0x15438 :: STOPS2)%Z.
Definition run3 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS3 scr ss [].

(* [comment removed for export] *)
Definition ok_sr : list expr := sr_after_call_j o_srB KEPT_AL 38.
Definition ok_kn : list kentry :=
  KRange (EVar 48) 0x66000 0x7fffff7f0000 :: KAlign (EVar 48) 16 :: KWr (SA (EVar 48) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 48) 0) 65536 :: kn_acall o_knB.

(* [comment removed for export] *)
Definition d_ssR0 : sym_state := SS 0x15260 ok_sr [] ok_kn 70.
Definition d_scrR0 : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition d_rR0 := Eval vm_compute in run3 d_scrR0 d_ssR0.
Definition d_srR0 : list expr := Eval vm_compute in s_regs (fst (fst d_rR0)).
Definition d_knR0 : list kentry := Eval vm_compute in kn_after d_rR0 ok_kn.

(* [comment removed for export] *)
Definition d_srR10 : list expr := sr_upd d_srR0 (ridx 10) (ELit (2 ^ 64 - 21)).
Definition d_ssR1 : sym_state := SS 0x32c60 d_srR10 [] d_knR0 70.
Definition d_rR1 := Eval vm_compute in run3 scr0 d_ssR1.
Definition d_srR1 : list expr := Eval vm_compute in s_regs (fst (fst d_rR1)).
Definition d_knR1 : list kentry := Eval vm_compute in kn_after d_rR1 d_knR0.

Section VP1.
Lemma d_itin :
  (s_pc (fst (fst d_rR0)), snd (fst d_rR0)) = (0x32c5c%Z, [])
  /\ (nth 17 d_srR0 (ELit 0), nth 10 d_srR0 (ELit 0), nth 11 d_srR0 (ELit 0), nth 12 d_srR0 (ELit 0))
     = (ELit 63, ELit 3, ELit 0x35379, ELit 65536)
  /\ (s_pc (fst (fst d_rR1)), snd (fst d_rR1)) = (0x15438%Z, [])
  /\ (nth 2 d_srR1 (ELit 0), nth 3 d_srR1 (ELit 0), nth 4 d_srR1 (ELit 0), nth 18 d_srR1 (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x45480, EVar 2).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10DirRead_defs.

Module V10Oom.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Oom_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS2 scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS2 scr NX true.

(* [comment removed for export] *)
Ltac close_exit_w HR HK P0 Hh Hlazy sp0 WP2 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | left; unfold atexit_none; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.
End V10Oom.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefNodes.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefNodesFS.
Module V10OpenFail.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10ExitBase. Import V10ExitR23.V10Exit. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup. Import V10Kit.V10StartupFacts.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1.
Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
  apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End VP1.

Section VP2.
Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
  intros A l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
Qed.
End VP2.

Section VP3.
Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.
End VP3.

Section OpenFail.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None.
  Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = [].
  Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.
  Lemma model0_pure : md_pure model0.
  Proof. constructor; reflexivity. Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.
  Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct Hva as (_ & _ & Hl & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma path_plain : path <> dot_path -> openat_plain_name path = true.
  Proof.
    intros Hnd. destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl.
    inversion Htl as [|x l [Hsl Hdd] _]; subst.
    unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
    change Uapi.dot_path with dot_path. rewrite (path_eqb_neq _ _ Hnd). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma path_facts :
    rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z
    /\ (bv_unsigned (p1 sp0 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen. unfold p1.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|].
    pose proof (lay_bsb_nw RPH sp0 a_draw [a0s; path] envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (read_word_stack RPH RSEGS sp0 [a0s; path] envv 1 (length path) a_uid a_hwcap a_draw ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
      as (t8 & Hl8 & Hr8).
    exists t8. rewrite w_add_nat in Hr8.
    pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)).
    rewrite (main_entry_rdn_above sp0 [a0s; path] envv tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
    vals_ev vals 2 = p1 sp0 a0s path envv ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c60) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    destruct path_facts as (Sr & Slo & Shi & t8 & Ht8).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    rewrite <- model0_fs.
    pose proof (main_str_fits sp0 a0s path envv Hva Hve Hvsp 1%nat ltac:(lia) Hfits) as Hfit1.
    cbn [nth] in Hfit1.
    eapply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 path (p1 sp0 a0s path envv) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
       vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 5 = tid ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M x = mem0 x) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c5c) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path envv tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    - intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x66000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - intros x Hx. rewrite EQM. apply (mem_denot_out_win (ENV vals) mem0 _ 0%nat);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; unfold WIN; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 sp0 a0s path envv -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 sp0 a0s path envv
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma after_openat_fail : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x32c5c) 4) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0x32c5c + 4)%Z with 0x32c60%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
    eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
    - rewrite length_app, HL. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
    - rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
    - apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
      rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_toolong :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong_at RSEGS R _ M model0 ECALLW _ model0_pure HF is_ecall_ECALLW
              ltac:(rewrite A17; reflexivity) A12).
    - rewrite A11. apply (read_cstr_toolong_of_rdn RSEGS M _ (firstn 4096 path)).
      + rewrite firstn_length_le; lia.
      + intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
      + replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
          by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
        apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
        rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_empty :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty_at RSEGS R _ M model0 ECALLW _ model0_pure HF is_ecall_ECALLW
              ltac:(rewrite A17; reflexivity) A12).
    - rewrite A11. apply (read_cstr_of_rdn RSEGS M _ []); [cbn; lia | intros [] |].
      replace (length path + 1)%nat with (length ([] : list byte) + 1)%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with ([] ++ [Z_to_bv 8 0]) in Sr by (rewrite Hnil; reflexivity).
      rewrite <- Sr. apply rdn_agree. intros j Hj. cbn in Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent_at RSEGS R _ M model0 ECALLW path _ model0_pure HF is_ecall_ECALLW
              ltac:(rewrite A17; reflexivity) A10 A12).
    - rewrite A11. apply (read_cstr_of_rdn RSEGS M _ path Hlen path_nonul).
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - apply path_plain. exact Hnd.
    - rewrite model0_fs. exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (0x1520c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x1520c : word) with (Z_to_bv 64 0x1520c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (0x1520c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x1520c : word) with (Z_to_bv 64 0x1520c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (0x1520c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H1 H2 H3 H4. replace (0x1520c : word) with (Z_to_bv 64 0x1520c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10OpenFail.

Module V10Refused.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10ReadErr_defs.
Import V10ReadErr_tail.
Import V10ReadErr.
Import V10Refused_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10MemPreds.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition PRE14 : list byte := s2b "cli: input >= "%string.
Definition DIG8 : list byte := s2b "67108864"%string.
Definition SUF16 : list byte := s2b " bytes, refused"%string ++ [Z_to_bv 8 10].

Section VP1.
Lemma msg_refused_split : msg_refused = PRE14 ++ DIG8 ++ SUF16.
Proof. reflexivity. Qed.
End VP1.

Section VP2.
Lemma PRE14_words :
  word_to_le_bytes 8 (Z_to_bv 64 8101528366825958499) ++ word_to_le_bytes 4 (Z_to_bv 64 1042314357)
  ++ word_to_le_bytes 2 (Z_to_bv 64 8253) = PRE14.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
End VP2.
Section VP3.
Lemma DIG8_word : word_to_le_bytes 8 (Z_to_bv 64 3762256352692483894) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
End VP3.
Section VP4.
Lemma DIG8_bytes :
  word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 55) ++ word_to_le_bytes 1 (Z_to_bv 64 49)
  ++ word_to_le_bytes 1 (Z_to_bv 64 48) ++ word_to_le_bytes 1 (Z_to_bv 64 56) ++ word_to_le_bytes 1 (Z_to_bv 64 56)
  ++ word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 52) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
End VP4.
Section VP5.
Lemma SUF16_words :
  word_to_le_bytes 8 (Z_to_bv 64 2318354787771965984) ++ word_to_le_bytes 8 (Z_to_bv 64 748834984615634290) = SUF16.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
End VP5.
Section VP6.
Lemma pre14_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10db4) 14 = Some PRE14.
Proof. vm_compute. reflexivity. Qed.
End VP6.
Section VP7.
Lemma suf16_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10dc4) 16 = Some SUF16.
Proof. vm_compute. reflexivity. Qed.
End VP7.
Section VP8.
Lemma PRE14_len : length PRE14 = 14%nat. Proof. reflexivity. Qed.
End VP8.
Section VP9.
Lemma DIG8_len : length DIG8 = 8%nat. Proof. reflexivity. Qed.
End VP9.
Section VP10.
Lemma SUF16_len : length SUF16 = 16%nat. Proof. reflexivity. Qed.
End VP10.

Section Refused.
  Variable sp0 : word.
  Ltac at_addr k H :=
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (bv_unsigned sp0 + k)%Z by lia; exact H end.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let T : TSet := t_emit (W 2 msg_refused) (t_exit (exit_code 2) (m_fs model)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segH : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH0 R -> know_ok RSEGS (ENV BL vals) M knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knH ltac:(let i := kidx knH (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x45480), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knH ltac:(let i := kidx knH (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (283776 - 168)%Z with 0x453d8%Z.
        krd HK 0x453d8%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * left; unfold atexit_none; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segG : forall vals R M,
    length vals = 199%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srG0 R -> know_ok RSEGS (ENV BL vals) M knG0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 199%nat.
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 4%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-548)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-546)%Z 8%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-538)%Z 8%nat Hw4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-530)%Z 8%nat Hw5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    assert (MSG : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + -560)) ((8 + (4 + 2)) + (8 + (8 + 8)))
                  = Some msg_refused).
    { rewrite msg_refused_split, <- PRE14_words, <- DIG8_word, <- SUF16_words.
      apply rdn_app_Z; [ | | lia | lia].
      - apply rdn_app_Z; [exact Hw0 | | lia | lia].
        apply rdn_app_Z; [at_addr (-552)%Z Hw1 | at_addr (-548)%Z Hw2 | lia | lia].
      - apply rdn_app_Z; [at_addr (-546)%Z Hw3 | | lia | lia].
        apply rdn_app_Z; [at_addr (-538)%Z Hw4 | at_addr (-530)%Z Hw5 | lia | lia]. }
    (* [comment removed for export] *)
    unfold T.
    replace (W 2 msg_refused) with (map (WriteEv (Z_to_bv 64 2)) (msg_refused ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_rf as (_ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG knG Rc Mc model scRF msg_refused []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRF];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. reflexivity.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      change 38%nat with ((8 + (4 + 2)) + (8 + (8 + 8)))%nat. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (rf_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE14.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE14_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Lemma memcpy4_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM4 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 546)) DIG8.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- DIG8_word. cbn [mem_denot logM4].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Lemma memcpy5_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM5 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 538)) SUF16.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- SUF16_words. cbn [mem_denot logM5]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  (* [comment removed for export] *)
  Ltac after_memcpy HL Hms Hkeep :=
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity);
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]; clear Hms;
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity);
    lazymatch goal with H : regs_ok ?E ?sr ?Rc |- realizes _ (mkCfg (mkst ?R2 _ _ _) _) _ =>
      pose proof (regs_after_keeps _ (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) H Hkeep callee_kept_no0) as HR2;
      rewrite HL in HR2; clear H Hkeep; rename HR2 into HR
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segF : forall vals R M,
    length vals = 167%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knF0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 167%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 538)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x10dc4) 16 = Some SUF16).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x10dc4 16) in exact i)
                 _ _ 0x10dc4 16 HK eq_refl) by (cbn; lia). apply suf16_img. }
    assert (Hdst : store_ok RSEGS M dst 16 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-538) 16) in exact i)
                    _ _ _ (-538) 16 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 538)%Z with (bv_unsigned sp0 + -538)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x10dc4) 16 SUF16).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10dc4) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 16) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x10dc4) 16 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst SUF16) knG0).
    { subst dst. rewrite <- (memcpy5_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM5 knF [] knG0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM5].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst SUF16) knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segG vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segE : forall vals R M,
    length vals = 135%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srE0 R -> know_ok RSEGS (ENV BL vals) M knD ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 135%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546)).
    set (src := Z_to_bv 64 (bv_unsigned sp0 - 952)).
    (* [comment removed for export] *)
    krdv HK 0%nat (-952)%Z 1%nat Hd0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-951)%Z 1%nat Hd1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-950)%Z 1%nat Hd2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-949)%Z 1%nat Hd3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-948)%Z 1%nat Hd4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-947)%Z 1%nat Hd5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-946)%Z 1%nat Hd6. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-945)%Z 1%nat Hd7. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    cbn [a_base a_off edenot ev ENV] in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    rewrite P0 in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    assert (Hsrc : rdn RSEGS M src (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) = Some DIG8).
    { subst src. replace (bv_unsigned sp0 - 952)%Z with (bv_unsigned sp0 + -952)%Z by lia. rewrite <- DIG8_bytes.
      apply rdn_app_Z; [exact Hd0 | | lia | lia].
      apply rdn_app_Z; [at_addr (-951)%Z Hd1 | | lia | lia].
      apply rdn_app_Z; [at_addr (-950)%Z Hd2 | | lia | lia].
      apply rdn_app_Z; [at_addr (-949)%Z Hd3 | | lia | lia].
      apply rdn_app_Z; [at_addr (-948)%Z Hd4 | | lia | lia].
      apply rdn_app_Z; [at_addr (-947)%Z Hd5 | | lia | lia].
      apply rdn_app_Z; [at_addr (-946)%Z Hd6 | at_addr (-945)%Z Hd7 | lia | lia]. }
    assert (Hdst : store_ok RSEGS M dst 8 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knE ltac:(let i := kidx knE (is_kwr_cov (EVar 0) (-546) 8) in exact i)
                    _ _ _ (-546) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 546)%Z with (bv_unsigned sp0 + -546)%Z by lia. exact Hst. }
    assert (MC : mcH M dst src 8 DIG8).
    { constructor; subst dst src; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = src)
        by (regv HR (11 : reg); subst src; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A12 : getr Rc 12 = Z_to_bv 64 8) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst DIG8) knF0).
    { subst dst. rewrite <- (memcpy4_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM4 knE [] knF0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM4].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst DIG8) knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 167%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segF vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  Ltac memcpy0_step HL P0 srcZ :=
    let dst := fresh "dst" in
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546));
    lazymatch goal with HR : regs_ok _ _ ?Rc |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      assert (MC : mcH Mc dst (Z_to_bv 64 srcZ) 0 [])
        by (constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity);
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 srcZ) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy Mc dst (Z_to_bv 64 srcZ) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12 MC;
      after_memcpy HL Hms Hkeep;
      change (wbytes Mc dst []) with Mc
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segD : forall vals R M,
    length vals = 103%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srD0 R -> know_ok RSEGS (ENV BL vals) M knC ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 103%nat.
    memcpy0_step HL P0 0x1033d%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knD ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segE vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segC : forall vals R M,
    length vals = 71%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srC0 R -> know_ok RSEGS (ENV BL vals) M knC0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 71%nat.
    memcpy0_step HL P0 0x10dc2%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knC ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 103%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segD vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segB : forall vals R M,
    length vals = 39%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srRF0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15454) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 39%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x10db4) 14 = Some PRE14).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x10db4 14) in exact i)
                 _ _ 0x10db4 14 HK eq_refl) by (cbn; lia). apply pre14_img. }
    assert (Hdst : store_ok RSEGS M dst 14 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 14) in exact i)
                    _ _ _ (-560) 14 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x10db4) 14 PRE14).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10db4) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 14) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x10db4) 14 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE14) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE14) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segC vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x45480.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x453d8 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x453b8 8 0x453b8.
  Hypothesis Mpagesz : cell M 0x65738 8 4096.
  (* [comment removed for export] *)
  Hypothesis HBL2 : length (nth 2 BL []) = 8%nat.
  Hypothesis Mguard : bytes_at M 0x656e8 (nth 2 BL []).

  Let E : env := ENV BL (valsRE sp0 sp0 tid R).

  Lemma evRF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid R i Hi). Qed.

  Ltac reg_caseRF :=
    cbn [nth srRF0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRF_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRF : regs_ok E srRF0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRF.
  Qed.

  Theorem ref_refused_tail :
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15454) M (seg_rom RSEGS)) model)
               (t_die msg_refused (m_fs model)).
  Proof.
    pose proof SPlo. pose proof SPhi.
    unfold t_die.
    eapply (rf_segB (valsRE sp0 sp0 tid R) R M (valsRE_len sp0 sp0 tid R) eq_refl regs_okRF).
    apply (know_okRE sp0 BL Hvsp sp0 tid R M Mstack Mimg Mtid Htid Mself Mpagesz HBL2 Mguard); lia.
  Qed.
End Refused.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10Refused.

Module V10Usage_tail.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10MainEntryN.
Import V10Usage_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PRE7 : list byte := s2b "usage: "%string.
Definition SUF7 : list byte := s2b " INPUT"%string ++ [Z_to_bv 8 10].

Section VP1.
Lemma PRE7_word : word_to_le_bytes 7 (Z_to_bv 64 9071406455288693) = PRE7.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
End VP1.
Section VP2.
Lemma SUF7_word : word_to_le_bytes 7 (Z_to_bv 64 2907475163367712) = SUF7.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
End VP2.
Section VP3.
Lemma pre7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x108b7) 7 = Some PRE7.
Proof. vm_compute. reflexivity. Qed.
End VP3.
Section VP4.
Lemma suf7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x108c0) 7 = Some SUF7.
Proof. vm_compute. reflexivity. Qed.
End VP4.
Section VP5.
Lemma PRE7_len : length PRE7 = 7%nat. Proof. reflexivity. Qed.
End VP5.
Section VP6.
Lemma SUF7_len : length SUF7 = 7%nat. Proof. reflexivity. Qed.
End VP6.
Section VP7.
Lemma msg_usage_eq : forall a0s, msg_usage a0s = PRE7 ++ a0s ++ SUF7.
Proof. intros. unfold msg_usage, PRE7, SUF7. reflexivity. Qed.
End VP7.

Section UTail.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

(* [comment removed for export] *)
Ltac close_exit_at HR HK P0 Hh Hlazy sp0 OFF WLO :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV EN] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV EN];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV EN] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV EN] in Ktid |- *; lia
      | lit_u; cbn [ev ENV EN] in Ktid |- *; lia
      | cbn [ev ENV EN] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev ENV EN] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | left; unfold atexit_none; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH0 R -> know_ok RSEGS (ENV vals) M u_knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG : forall (a0s : list byte) (L : Z) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
    length vals = 230%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 112 = Z_to_bv 64 L ->
    regs_ok (ENV vals) u_srG0 R -> know_ok RSEGS (ENV vals) M u_knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7%nat = Some SUF7 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L vals R M HP HPr HL P0 P112 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep scr0 230%nat.
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7 = Some SUF7).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + (length a0s + 7))
                  = Some (msg_usage a0s)).
    { rewrite msg_usage_eq.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 7 + Z.of_nat (length a0s))%Z
          with (bv_unsigned sp0 - 553 + L)%Z by lia. exact SBn'. }
    replace (W 2 (msg_usage a0s)) with (map (WriteEv (Z_to_bv 64 2)) (msg_usage a0s ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    assert (LEN : length (msg_usage a0s) = (7 + (length a0s + 7))%nat)
      by (rewrite msg_usage_eq, !length_app, PRE7_len, SUF7_len; reflexivity).
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG u_knG Rc Mc model u_scG (msg_usage a0s) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG u_knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Definition atUF0 (a0s : list byte) (L : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 198%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 112 = Z_to_bv 64 L ->
      regs_ok (ENV vals) u_srF0 R -> know_ok RSEGS (ENV vals) M u_knF0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.

  Lemma us_segF : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
    atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep u_scrF 198%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
      replace (-1 * L + 73)%Z with (73 - L)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553 + L)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x108c0) 7 = Some SUF7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kimg_cov 0x108c0 7) in exact i)
                 _ _ 0x108c0 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
    assert (Hdst : store_ok RSEGS M' dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kwr_cov (EVar 0) (-553) 73) in exact i)
                    _ _ _ (-553 + L) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 553 + L)%Z with (bv_unsigned sp0 + (-553 + L))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x108c0) 7 SUF7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x108c0) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x108c0) 7 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst SUF7) 0 (-553) BUF_HI IHI u_knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst SUF7 (ENV vals) 0 (-553) BUF_HI);
                        cbn [ev ENV]; rewrite P0, ?SUF7_len; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knF) with u_knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst SUF7) u_knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 230%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (us_segG a0s L vals1); try eassumption.
    - rewrite rdn_wbytes_out; [exact SBp' | | |]; rewrite ?SUF7_len; subst dst; rewrite ?u_small by lia; lia.
    - subst dst. rewrite <- SUF7_len.
      apply (rdn_wbytes_hit RSEGS SUF7 M'). rewrite SUF7_len, u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segE_gen : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 73)%Z ->
    length vals = 166%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 112 = Z_to_bv 64 L ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    atUF0 a0s L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T vals R M HP HPr HL P0 P1 P112 Hpp1 Hpp2 HR HK Hstr HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
    run_blk_keep u_scrE 166%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
    { replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length a0s) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knE ltac:(let i := kidx u_knE (is_kwr_cov (EVar 0) (-553) 73) in exact i)
                    _ _ _ (-553) (length a0s) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 553)%Z with (bv_unsigned sp0 + -553)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp L a0s).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P1);
      assert (A12 : getr Rc 12 = Z_to_bv 64 L) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P112);
      destruct (ref_memcpy M' dst pp L _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst a0s) 0 (-553) BUF_HI IHI u_knE
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst a0s (ENV vals) 0 (-553) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knE) with u_knF0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst a0s) u_knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 198%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HF0 vals1); try eassumption.
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS a0s M' (Z_to_bv 64 (bv_unsigned sp0 - 553))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition atUE0 (a0s : list byte) (pp : word) (L : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 166%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 112 = Z_to_bv 64 L ->
      regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
      rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.

  Lemma us_segCD : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
    length vals = 102%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srC0 R -> know_ok RSEGS (ENV vals) M u_knB ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
    atUE0 a0s pp L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 102%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (a0s ++ t8)) = Some (a0s ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length a0s) (a0s ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length a0s + 1) _ (length a0s)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + L) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length a0s))%Z with (bv_unsigned pp + L)%Z in B1 by lia.
      replace (bv_unsigned pp + L + Z.of_nat 0)%Z with (bv_unsigned pp + L)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (a0s ++ t8) L 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq a0s (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ u_knC ltac:(let k := kidx u_knC (is_kimg_cov 0x11758 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knC ltac:(let i := kidx u_knC (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2dfac : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P1);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (a0s ++ t8) L 0x7fffffff (seg_rom RSEGS) Rc (0x2dfac : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 207104) with (0x32900 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2dfac : word) with (Z_to_bv 64 0x2dfac) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI u_knC
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI u_knC)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 134%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L).
    { subst vals1. change 112%nat with (102 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 u_knD0).
    { unfold u_knD0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV LX]. rewrite Q112, u_small by lia. lia. }
    clear HK3.
    assert (Hstr2 : rdn RSEGS M2 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q112, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep u_scrD 134%nat.
    { unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q1, ?Q112). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length a0s + 1) _ (length a0s)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1033d) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1033d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1033d) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 u_knD ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 166%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q1).
    assert (W112 : vals_ev vals2 112 = Z_to_bv 64 L) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q112).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HE0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segB : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
    atUE0 a0s pp L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    run_blk_keep scr0 70%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M3.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x108be) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x108be) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x108be) 0 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals (junk_vals R4) (blobs_ev BL) M3 u_knB ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 102%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (us_segCD a0s pp L T t8 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH3 : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH30 R -> know_ok RSEGS (ENV vals) M u_knH30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG3 : forall vals R M,
    length vals = 230%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srG30 R -> know_ok RSEGS (ENV vals) M u_knG30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2dadc) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 230%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG3 u_knG3 Rc Mc model u_scG3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG3 u_knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG3 length Z.of_nat] end.
    - lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  Lemma us_segF3 : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (67 <= L <= 73)%Z ->
    atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep u_scrF3 198%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite <- (zbv_mod (-1 * L + 73)%Z).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + length a0s) = Some (PRE7 ++ a0s)).
    { apply rdn_app_Z; [exact Hw0 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'. }
    assert (Hsuf : rdn RSEGS M' (Z_to_bv 64 0x108c0) 7 = Some SUF7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF3 ltac:(let i := kidx u_knF3 (is_kimg_cov 0x108c0 7) in exact i)
                 _ _ 0x108c0 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
    rewrite msg_usage_eq, app_assoc. unfold W.
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srF3 u_knF3 Rc Mc model u_scF3 (PRE7 ++ a0s) SUF7
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srF3 u_knF3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scF3];
      rewrite ?length_app, ?PRE7_len, ?SUF7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
      replace (7 + length a0s)%nat with (7 + length a0s)%nat by lia. exact B80.
    - cbn [edenot]. exact Hsuf.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (us_segG3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH4 : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH40 R -> know_ok RSEGS (ENV vals) M u_knH40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d90c) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG4 : forall vals R M,
    length vals = 230%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srG40 R -> know_ok RSEGS (ENV vals) M u_knG40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 230%nat.
    krdv HK 0%nat (-560)%Z 7%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite SUF7_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 SUF7) with (map (WriteEv (Z_to_bv 64 2)) (SUF7 ++ [])) by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG4 u_knG4 Rc Mc model u_scG4 SUF7 []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG4 u_knG4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG4];
      rewrite ?SUF7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot length Z.of_nat]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  Lemma us_segEF4 : forall (a0s : list byte) (pp : word) (L : Z), Z.of_nat (length a0s) = L -> (74 <= L <= 131071)%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + L + 1 <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    atUE0 a0s pp L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s pp L HP HPr Hpp1 Hpp2 Hpp3 vals R M HL P0 P1 P112 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
    run_blk_keep u_scrE4 166%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
    { replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE7 ++ a0s)) (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))))).
    2:{ rewrite msg_usage_eq, app_assoc. unfold W. rewrite (map_app _ (PRE7 ++ a0s)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srE4 u_knE4 Rc Mc model u_scE4 PRE7 a0s
             (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n u_srE4 u_knE4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scE4];
      rewrite ?PRE7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - first [lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV LX]. rewrite P112. rewrite u_small by lia. lia.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV LX]. rewrite P1. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV LX]. rewrite P1, P112. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hw0.
    - cbn [edenot ev ENV LX]. rewrite P1. exact Hsrc.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with u_knF40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with u_srF40 in HR end.
      set (vals0 := vals) in P1, P112.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 198%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
      run_blk scr0 198%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hsuf : rdn RSEGS MG (Z_to_bv 64 0x108c0) 7 = Some SUF7).
      { rewrite (kimg_rdn RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kimg_cov 0x108c0 7) in exact i)
                   _ _ 0x108c0 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
      assert (Hdst : store_ok RSEGS MG dst 7 = true).
      { pose proof (kwr_store_ok RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                      _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x108c0) 7 SUF7).
      { constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
        - exact Hsuf.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x108c0) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x108c0) 7 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      pose proof (know_after_store RSEGS (ENV vals1) MG u_knF4 (SA (EVar 0) (-560)) 7 (ELit 2907475163367712) SUF7
                    u_knG40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply SUF7_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst SUF7) u_knG40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 230%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
      eapply (us_segG4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem us_tail : forall (a0s : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) a0s -> (Z.of_nat (length a0s) <= 131071)%Z ->
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 1 <= 0x800000000000)%Z ->
    regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length a0s))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d61c) M (seg_rom RSEGS)) model)
               (t_die (msg_usage a0s) (m_fs model)).
  Proof.
    intros a0s pp t8 vals R M Hnonul HPl HL P0 P1 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
    unfold t_die.
    eapply (us_segB a0s pp (Z.of_nat (length a0s)) _ t8 vals); try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q1 Q112 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length a0s)) 73) as [Hle | Hgt].
    - eapply (us_segE_gen a0s pp _ _ vals'); try eassumption; try lia.
      destruct (Z.le_gt_cases (Z.of_nat (length a0s)) 66) as [Hle2 | Hgt2].
      + apply us_segF; [reflexivity | lia].
      + apply us_segF3; [reflexivity | lia].
    - eapply (us_segEF4 a0s pp _ eq_refl); try eassumption; lia.
  Qed.

End UTail.
End V10Usage_tail.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SimInv.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ExitSim.
Module V10Open.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SimInv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ExitSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail.
Import V10Open_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import V10Kit.V10Startup.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS2 scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS2 scr NX true.

Lemma alloc_fd_init : forall e0 e1 e2,
  alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. reflexivity. Qed.
Lemma fd_lookup_init_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. intros. reflexivity. Qed.

Section Open.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  Definition vm0 : VmMaps := mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0.
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0)).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model := mkModelC (fds1g fd3) vm0 stdin0 fs0 None (Some tid) None.

  Lemma model0_eq : model0 = mkModelC fds0 vm0 stdin0 fs0 None (Some tid) None.
  Proof. reflexivity. Qed.
  Lemma model0_OF : model0 = V10OpenFail.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.
  Proof. reflexivity. Qed.
  Lemma m0_fds : m_fds model0 = fds0. Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.
  Lemma m0_pure : md_pure model0. Proof. constructor; reflexivity. Qed.
  Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3. Proof. intros; reflexivity. Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0. Proof. intros; reflexivity. Qed.
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = vm0. Proof. intros; reflexivity. Qed.
  Lemma m1_pure : forall fd3, md_pure (model1g fd3). Proof. intros; constructor; reflexivity. Qed.
  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. intros. reflexivity. Qed.
  Lemma fds1_3 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 3) = Some fd3.
  Proof. intros. reflexivity. Qed.
  Lemma model1_with_fds : forall fd3,
    with_fds (fd_insert (m_fds model0) (alloc_fd (m_fds model0)) fd3) model0 = model1g fd3.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.
  (* [comment removed for export] *)
  Definition out_win (M : word -> option byte) : Prop :=
    forall a : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> M a = mem0 a.
  Lemma out_win_above : forall M, out_win M -> above_sp0 M.
  Proof. intros M H a Ha. apply H. lia. Qed.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      above_sp0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c60) M (seg_rom RSEGS)) model0) KA.

  (* [comment removed for export] *)
  Definition at_malloc (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
      regs_ok (ENV vals) o_srB R -> know_ok RSEGS (ENV vals) M o_knB ->
      out_win M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b348) M (seg_rom RSEGS)) (model1g fd3)) KB.

  (* [comment removed for export] *)
  Lemma open_ok_blockB : forall fd3 KB vals R M,
    at_malloc fd3 KB ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (ELit 3)) R -> know_ok RSEGS (ENV vals) M knA ->
    out_win M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c60) M (seg_rom RSEGS)) (model1g fd3)) KB.
  Proof.
    intros fd3 KB vals R M HKB HL P0 P1 P2 P5 HR HK HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (mp_halted _ (m1_pure fd3)) as Hh.
    change (sr_upd srA (ridx 10) (ELit 3)) with o_srB0 in HR.
    run_block_keep scr0 38%nat.
    apply (HKB vals); try assumption.
    intros x Hx. rewrite EQM. rewrite (mem_denot_out_win (ENV vals) M _ 0%nat);
      [apply HA; exact Hx | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; unfold WIN; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 sp0 a0s path envv -> regs_ok (ENV vals) srA R ->
    bv_unsigned (getr R 17) = 56%Z /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 sp0 a0s path envv
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  Lemma path_facts :
    rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z
    /\ (bv_unsigned (p1 sp0 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen. unfold p1. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma open_pipeline_gen : forall fd3 KA KB,
    (forall (R : bvmap 5 word) (M : word -> option byte),
       bv_unsigned (getr R 17) = 56%Z -> getr R 10 = AT_FDCWD ->
       Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z ->
       rdn RSEGS M (getr R 11) (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
       (forall e, In e openat_errnos ->
          realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x32c5c) 4) M (seg_rom RSEGS)) model0) KA) ->
       realizes RSEGS (mkCfg (mkst (regupd R 10 (alloc_fd (m_fds model0))) (v_addi (Z_to_bv 64 0x32c5c) 4) M (seg_rom RSEGS))
                            (with_fds (fd_insert (m_fds model0) (alloc_fd (m_fds model0)) fd3) model0)) KB ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c5c) M (seg_rom RSEGS)) model0) (t_alt2 KA KB)) ->
    open_err_branch KA -> at_malloc fd3 KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros fd3 KA KB NODE HKA HKB.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & Slen). pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    rewrite model0_OF.
    apply (V10OpenFail.of_blockA sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Htid ME).
    intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout. rewrite <- model0_OF.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    apply (NODE R M A17 A10 A12).
    - rewrite A11, <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x32c5c + 4)%Z with 0x32c60%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x32c5c + 4)%Z with 0x32c60%Z.
      rewrite model1_with_fds. rewrite m0_fds. unfold fds0. rewrite alloc_fd_init.
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (open_ok_blockB fd3 KB vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  Theorem open_file_pipeline : forall fdata KA KB,
    fs_lookup fs0 path = Some fdata -> path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
    open_err_branch KA -> at_malloc (FdFile path (Z_to_bv 64 0)) KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros fdata KA KB Hfile Hpne Hpnd Hplen HKA HKB.
    apply (open_pipeline_gen (FdFile path (Z_to_bv 64 0)) KA KB); [| exact HKA | exact HKB].
    intros R M A17 A10 A12 Hstr HA HB.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_file_at RSEGS R _ M model0 ECALLW path fdata KA KB m0_pure HF is_ecall_ECALLW A17 A10 A12).
    - apply (read_cstr_of_rdn RSEGS M _ path Hplen path_nonul Hstr).
    - exact Hpne.
    - apply (V10OpenFail.path_plain a0s path Hva). exact Hpnd.
    - rewrite m0_fs. exact Hfile.
    - rewrite m0_fds. apply fd_lookup_init_3.
    - exact HA.
    - exact HB.
  Qed.

  (* [comment removed for export] *)
  Theorem open_dir_pipeline : forall KA KB,
    path = dot_path ->
    open_err_branch KA -> at_malloc FdDir KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros KA KB Hdot HKA HKB.
    apply (open_pipeline_gen FdDir KA KB); [| exact HKA | exact HKB].
    intros R M A17 A10 A12 Hstr HA HB.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_dir_at RSEGS R _ M model0 ECALLW KA KB m0_pure HF is_ecall_ECALLW A17 A10 A12).
    - replace Uapi.dot_path with path by (rewrite Hdot; reflexivity).
      apply (read_cstr_of_rdn RSEGS M _ path ltac:(rewrite Hdot; cbn; lia) path_nonul Hstr).
    - rewrite m0_fds. apply fd_lookup_init_3.
    - exact HA.
    - exact HB.
  Qed.
End Open.
End V10Open.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require LibKnowXfer.
Module V10ReadLoop_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10Open_defs.
Import V10Oom_defs.
Import V10DirRead_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSL : list Z := (0x152d8 :: 0x15308 :: 0x152a0 :: STOPS3)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSL scr ss [].
Definition NXL : nat := 41.
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_L : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x45480; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; ELit 3; EVar 8; ELit 0x35379; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x45480; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_F : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x45480; J 5; J 6; J 7;
   ELit 2; J 9; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 8; ELit 3; EVar 8; ELit 0x35379; EVar 6;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_ML : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-8388608)) 8388608;
   (* [comment removed for export] *)
   KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-88)) 8 (spx 32); KWord (SA (EVar 0) (-80)) 8 (ELit 0x1520c);
   KWord (SA (EVar 0) (-72)) 8 (ELit 2); KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-56)) 8 (ELit 0x2a9d4);
   (* [comment removed for export] *)
   KRange (EVar 6) 0x66000 0x7fffff7f0000; KAlign (EVar 6) 16; KWr (SA (EVar 6) 0) 65536;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 6) 0) 65536;
   (* [comment removed for export] *)
   KWr (SA (ELit 0) 0x34000) 204800;
   KImg 0x10000 0x35330; KImg 0x35331 0x35379; KImg 0x45379 0x453b0; KImg 0x65488 0x654a8;
   KWord (SA (ELit 0) 0x453b8) 8 (ELit 0x453b8); KWord (SA (ELit 0) 0x453d8) 4 (EVar 5);
   KImg 0x453e4 0x45430; KImg 0x45438 0x45450; KImg 0x45458 0x45470; KImg 0x45480 0x45490; KImg 0x45498 0x65488; KImg 0x654c0 0x656e8;
   KBlob (SA (ELit 0) 0x656e8) (ELit 8) 2; KImg 0x656f0 0x656f8; KImg 0x65709 0x65710;
   KWord (SA (ELit 0) 0x65710) 8 (EVar 3); KImg 0x65718 0x65720; KImg 0x65730 0x65738;
   KWord (SA (ELit 0) 0x65738) 8 (ELit 4096); KImg 0x65740 0x65770; KImg 0x65b28 0x66000;
   KRange (EVar 5) 1 4194303; KImg 0 0x1000].

(* [comment removed for export] *)
Definition rvl9 (ebuf elen ecap : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; ebuf; elen; ecap] ++ (ELit 0 :: tl sr).
Definition idb (k : nat) : nat := k.

(* [comment removed for export] *)
Definition e_r := Eval vm_compute in runL (SCR [false] [] []) d_ssR0.      (* [comment removed for export] *)
Definition e_sr : list expr := Eval vm_compute in s_regs (fst (fst e_r)).
Definition e_kn : list kentry := Eval vm_compute in kn_after e_r ok_kn.
Definition e_rvl : list expr := rvl9 (EVar 48) (ELit 0) (ELit 65536) e_sr.

(* [comment removed for export] *)
Definition l_ssA : sym_state := SS 0x152d8 sr_L [] kn_ML NXL.
Definition l_rAn := Eval vm_compute in runL (SCR [false] [] []) l_ssA.   (* [comment removed for export] *)
Definition l_rAt := Eval vm_compute in runL (SCR [true] [] []) l_ssA.    (* [comment removed for export] *)
Definition l_srAn : list expr := Eval vm_compute in s_regs (fst (fst l_rAn)).
Definition l_srAt : list expr := Eval vm_compute in s_regs (fst (fst l_rAt)).
Definition l_knA : list kentry := Eval vm_compute in kn_after l_rAn kn_ML.
(* [comment removed for export] *)
Definition l_srR (e : expr) : list expr := sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) e.
Definition l_knR : list kentry := Eval vm_compute in kn_frame l_knA (ELit 0) 0x35379 65536.

(* [comment removed for export] *)
Definition l_rC := Eval vm_compute in runL scr0 (SS 0x32c60 (l_srR (ELit 0)) [] l_knR 42).
Definition l_srC : list expr := Eval vm_compute in s_regs (fst (fst l_rC)).
Definition l_knC : list kentry := Eval vm_compute in kn_after l_rC l_knR.
Definition l_rC2 := Eval vm_compute in runL scr0 (SS 0x32c60 (sr_upd l_srC (ridx 10) (ELit 0)) [] l_knC 42).
Definition l_srC2 : list expr := Eval vm_compute in s_regs (fst (fst l_rC2)).
Definition l_knC2 : list kentry := Eval vm_compute in kn_after l_rC2 l_knC.
Definition h_rvl : list expr := rvl9 (EVar 6) (EVar 7) (EVar 8) l_srC2.

(* [comment removed for export] *)
Definition l_knRB : list kentry := KRange (EVar 42) 1 65536 :: l_knR.
Definition l_rB := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x32c60 (l_srR (EVar 42)) [] l_knRB 43).
Definition l_srB : list expr := Eval vm_compute in s_regs (fst (fst l_rB)).
Definition l_knB : list kentry := Eval vm_compute in kn_after l_rB l_knRB.

(* [comment removed for export] *)
Definition l_srD0 : list expr := Eval vm_compute in sr_after_call_j l_srB KEPT_MC 43.
Definition l_knD0 : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x34000 l_knB.
Definition l_rDn := Eval vm_compute in runL (SCR [false] [] []) (SS 0x1528c l_srD0 [] l_knD0 75).  (* [comment removed for export] *)
Definition l_rDt := Eval vm_compute in runL (SCR [true] [] []) (SS 0x1528c l_srD0 [] l_knD0 75).   (* [comment removed for export] *)
Definition l_srDn : list expr := Eval vm_compute in s_regs (fst (fst l_rDn)).
Definition l_srDt : list expr := Eval vm_compute in s_regs (fst (fst l_rDt)).
Definition l_knD : list kentry := Eval vm_compute in kn_after l_rDn l_knD0.
Definition d_rvl : list expr := rvl9 (EVar 6) (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8) l_srDn.
Definition f_rvl : list expr := rvl9 (EVar 6) (EVar 8) (EVar 8) l_srDt.

(* [comment removed for export] *)
Definition want_x : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 7)) (EVar 8).

Section VP1.
(* [comment removed for export] *)
Lemma e_itin :
  (s_pc (fst (fst e_r)), snd (fst e_r), s_log (fst (fst e_r))) = (0x152d8%Z, [], [])
  /\ (sr_mismatch e_rvl idb e_sr sr_L 0, kn_missing e_kn (map (kmap e_rvl idb) kn_ML)) = ([0%nat], []).
Proof. vm_compute. split; reflexivity. Qed.

Lemma l_itinA :
  (s_pc (fst (fst l_rAn)), snd (fst l_rAn), log_win_b 0 (s_log (fst (fst l_rAn))))
    = (0x32c5c%Z, [SCBr false BC_LTU want_x (ELit 65536)], true)
  /\ (s_pc (fst (fst l_rAt)), snd (fst l_rAt), log_win_b 0 (s_log (fst (fst l_rAt))))
    = (0x32c5c%Z, [SCBr true BC_LTU want_x (ELit 65536)], true)
  /\ kn_after l_rAt kn_ML = l_knA
  /\ (nth 17 l_srAn (ELit 0), nth 10 l_srAn (ELit 0), nth 11 l_srAn (ELit 0), nth 12 l_srAn (ELit 0))
     = (ELit 63, ELit 3, ELit 0x35379, ELit 65536)
  /\ nth 12 l_srAt (ELit 0) = want_x
  /\ sr_upd l_srAt (ridx 12) (EVar 41) = sr_upd l_srAn (ridx 12) (EVar 41)
  /\ sr_vars_lt 41 l_srAn = true /\ sr_vars_lt 41 l_srAt = true /\ kn_vars_lt 41 l_knA = true
  /\ kn_frame l_knA (ELit 0) 0x35379 65536 = l_knR
  /\ sr_vars_lt 42 (sr_upd l_srAn (ridx 12) (EVar 41)) = true /\ kn_vars_lt 42 l_knR = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma l_itinC :
  (s_pc (fst (fst l_rC)), snd (fst l_rC), log_win_b 0 (s_log (fst (fst l_rC))), nth 17 l_srC (ELit 0), nth 10 l_srC (ELit 0))
    = (0x32c5c%Z, [], true, ELit 57, ELit 3)
  /\ (s_pc (fst (fst l_rC2)), snd (fst l_rC2), s_log (fst (fst l_rC2))) = (0x15308%Z, [], [])
  /\ (sr_mismatch h_rvl idb l_srC2 sr_H 0, kn_missing l_knC2 (map (kmap h_rvl idb) kn_ML)) = ([], []).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma l_itinB :
  (s_pc (fst (fst l_rB)), snd (fst l_rB), log_win_b 0 (s_log (fst (fst l_rB)))) = (0x3233c%Z, [], true)
  /\ (nth 1 l_srB (ELit 0), nth 10 l_srB (ELit 0), nth 11 l_srB (ELit 0), nth 12 l_srB (ELit 0))
     = (ELit 0x1528c, EAlu ALU_ADD (EVar 6) (EVar 7), ELit 0x35379, EVar 42)
  /\ sr_vars_lt 43 l_srB = true /\ kn_vars_lt 43 l_knB = true
  /\ sr_after_call_j l_srB KEPT_MC 43 = l_srD0 /\ kn_call [] 0 0 IHI 0x34000 l_knB = l_knD0 /\ kn_vars_lt 43 l_knD0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma l_itinD :
  (s_pc (fst (fst l_rDn)), snd (fst l_rDn), s_log (fst (fst l_rDn)))
    = (0x152d8%Z, [SCBr false BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ (s_pc (fst (fst l_rDt)), snd (fst l_rDt), s_log (fst (fst l_rDt)))
    = (0x152a0%Z, [SCBr true BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ kn_after l_rDt l_knD0 = l_knD
  /\ (sr_mismatch d_rvl idb l_srDn sr_L 0, kn_missing l_knD (map (kmap d_rvl idb) kn_ML))
     = ([0%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ (sr_mismatch f_rvl idb l_srDt sr_F 0, kn_missing l_knD (map (kmap f_rvl idb) kn_ML))
     = ([0%nat; 19%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ nth 19 l_srDt (ELit 0) = EAlu ALU_ADD (EVar 7) (EVar 42).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10ReadLoop_defs.

Module V10Usage.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10MainEntryN.
Import V10Usage_defs.
Import V10Usage_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10StartupDefs. Import V10Kit.V10ExitBase. Import V10ExitR23.V10Exit. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memchr. Import V10Kit.V10Strnlen. Import V10Kit.V10Startup. Import V10Kit.V10StartupFacts.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Usage.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 av envv.   (* [comment removed for export] *)

  Definition BL : list (list byte) := [[]; []; guard_bytes a_draw].   (* [comment removed for export] *)
  Hypothesis Hargc : length av <> 2%nat.

  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC av envv fs0 stdin0)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

  Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
  Proof.
    destruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
    inversion Hn; subst. assumption.
  Qed.

  Lemma hd_nth : hd [] av = nth 0 av [].
  Proof. destruct av; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE7_word. cbn [mem_denot u_logM1].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    f_equal; f_equal; lia.
  Qed.

  Lemma pre7_len_w : length (word_to_le_bytes 7 (Z_to_bv 64 9071406455288693)) = 7%nat.
  Proof. apply length_N_to_le_bytes. Qed.

  Theorem ref_usage :
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (HR : regs_ok (EN sp0 av envv tid regs0) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
    assert (HK : know_ok RSEGS (EN sp0 av envv tid regs0) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
    assert (Hac : ev (EN sp0 av envv tid regs0) 16 = argcN av) by (eapply evN_argc; eassumption).
    change (EN sp0 av envv tid regs0) with (ENV BL (valsN sp0 av envv tid regs0)) in HR, HK, Hac.
    set (vals := valsN sp0 av envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold valsN; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0N sp0 av envv) by reflexivity.
    cbn [ev ENV] in Hac.
    assert (STR := fun k Hk => main_strN sp0 av envv tid regs0 mem0 Hva Hve Hvsp ME k Hk) || idtac.
    edestruct (main_strN sp0 av envv tid regs0 mem0) as (Sr & Slo & Shi & Slen & t8 & Ht8); try eassumption.
    1:{ instantiate (1 := 0%nat). lia. }
    rewrite <- hd_nth in Sr, Slen, Ht8. set (a0s := hd [] av) in *.
    pose proof (u64_range (cat_argv_ptr sp0 av envv 0)) as Hppr.
    clearbody vals.
    pose proof model0_halted as Hh.
    (* [comment removed for export] *)
    run_blk_keep u_scrA 38%nat.
    { unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN av Hva). change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV BL vals) mem0 _ 0%nat 0x66000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x108b7) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x108b7 7) in exact i)
                 _ _ 0x108b7 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x108b7) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2d61c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x108b7) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x108b7) 7 _ (seg_rom RSEGS) MC Rc (0x2d61c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
    replace (0x2d61c : word) with (Z_to_bv 64 0x2d61c) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = p0N sp0 av envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    rewrite <- model0_fs.
    pose proof (main_strN_fits sp0 av envv Hva Hve Hvsp 0%nat ltac:(lia) Hfits) as Hfit0. rewrite <- hd_nth in Hfit0.
    eapply (us_tail sp0 BL model0 Hvsp model0_halted model0_lazy model0_fd2 a0s (p0N sp0 av envv) t8 vals1); try eassumption.
    - apply a0s_nonul.
    - unfold p0N. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  Corollary ref_usage_w :
    realizes RSEGS (mkCfg (mkst regs0 (0x1520c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    replace (0x1520c : word) with (Z_to_bv 64 0x1520c) by (apply bv_eq; reflexivity). apply ref_usage.
  Qed.

End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10Usage.

Module V10Grow_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10Open_defs.
Import V10Oom_defs.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSG : list Z := (0x15454 :: STOPSL)%Z.
Definition runG (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSG scr ss [].

(* [comment removed for export] *)
Definition g_ss1 : sym_state := SS 0x152a0 sr_F [] kn_ML NXL.
Definition g_r1n := Eval vm_compute in runG (SCR [false] [] []) g_ss1.    (* [comment removed for export] *)
Definition g_r1t := Eval vm_compute in runG (SCR [true] [] []) g_ss1.     (* [comment removed for export] *)
Definition g_sr1 : list expr := Eval vm_compute in s_regs (fst (fst g_r1n)).
Definition g_kn1 : list kentry := Eval vm_compute in kn_after g_r1n kn_ML.
Definition g_sr1t : list expr := Eval vm_compute in s_regs (fst (fst g_r1t)).
Definition cap2_x : expr := Eval vm_compute in nth 10 g_sr1 (ELit 0).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition g_srM : list expr := sr_after_call_j g_sr1 KEPT_AL 41.
Definition g_knM : list kentry := Eval vm_compute in kn_acall g_kn1.
(* [comment removed for export] *)
Definition g_knOK : list kentry :=
  KRange (EVar 51) 0x66000 0x7fffff7f0000 :: KAlign (EVar 51) 16 :: KWr (SA (EVar 51) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 51) 0) 65536 :: g_knM.

(* [comment removed for export] *)
Definition g_r2 := Eval vm_compute in runG (SCR [false; false] [] []) (SS 0x152b4 g_srM [] g_knOK 73).
Definition g_sr2 : list expr := Eval vm_compute in s_regs (fst (fst g_r2)).
Definition g_kn2 : list kentry := Eval vm_compute in kn_after g_r2 g_knOK.

(* [comment removed for export] *)
Definition g_sr3i : list expr := Eval vm_compute in sr_after_call_j g_sr2 KEPT_MC 73.
Definition g_kn3i : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x34000 g_kn2.
Definition g_r3 := Eval vm_compute in runG scr0 (SS 0x152d0 g_sr3i [] g_kn3i 105).
Definition g_sr3 : list expr := Eval vm_compute in s_regs (fst (fst g_r3)).
Definition g_kn3 : list kentry := Eval vm_compute in kn_after g_r3 g_kn3i.

(* [comment removed for export] *)
Definition g_srL : list expr := Eval vm_compute in sr_after_call_j g_sr3 KEPT_AL 105.
Definition g_knL : list kentry := Eval vm_compute in kn_acall g_kn3.
Definition g_rvl : list expr := rvl9 (EVar 51) (EVar 8) cap2_x g_srL.

Section VP1.
Lemma g_itin1 :
  (s_pc (fst (fst g_r1n)), snd (fst g_r1n), s_log (fst (fst g_r1n)))
    = (0x2b348%Z, [SCBr false BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ (nth 1 g_sr1 (ELit 0), nth 10 g_sr1 (ELit 0), nth 2 g_sr1 (ELit 0), nth 4 g_sr1 (ELit 0))
     = (ELit 0x152b4, cap2_x, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x45480)
  /\ cap2_x = EMd M_MUL (ELit 2) (EVar 8)
  /\ (s_pc (fst (fst g_r1t)), snd (fst g_r1t), s_log (fst (fst g_r1t)))
    = (0x15454%Z, [SCBr true BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ kn_after g_r1t kn_ML = kn_ML
  /\ (nth 2 g_sr1t (ELit 0), nth 3 g_sr1t (ELit 0), nth 4 g_sr1t (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x45480)
  /\ kn_vars_lt 41 g_kn1 = true /\ kn_acall g_kn1 = g_knM.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma g_itin2 :
  (s_pc (fst (fst g_r2)), snd (fst g_r2), s_log (fst (fst g_r2))) = (0x3233c%Z, [SCBr false BC_EQ (EVar 8) (ELit 0)], [])
  /\ (nth 1 g_sr2 (ELit 0), nth 10 g_sr2 (ELit 0), nth 11 g_sr2 (ELit 0), nth 12 g_sr2 (ELit 0))
     = (ELit 0x152d0, EVar 51, EVar 6, EVar 8)
  /\ sr_vars_lt 73 g_sr2 = true /\ kn_vars_lt 73 g_kn2 = true
  /\ sr_after_call_j g_sr2 KEPT_MC 73 = g_sr3i /\ kn_call [] 0 0 IHI 0x34000 g_kn2 = g_kn3i /\ kn_vars_lt 73 g_kn3i = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma g_itin3 :
  (s_pc (fst (fst g_r3)), snd (fst g_r3), s_log (fst (fst g_r3))) = (0x2b208%Z, [], [])
  /\ (nth 1 g_sr3 (ELit 0), nth 10 g_sr3 (ELit 0), nth 2 g_sr3 (ELit 0), nth 4 g_sr3 (ELit 0))
     = (ELit 0x152d8, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x45480)
  /\ kn_vars_lt 105 g_kn3 = true /\ kn_acall g_kn3 = g_knL
  /\ (sr_mismatch g_rvl idb g_srL sr_L 0, kn_missing g_knL (map (kmap g_rvl idb) kn_ML)) = ([0%nat], [KWr (SA (EVar 51) 0) 65536]).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10Grow_defs.

Module V10Hdr_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10Open_defs.
Import V10Oom_defs.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSH : list Z := (0x154dc :: STOPSL)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH scr ss [].
Definition STOPSH2 : list Z := (0x15400 :: STOPSH)%Z.
Definition runH2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH2 scr ss [].

(* [comment removed for export] *)
Definition kn_H6 : list kentry :=
  KWord (SA (EVar 6) 0) 1 (EVar 41) :: KWord (SA (EVar 6) 1) 1 (EVar 42) :: KWord (SA (EVar 6) 2) 1 (EVar 43)
  :: KRange (EVar 41) 0 255 :: KRange (EVar 42) 0 255 :: KRange (EVar 43) 0 255 :: kn_ML.

(* [comment removed for export] *)
Definition h_rS := Eval vm_compute in runH (SCR [true] [] []) (SS 0x15308 sr_H [] kn_ML 41).
Definition h_srS : list expr := Eval vm_compute in s_regs (fst (fst h_rS)).
Definition h_knS : list kentry := Eval vm_compute in kn_after h_rS kn_ML.
Definition h_scS : stdio_res := Eval vm_compute in sc_of 41 h_srS h_knS.
(* [comment removed for export] *)
Definition h_srS2i : list expr := Eval vm_compute in sc_sr h_scS.
Definition h_knS2i : list kentry := Eval vm_compute in sc_kn h_scS.
Definition h_rS2 := Eval vm_compute in runH2 scr0 (SS 0x2d6d8 h_srS2i [] h_knS2i 73).
Definition h_srS2 : list expr := Eval vm_compute in s_regs (fst (fst h_rS2)).
Definition h_knS2 : list kentry := Eval vm_compute in kn_after h_rS2 h_knS2i.

(* [comment removed for export] *)
Definition h_rK := Eval vm_compute in runH (SCR [false; false] [] []) (SS 0x15308 sr_H [] kn_H6 44).
Definition h_srK : list expr := Eval vm_compute in s_regs (fst (fst h_rK)).
Definition h_knK : list kentry := Eval vm_compute in kn_after h_rK kn_H6.

Definition cfglen_x : expr := Eval vm_compute in nth 18 h_srK (ELit 0).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_rO := Eval vm_compute in runH (SCR [false; true] [] []) (SS 0x15308 sr_H [] kn_H6 44).
Definition h_srO : list expr := Eval vm_compute in s_regs (fst (fst h_rO)).
Definition h_knO : list kentry := Eval vm_compute in kn_after h_rO kn_H6.
Definition h_scO : stdio_res := Eval vm_compute in sc_of 44 h_srO h_knO.
Definition h_srO2i : list expr := Eval vm_compute in sc_sr h_scO.
Definition h_knO2i : list kentry := Eval vm_compute in sc_kn h_scO.
Definition h_rO2 := Eval vm_compute in runH2 scr0 (SS 0x2d6d8 h_srO2i [] h_knO2i 76).
Definition h_srO2 : list expr := Eval vm_compute in s_regs (fst (fst h_rO2)).
Definition h_knO2 : list kentry := Eval vm_compute in kn_after h_rO2 h_knO2i.

(* [comment removed for export] *)
Definition JF (i : nat) : expr := EVar (7 + i).
Definition sr_F2 : list expr :=
  [ELit 0; JF 1; spx (-128); ELit 0x10800; ELit 0x45480; JF 5; JF 6; JF 7;
   ELit 2; EVar 6; JF 10; JF 11; JF 12; JF 13; JF 14; JF 15;
   JF 16; JF 17; JF 18; JF 19; JF 20; JF 21; JF 22; JF 23;
   JF 24; JF 25; JF 26; JF 27; JF 28; JF 29; JF 30; JF 31].
Definition kn_F2 : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) h_knO2.
Definition f_rvlS : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srS2).
Definition f_rvlO : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srO2).
(* [comment removed for export] *)
Definition f_r1 := Eval vm_compute in runH scr0 (SS 0x15400 sr_F2 [] kn_F2 39).
Definition f_sr1 : list expr := Eval vm_compute in s_regs (fst (fst f_r1)).
Definition f_kn1 : list kentry := Eval vm_compute in kn_after f_r1 kn_F2.
(* [comment removed for export] *)
Definition f_sr2i : list expr := Eval vm_compute in sr_after_call_j f_sr1 KEPT_AL 39.
Definition f_kn2i : list kentry := Eval vm_compute in kn_acall f_kn1.
Definition f_r2 := Eval vm_compute in runH scr0 (SS 0x15408 f_sr2i [] f_kn2i 71).
Definition f_sr2 : list expr := Eval vm_compute in s_regs (fst (fst f_r2)).
Definition f_kn2 : list kentry := Eval vm_compute in kn_after f_r2 f_kn2i.

Definition paylen_x : expr := Eval vm_compute in nth 13 h_srK (ELit 0).    (* [comment removed for export] *)
Definition pay_x : expr := Eval vm_compute in nth 12 h_srK (ELit 0).       (* [comment removed for export] *)
Definition b1s_x : expr := EExt true 0 1 (EVar 42).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JR (i : nat) : expr := EVar (13 + i).
Definition sr_R : list expr :=
  [ELit 0; ELit 0x15380; spx (-128); ELit 0x10800; ELit 0x45480; JR 5; JR 6; JR 7;
   EAlu ALU_ADD (EVar 6) (ELit 2); EVar 6; EAlu ALU_ADD (EVar 6) (ELit 2); EVar 8; EVar 12; EVar 9; JR 14; JR 15;
   JR 16; JR 17; EVar 8; EVar 12; EVar 9; EVar 10; JR 22; JR 23;
   JR 24; JR 25; JR 26; JR 27; JR 28; JR 29; JR 30; JR 31].
Definition kn_R : list kentry := KWord (SA (EVar 6) 2) 1 (EVar 11) :: KRange (EVar 11) 0 255 :: kn_ML.
Definition NXR : nat := 45.
Definition r_rvl : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; cfglen_x; paylen_x; b1s_x; EVar 43; pay_x] ++ (ELit 0 :: tl h_srK).

(* [comment removed for export] *)
Definition cfgF (v41 v42 : word) : word :=
  edenot (Env (fun n => match n with 41%nat => v41 | 42%nat => v42 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_x.
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma cfgF_tab :
  forallb (fun b1 => forallb (fun b0 =>
     Z.eqb (bv_unsigned (cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
     (zseq 256)) (zseq 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)

Section VP1.
Lemma h_itinS :
  (s_pc (fst (fst h_rS)), snd (fst h_rS)) = (0x2d23c%Z, [SCBr true BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 41 h_srS h_knS = Some h_scS
  /\ (sc_ret h_scS, sc_f h_scS, sc_fd h_scS, sc_s h_scS, sc_l h_scS) = (0x2d6d8%Z, 0x35140%Z, 2%Z, ELit 0x114cc, ELit 31)
  /\ (s_pc (fst (fst h_rS2)), snd (fst h_rS2), log_win_b 0 (s_log (fst (fst h_rS2)))) = (0x15400%Z, [], true)
  /\ (sr_mismatch f_rvlS idb h_srS2 sr_F2 0, kn_missing h_knS2 (map (kmap f_rvlS idb) kn_F2)) = ([0%nat], []).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma h_itinO :
  (s_pc (fst (fst h_rO)), snd (fst h_rO)) = (0x2d23c%Z, [SCBr true BC_LTU (EVar 7) (EAlu ALU_ADD cfglen_x (ELit 6)); SCBr false BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 44 h_srO h_knO = Some h_scO
  /\ (sc_ret h_scO, sc_f h_scO, sc_fd h_scO, sc_s h_scO, sc_l h_scO) = (0x2d6d8%Z, 0x35140%Z, 2%Z, ELit 0x108c8, ELit 31)
  /\ (s_pc (fst (fst h_rO2)), snd (fst h_rO2), log_win_b 0 (s_log (fst (fst h_rO2)))) = (0x15400%Z, [], true)
  /\ (sr_mismatch f_rvlO idb h_srO2 sr_F2 0, kn_missing h_knO2 (map (kmap f_rvlO idb) kn_F2)) = ([0%nat], []).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma f_itin :
  (s_pc (fst (fst f_r1)), snd (fst f_r1), s_log (fst (fst f_r1))) = (0x2b208%Z, [], [])
  /\ (nth 1 f_sr1 (ELit 0), nth 10 f_sr1 (ELit 0), nth 2 f_sr1 (ELit 0), nth 4 f_sr1 (ELit 0))
     = (ELit 0x15408, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x45480)
  /\ kn_vars_lt 39 f_kn1 = true /\ kn_acall f_kn1 = f_kn2i
  /\ (s_pc (fst (fst f_r2)), snd (fst f_r2), s_log (fst (fst f_r2))) = (0x2aed0%Z, [], [])
  /\ (nth 10 f_sr2 (ELit 0), nth 2 f_sr2 (ELit 0), nth 4 f_sr2 (ELit 0)) = (ELit 2, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x45480).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma h_itinK :
  (s_pc (fst (fst h_rK)), s_log (fst (fst h_rK)), s_next (fst (fst h_rK))) = (0x154dc%Z, [], 48%nat)
  /\ paylen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 7) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6))
  /\ pay_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 6) cfglen_x) (ELit 6)
  /\ (sr_mismatch r_rvl idb h_srK sr_R 0, kn_missing h_knK (map (kmap r_rvl idb) kn_R)) = ([], []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
End V10Hdr_defs.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocLayout.
Module V10Malloc65536.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10FuzzIface.
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma kept_al_saved : forall i, In i KEPT_AL -> (i < 32)%nat /\ callee_saved (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros i Hi. unfold KEPT_AL in Hi. unfold callee_saved.
  repeat (destruct Hi as [Hi|Hi]; [subst i; split; [lia|];
    first [ left; apply bv_eq; reflexivity | right; left; apply bv_eq; reflexivity
          | right; right; left; apply bv_eq; reflexivity | right; right; right; left; apply bv_eq; reflexivity
          | right; right; right; right; left; apply bv_eq; reflexivity
          | do 5 right; vm_compute; split; discriminate ] |]).
  destruct Hi.
Qed.
Lemma kept_al_no0 : ~ In 0%nat KEPT_AL.
Proof. unfold KEPT_AL. cbn [In]. lia. Qed.

Section Malloc1.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.

  (* [comment removed for export] *)
  Definition env_ok (M : word -> option byte) : Prop :=
    V10Open.above_sp0 sp0 mem0 M
    /\ (forall a : word, (0x453b0 <= bv_unsigned a < 0x65778)%Z -> ~ ((0x453dc <= bv_unsigned a < 0x453e0)%Z \/ (0x654c0 <= bv_unsigned a < 0x656e0)%Z) -> M a = mem0 a)
    /\ (forall a : word, (0x10000 <= bv_unsigned a < 0x33000)%Z \/ (0x33dc0 <= bv_unsigned a < 0x33dc8)%Z -> M a = None).
      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.   (* [comment removed for export] *)
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall z, In z [0x15260; 0x1528c; 0x15308; 0x15408; 0x15538]%Z -> al_ret_ok (Z_to_bv 64 z).
  Hypothesis AL_env : forall M, env_ok M -> al_env sp0 [a0s; path] envv M.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Let ENV := V10Open.ENV a0s path.
  Let vm0 := V10Open.vm0 sp0 brk mbase lim.
  Let model1g := V10Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Definition heap_none (M : word -> option byte) : Prop :=
    forall a : word, (0x66000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z ->
    M a = None.

  (* [comment removed for export] *)
  Lemma mem0_gap_none : heap_none mem0.
  Proof.
    intros a Ha. pose proof (u64_range a) as Hr. pose proof SPlo.
    rewrite (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME) by (rewrite stack_max_size_val; lia).
    pose proof (u64_range tid).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite MemSplit.wbytes_outside;
      [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
        | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); lia ]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mem0_ro_none : forall a : word, (0x10000 <= bv_unsigned a < 0x33000)%Z \/ (0x33dc0 <= bv_unsigned a < 0x33dc8)%Z -> mem0 a = None.
  Proof.
    intros a Ha. pose proof (u64_range a) as Hr. pose proof SPlo.
    rewrite (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME) by (rewrite stack_max_size_val; lia).
    pose proof (u64_range tid).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite MemSplit.wbytes_outside;
      [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
        | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); left + right; lia ]).
    reflexivity.
  Qed.

  Lemma out_win_facts : forall M, V10Open.out_win sp0 mem0 M ->
    V10Open.above_sp0 sp0 mem0 M /\ env_ok M /\ heap_none M.
  Proof.
    intros M H. pose proof SPlo. split; [|split].
    - apply V10Open.out_win_above. exact H.
    - split; [apply V10Open.out_win_above; exact H|]. split.
      + intros a H1 H2. apply H. lia.
      + intros a Ha. rewrite H by lia. apply mem0_ro_none. exact Ha.
    - intros a Ha. rewrite H by lia. apply mem0_gap_none. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition ok_sr : list expr := sr_after_call_j o_srB KEPT_AL 38.
  Definition ok_kn : list kentry :=
    KRange (EVar 48) 0x66000 0x7fffff7f0000 :: KAlign (EVar 48) 16 :: KWr (SA (EVar 48) 0) 65536
    :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 48) 0) 65536 :: kn_acall o_knB.

  Definition at_buf (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall A1 vm1 vals R M,
      length vals = 70%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
      ainv A1 M vm1 -> live A1 (vals_ev vals 48) = Some 65536%Z ->
      (forall q, q <> vals_ev vals 48 -> live A1 q = None) ->
      aroom A1 vm1 (need_k FUZZ_CALLS 0) (need_b FUZZ_BMAX 0 65536) ->
      vm_limit vm1 = lim -> alloc_top vm1 = (bv_unsigned sp0 - 8388608)%Z ->
      vm_init_sp vm1 = sp0 -> vm_reserved vm1 = segments_reserved RSEGS ->
      regs_ok (ENV vals) ok_sr R -> know_ok RSEGS (ENV vals) M ok_kn ->
      env_ok M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15260) M (seg_rom RSEGS)) (with_vmmaps vm1 (model1g fd3))) KB.

  (* [comment removed for export] *)
  Lemma owned0_range : forall a, owned A0 a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Proof. intros a H. apply AL_glob. apply (proj1 (ai_init_owned a)). exact H. Qed.

  Lemma ownedA_range : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z
                 \/ ((0x66000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
  Proof.
    intros A m vm a HI Htop Ho. destruct (ai_owned_where A m vm a HI Ho) as [Hg|[[Hg Hlt] _]].
    - left. apply AL_glob. exact Hg.
    - right. pose proof (AL_grant a Hg). lia.
  Qed.

  Lemma round16_ge0 : forall n, (n <= round16 n)%Z.
  Proof.
    intros n. unfold round16. pose proof (Z.div_mod (n + 15) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_lo : forall A m vm p n, ainv A m vm -> live A p = Some n -> (0 < n)%Z -> (0x1000 <= bv_unsigned p)%Z.
  Proof.
    intros A m vm p n HI Hl Hn. destruct (ai_live_hull A m vm p n HI Hl) as (_ & _ & _ & Hbytes). pose proof (round16_ge0 n).
    destruct (Hbytes 0%Z ltac:(lia)) as (Ho & _ & _ & _).
    destruct (ai_owned_where A m vm _ HI Ho) as [Hg|[[Hg _] _]].
    - exfalso. exact (ai_live_not_globals A m vm p n 0 HI Hl ltac:(lia) Hg).
    - apply AL_grant in Hg. unfold at_ in Hg. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hg. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_big_lo : forall A m vm p n, ainv A m vm -> live A p = Some n -> (61440 < n)%Z -> (0x66000 <= bv_unsigned p)%Z.
  Proof.
    intros A m vm p n HI Hl Hn. pose proof (live_lo A m vm p n HI Hl ltac:(lia)) as Hlo. pose proof (u64_range p).
    destruct (ai_live_hull A m vm p n HI Hl) as (_ & _ & Hend & Hbytes). pose proof (round16_ge0 n).
    destruct (Z_lt_ge_dec (bv_unsigned p) 0x66000) as [Hlt|Hge]; [exfalso | lia].
    assert (CASE : forall i, (0 <= i < round16 n)%Z -> (bv_unsigned p + i < 2 ^ 64)%Z ->
              ~ (0x10000 <= bv_unsigned p + i < 0x66000)%Z).
    { intros i Hi Hw. destruct (Hbytes i Hi) as (Ho & _ & _ & _).
      destruct (ai_owned_where A m vm _ HI Ho) as [Hg|[[Hg _] _]].
      - exfalso. exact (ai_live_not_globals A m vm p n i HI Hl Hi Hg).
      - apply AL_grant in Hg. unfold at_ in Hg. rewrite u_small in Hg by lia. lia. }
    destruct (Z_lt_ge_dec (bv_unsigned p) 0x10000) as [H1|H1].
    - apply (CASE (0x10000 - bv_unsigned p)%Z); lia.
    - apply (CASE 0%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_where : forall A m vm p n, ainv A m vm -> live A p = Some n -> (0 < n)%Z ->
    alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ((0x1000 <= bv_unsigned p)%Z /\ (bv_unsigned p + n <= 0x10000)%Z)
    \/ ((0x66000 <= bv_unsigned p)%Z /\ (bv_unsigned p + n <= bv_unsigned sp0 - 8388608)%Z).
  Proof.
    intros A m vm p n HI Hl Hn Htop. pose proof (live_lo A m vm p n HI Hl Hn) as Hlo. pose proof (u64_range p).
    destruct (ai_live_hull A m vm p n HI Hl) as (_ & _ & Hend & Hbytes). pose proof (round16_ge0 n). rewrite Htop in Hend.
    assert (CASE : forall i, (0 <= i < round16 n)%Z -> (bv_unsigned p + i < 2 ^ 64)%Z ->
              ~ (0x10000 <= bv_unsigned p + i < 0x66000)%Z).
    { intros i Hi Hw. destruct (Hbytes i Hi) as (Ho & _ & _ & _).
      destruct (ai_owned_where A m vm _ HI Ho) as [Hg|[[Hg _] _]].
      - exfalso. exact (ai_live_not_globals A m vm p n i HI Hl Hi Hg).
      - apply AL_grant in Hg. unfold at_ in Hg. rewrite u_small in Hg by lia. lia. }
    pose proof SPlo.
    destruct (Z_lt_ge_dec (bv_unsigned p) 0x66000) as [Hlt|Hge]; [left | right; lia].
    pose proof (CASE 0%Z ltac:(lia) ltac:(lia)).
    destruct (Z_lt_ge_dec 0x10000 (bv_unsigned p + n)) as [Hov|Hov]; [| lia].
    exfalso. apply (CASE (0x10000 - bv_unsigned p)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ainv_frame_driver : forall A M M' vm,
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, M' a <> M a ->
       (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z \/ (0x10000 <= bv_unsigned a < 0x65778)%Z
       \/ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned a < bv_unsigned p + n)%Z)) ->
    mem_grows M M' ->
    (forall a : word, (0x66000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z ->
                      M' a <> None -> M a <> None) ->
    ainv A M' vm.
  Proof.
    intros A M M' vm HI Htop Hchg Hgr Hheap.
    apply (ai_frame A M M' vm HI).
    - intros a Ho Hnl. destruct (M' a) as [b'|] eqn:E1; destruct (M a) as [b|] eqn:E2.
      + destruct (Z.eq_dec (bv_unsigned b') (bv_unsigned b)) as [Hb|Hb].
        * f_equal. apply bv_eq. exact Hb.
        * exfalso. destruct (Hchg a ltac:(rewrite E1, E2; intros HH; injection HH as HH; apply Hb; rewrite HH; reflexivity))
            as [Hw|[Hl|(p & n & Hp & Hin)]].
          -- destruct (ownedA_range A M vm a HI Htop Ho); lia.
          -- destruct (ownedA_range A M vm a HI Htop Ho); lia.
          -- exact (Hnl p n Hp Hin).
      + exfalso. destruct (Hchg a ltac:(rewrite E1, E2; discriminate)) as [Hw|[Hl|(p & n & Hp & Hin)]].
        -- destruct (ownedA_range A M vm a HI Htop Ho); lia.
        -- destruct (ownedA_range A M vm a HI Htop Ho); lia.
        -- exact (Hnl p n Hp Hin).
      + exfalso. apply (Hgr a); [rewrite E2; discriminate | exact E1].
      + reflexivity.
    - intros a Ho HM. apply Hgr. exact HM.
    - intros a [Hg Hlt] HM'. apply (Hheap a); [| exact HM']. pose proof (AL_grant a Hg). lia.
  Qed.

  Lemma vm0_alloc_top : alloc_top vm0 = (bv_unsigned sp0 - 8388608)%Z.
  Proof. unfold alloc_top. rewrite stack_max_size_val. reflexivity. Qed.

  Lemma regs_ok_same10 : forall E sr R e,
    regs_ok E sr R -> getr R 10 = edenot E e -> regs_ok E (sr_upd sr (ridx 10) e) R.
  Proof.
    intros E sr R e HR H10 r.
    pose proof (regs_ok_set E sr R 10 (getr R 10) e HR ltac:(intros H; apply bv_eq in H; discriminate H) (eq_sym H10) r) as H.
    rewrite <- H. destruct (Z.eq_dec (bv_unsigned r) 10) as [Hr|Hr].
    - assert (r = 10%bv) by (apply bv_eq; exact Hr). subst r.
      rewrite getr_same by (intros H0; apply bv_eq in H0; discriminate H0). reflexivity.
    - rewrite getr_other; [reflexivity|]. intros Hc. apply Hr. rewrite Hc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma regs_after_alloc : forall vals R R' ,
    length vals = 38%nat -> regs_ok (ENV vals) o_srB R ->
    (forall r, callee_saved r -> getr R' r = getr R r) ->
    regs_ok (ENV (vals ++ junk_vals R')) (sr_after_call_j o_srB KEPT_AL 38) R'.
  Proof.
    intros vals R R' HL HR Hcs. rewrite <- HL.
    apply (regs_after_call vals _ o_srB R R' KEPT_AL); [rewrite HL; vm_compute; reflexivity | exact HR | | apply kept_al_no0].
    intros i Hi. destruct (kept_al_saved i Hi) as [H32 Hc]. split; [exact H32|]. apply Hcs. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma know_after_alloc : forall (A' : AS) vals (M M' : word -> option byte) vm' R' kn,
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    kn_vars_lt 38%nat kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A0 a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 128 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 128)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A0 a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acall kn).
  Proof.
    intros A' vals M M' vm' R' kn HL P0 Hlt HK HI Htop Hfr Hgr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    unfold kn_acall. apply (know_ok_call RSEGS (ENV (vals ++ junk_vals R')) M M' GLOB A_SLO A_SHI IHI 0x34000).
    - cbn [ev ENV V10Open.ENV]. rewrite vals_ev_app_l by (rewrite HL; lia). rewrite P0. lia.
    - unfold IHI, WIN. lia.
    - unfold A_SLO, A_SHI, WIN. lia.
    - intros x Hnt. unfold touched in Hnt. cbn [ev ENV V10Open.ENV] in Hnt. rewrite vals_ev_app_l in Hnt by (rewrite HL; lia). rewrite P0 in Hnt.
      unfold IHI, WIN, A_SLO, A_SHI, GLOB in Hnt.
      apply Hfr.
      + intros Ho. apply owned0_range in Ho. apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [left; reflexivity | cbn; lia].
      + intros Ho. destruct (ownedA_range A' M' vm' x HI Htop Ho) as [Hg|[Hh|Hl]].
        * apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [left; reflexivity | cbn; lia].
        * apply Hnt. right. left. lia.
        * apply Hnt. left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [right; right; left; reflexivity | cbn; lia].
      + intros He. apply AL_errno in He. apply Hnt. left. split; [lia|]. exists (0x453dc, 0x453e0)%Z.
        split; [right; left; reflexivity | cbn; lia].
      + intros Hs. apply Hnt. right. right. unfold ALLOC_STACK in Hs. lia.
    - intros x Hx HM. cbn [ev ENV V10Open.ENV] in Hx. rewrite vals_ev_app_l in Hx by (rewrite HL; lia). rewrite P0 in Hx.
      unfold WIN in Hx. destruct (Hgr x HM) as [H|[H|H]]; [| | exact H].
      + pose proof AL_hi. exfalso. lia.
      + apply owned0_range in H. exfalso. lia.
    - intros m a n H1 H2. apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2].
    - apply (env_app_know RSEGS vals (junk_vals R') _ M kn); [rewrite HL; exact Hlt | exact HK].
  Qed.

  Theorem malloc65536_node : forall fd3 KB,
    at_buf fd3 KB ->
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
      regs_ok (ENV vals) o_srB R -> know_ok RSEGS (ENV vals) M o_knB ->
      V10Open.out_win sp0 mem0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b348) M (seg_rom RSEGS)) (model1g fd3)) KB.
  Proof.
    intros fd3 KB HKB vals R M HL P0 P1 P2 P5 HR HK HOW.
    destruct (out_win_facts M HOW) as (HA & HE & HN).
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    assert (R10 : getr R 10 = Z_to_bv 64 65536) by (regv HR (10 : reg); reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x15260) by (regv HR (1 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
    { regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV V10Open.ENV].
      rewrite P0. first [reflexivity | f_equal; lia]. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 0x65778 944) in exact i) _ HK eq_refl) as KG;
      cbn [kentry_ok] in KG;
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW
    end.
    destruct KG as (_ & _ & KG).
    (* [comment removed for export] *)
    assert (EQcfg : mkst R (Z_to_bv 64 0x2b348) M (seg_rom RSEGS) = mkst R al_malloc_pc M al_rom)
      by (rewrite AL_malloc, AL_rom; reflexivity).
    rewrite EQcfg. rewrite <- AL_segs.
    assert (HIL : init_ledger vm0).
    { constructor; try reflexivity.
      - rewrite AL_segs. reflexivity.
      - rewrite AL_segs. exact Hbrk.
      - exact Hvsp. }
    pose proof fuzz_room_fits as (HFK & HFB). pose proof fuzz_calls_nonneg as HFC0.
    pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    eapply (ai_malloc_sure fx0 A0 M (model1g fd3) R 65536 (room_k0 FUZZ_CALLS) (room_b0 FUZZ_BMAX)
              (Z_to_bv 64 0x15260) sp0 [a0s; path] envv KB).
    - (* [comment removed for export] *)
      change (m_vmmaps (model1g fd3)) with vm0. apply ai_init.
      + exact HIL.
      + intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply KG. pose proof (AL_glob a Ha). lia.
      + intros a [Hg Hlt]. apply HN. pose proof (AL_grant a Hg). rewrite vm0_alloc_top in Hlt. lia.
    - apply V10Open.m1_pure.
    - apply AL_env. exact HE.
    - exact R10.
    - lia.
    - (* [comment removed for export] *)
      change (m_vmmaps (model1g fd3)) with vm0. apply aroom_init.
      + exact HIL.
      + change (vm_limit vm0) with lim. unfold ROOM_BCAP. lia.
      + unfold room_k0, DRV_CALLS in *. lia.
      + unfold room_b0, DRV_BYTES in *. lia.
    - unfold room_k0, DRV_CALLS. lia.
    - pose proof (alloc_margin_le 65536). unfold room_b0, DRV_BYTES. lia.
    - unfold ROOM_NMAX. lia.
    - exact R1.
    - apply AL_ret. cbn. tauto.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps (model1g fd3)) with vm0. rewrite vm0_alloc_top. rewrite R2, u_small by lia. lia.
    - rewrite R2, u_small by lia. lia.
    - (* [comment removed for export] *)
      intros a Ha. rewrite R2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. apply owned0_range in Ho. lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - (* [comment removed for export] *)
      intros A' m' vm' regs' res HI' Ha0 Hcs Hnz Hl0 Hl1 Hlq Hnew Hfr Hlm Hgr Hvl Htop Hisp Hres Hroom.
      rewrite AL_segs, AL_rom.
      pose proof Htop as Htop'. change (m_vmmaps (model1g fd3)) with vm0 in Htop'. rewrite vm0_alloc_top in Htop'.
      change (m_vmmaps (model1g fd3)) with vm0 in Hvl, Hisp, Hres.
      destruct (ai_live_hull A' m' vm' res 65536 HI' Hl1) as (_ & Hal16 & Hend & Hbytes).
      change (round16 65536) with 65536%Z in Hend, Hbytes.
      assert (Hlo31 : (0x66000 <= bv_unsigned res)%Z) by (apply (live_big_lo A' m' vm' res 65536 HI' Hl1); lia).
      assert (A48 : vals_ev (vals ++ junk_vals regs') 48 = res).
      { replace 48%nat with (length vals + 10)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r.
        unfold junk_vals, vals_ev. rewrite (nth_map_seq_gen _ 32 0 10) by lia. cbn [Nat.add]. rewrite <- Ha0. reflexivity. }
      apply (HKB A' vm' (vals ++ junk_vals regs') regs' m').
      + rewrite length_app, junk_vals_length, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5.
      + exact HI'.
      + rewrite A48. exact Hl1.
      + intros q Hq. rewrite A48 in Hq. rewrite (Hlq q Hq). apply ai_init_live.
      + (* [comment removed for export] *)
        destruct (need0 FUZZ_CALLS FUZZ_BMAX) as (EK & EB). pose proof (alloc_margin_le 65536) as HM.
        pose proof (need_lo FUZZ_CALLS FUZZ_BMAX 0 65536 HFC0 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as (HK0 & HB0).
        apply (aroom_mono A' vm' _ _ _ _ Hroom); lia.
      + rewrite Hvl. reflexivity.
      + exact Htop'.
      + rewrite Hisp. reflexivity.
      + rewrite Hres. reflexivity.
      + unfold ok_sr. apply (regs_after_alloc vals R regs' HL HR Hcs).
      + (* [comment removed for export] *)
        unfold ok_kn. pose proof (u64_range res) as Hrr.
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]]].
        * cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite A48. lia.
        * cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite A48. split; [lia | exact Hal16].
        * cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot ev ENV V10Open.ENV]. rewrite A48. split; [lia|].
          intros d m Hd Hm. apply store_ok_of_all; [rewrite u_small by lia; lia|].
          intros x Hx. rewrite u_small in Hx by lia.
          destruct (Hbytes (bv_unsigned x - bv_unsigned res)%Z ltac:(lia)) as (_ & Hsome & _ & _).
          unfold at_ in Hsome. replace (bv_unsigned res + (bv_unsigned x - bv_unsigned res))%Z with (bv_unsigned x) in Hsome by lia.
          rewrite Z_to_bv_bv_unsigned in Hsome. unfold wview. destruct (m' x); [discriminate | exfalso; exact (Hsome eq_refl)].
        * cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev ENV V10Open.ENV].
          rewrite vals_ev_app_l by (rewrite HL; lia). rewrite P0, A48. right. lia.
        * eapply (know_after_alloc A' vals M m' vm' regs' o_knB HL P0 ltac:(vm_compute; reflexivity) HK HI' Htop').
          -- intros a H1 H2 H3 H4. apply Hfr; try assumption. rewrite R2, u_small by lia. exact H4.
          -- exact Hgr.
      + (* [comment removed for export] *)
        destruct HE as (HEa & HEl & HEr). split; [|split].
        * intros a Ha. rewrite Hfr; [apply HA; exact Ha | | | |].
          -- intros Ho. apply owned0_range in Ho. lia.
          -- intros Ho. destruct (ownedA_range A' m' vm' a HI' Htop' Ho); lia.
          -- intros He. apply AL_errno in He. lia.
          -- rewrite R2, u_small by lia. unfold ALLOC_STACK. lia.
        * intros a H1 H2. rewrite Hfr; [apply HEl; assumption | | | |].
          -- intros Ho. apply owned0_range in Ho. lia.
          -- intros Ho. destruct (ownedA_range A' m' vm' a HI' Htop' Ho); lia.
          -- intros He. apply AL_errno in He. lia.
          -- rewrite R2, u_small by lia. unfold ALLOC_STACK. lia.
        * intros a Ha. rewrite Hfr; [apply HEr; exact Ha | | | |].
          -- intros Ho. apply owned0_range in Ho. lia.
          -- intros Ho. destruct (ownedA_range A' m' vm' a HI' Htop' Ho); lia.
          -- intros He. apply AL_errno in He. lia.
          -- rewrite R2, u_small by lia. unfold ALLOC_STACK. lia.
  Qed.
End Malloc1.
End V10Malloc65536.

Module V10OpenFailBranch.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail.
Import V10Open_defs.
Import V10Open.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import V10Kit.V10Startup.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Section Branch.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.

  Theorem open_err_branch_cannot_open :
    V10Open.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
    rewrite (V10Open.model0_OF sp0 a0s path envv tid brk mbase fs0 stdin0 lim).
    apply (V10OpenFail.ref_open_fail_errno sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp ME Hfits
             e vals R M (openat_errnos_range e He) HL P0 P38 P2 HR HK Habove).
  Qed.
End Branch.
End V10OpenFailBranch.

Module V10DirRead.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10ReadErr.
Import V10Malloc65536.
Import V10DirRead_defs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS3 scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS3 scr NX true.

(* [comment removed for export] *)
Lemma kimg_clear : forall E M kn lo hi,
  know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
Proof.
  intros E M kn lo hi HK Hex. apply existsb_exists in Hex as (K & Hin & Hc).
  destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hn).
  intros i Hi. apply Hn. lia.
Qed.

Definition is_kblob_at (a : Z) (K : kentry) : bool :=
  match K with KBlob (SA (ELit 0) k) _ _ => (k =? a)%Z | _ => false end.

Section DirRead.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model1g := V10Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem dir_read_error :
    path = dot_path ->
    V10Malloc65536.at_buf sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim FdDir (t_die (msg_read_error path) fs0).
  Proof.
    intros Hdot A1 vm1 vals R M HL P0 P1 P2 P5 HI Hlive Hlq Hroom Hvl Htop Hisp Hres HR HK HE.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct HE as [HA HEl].
    unfold model1g, V10Open.model1g. rewrite with_vmmaps_C.
    set (model := mkModelC (V10Open.fds1g FdDir) vm1 stdin0 fs0 None (Some tid) None).
    assert (Hh : m_halted model = None) by reflexivity.
    change (V10Malloc65536.ok_sr) with ok_sr in HR. change (V10Malloc65536.ok_kn) with ok_kn in HK.
    (* [comment removed for export] *)
    run_blk_keep d_scrR0 70%nat.
    assert (HA1 : V10Open.above_sp0 sp0 mem0 M0).
    { intros x Hx. rewrite EQM. rewrite (mem_denot_above (ENV vals) M _ 0%nat 0x66000);
        [apply HA; exact Hx | vm_compute; reflexivity | cbn [ev ENV V10Open.ENV]; rewrite P0; lia | cbn [ev ENV V10Open.ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      assert (A17 : bv_unsigned (getr Rc 17) = 63%Z) by (regv HR (17 : reg); reflexivity);
      assert (A10 : getr Rc 10 = Z_to_bv 64 3) by (regv HR (10 : reg); reflexivity);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x35379) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 65536) by (regv HR (12 : reg); reflexivity)
    end.
    eapply (rz_read_dir_at RSEGS _ _ _ _ model ECALLW (Z_to_bv 64 3));
      [ constructor; reflexivity | exact HF | apply is_ecall_ECALLW | exact A17 | exact A10
      | vm_compute; split; discriminate | reflexivity | rewrite A11, A12; vm_compute; reflexivity | ].
    rewrite v_addi_pc4 by lia. change (0x32c5c + 4)%Z with 0x32c60%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (regs_set_a0 (ENV vals) sr Rc (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
    clear HR. rename HR1 into HR. change (sr_upd d_srR0 (ridx 10) (ELit (2 ^ 64 - 21))) with d_srR10 in HR.
    (* [comment removed for export] *)
    run_blk_keep scr0 70%nat.
    assert (HA2 : V10Open.above_sp0 sp0 mem0 M1).
    { intros x Hx. rewrite EQM. rewrite (mem_denot_above (ENV vals) M0 _ 0%nat 0x66000);
        [apply HA1; exact Hx | vm_compute; reflexivity | cbn [ev ENV V10Open.ENV]; rewrite P0; lia | cbn [ev ENV V10Open.ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    subst path.
    destruct (main_str sp0 a0s dot_path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi. pose proof (u64_range (cat_argv_ptr sp0 [a0s; dot_path] envv 1)) as Hpr.
    pose proof (lay_bsb_nw RPH sp0 a_draw [a0s; dot_path] envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (read_word_stack RPH RSEGS sp0 [a0s; dot_path] envv 1 1 a_uid a_hwcap a_draw ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
      as (t8 & Hl8 & Hr8).
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    eapply (ref_read_error_dot sp0 (blobs0 a0s dot_path) model Hvsp Hh eq_refl eq_refl
             (p1 sp0 a0s dot_path envv) (bv_unsigned tid) Rc Mc) with (t8 := t8) end end.
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV V10Open.ENV].
      rewrite P0. first [reflexivity | f_equal; lia].
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (18 : reg). cbn [edenot ev ENV V10Open.ENV]. exact P2.
    - (* [comment removed for export] *)
      intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ (-8388608 + d) m HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
      replace (bv_unsigned sp0 + (-8388608 + d))%Z with (bv_unsigned sp0 - 8388608 + d)%Z in Hst by lia. exact Hst.
    - (* [comment removed for export] *)
      unfold re_ivs. repeat (apply Forall_cons; [eapply kimg_clear; [exact HK | vm_compute; reflexivity] |]). apply Forall_nil.
    - (* [comment removed for export] *) unfold cell. krd HK 0x453d8%Z 4%nat Htc. rewrite Htc. cbn [edenot ev ENV V10Open.ENV]. rewrite P5.
      rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact Htid.
    - unfold cell. krd HK 0x453b8%Z 8%nat Hsf. rewrite Hsf. reflexivity.
    - unfold cell. krd HK 0x65738%Z 8%nat Hpg. rewrite Hpg. reflexivity.
    - cbn. apply (length_guard_bytes a_draw).
    - (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kblob_at 0x656e8) in exact i) _ HK eq_refl) as KB end.
      cbn [kentry_ok] in KB. destruct KB as (_ & _ & KB). unfold elenZ, estart in KB. cbn [a_base a_off edenot eb ENV V10Open.ENV blobs_ev blobs0 nth] in KB.
      rewrite (u_small 8), (u_small 0) in KB by lia.
      intros i Hi. change (nth 2 (blobs0 a0s dot_path) []) with (guard_bytes a_draw) in Hi |- *.
      rewrite Z.add_0_l in KB. apply KB. rewrite length_guard_bytes in Hi. exact Hi.
    - unfold p1. exact Slo.
    - unfold p1. lia.
    - unfold p1. change (length dot_path + 1)%nat with 2%nat in Sr.
      change ([Z_to_bv 8 46; Z_to_bv 8 0]) with (dot_path ++ [Z_to_bv 8 0]).
      rewrite <- Sr. apply rdn_agree. intros j Hj. cbn in Hj. apply HA2. rewrite u_small by lia. lia.
    - unfold p1. transitivity (rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 [a0s; dot_path] envv 1) + 1)) 8).
      { apply rdn_agree. intros j Hj. apply HA2. unorm. lia. }
      rewrite (main_entry_rdn_above sp0 [a0s; dot_path] envv tid regs0 mem0 ME) by (unorm; lia).
      pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; dot_path] envv a_uid a_hwcap a_draw) as Hw. unfold wmem in Hw.
      rewrite Hw by (unorm; lia). rewrite w_add_nat in Hr8. exact Hr8.
  Qed.
End DirRead.
End V10DirRead.

Module V10ReadLoop.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10FuzzIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)













Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPSL scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSL scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_add_Z : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma md_mul_Z : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. destruct (u_mul_eqm (Z_to_bv 64 a) (Z_to_bv 64 b)) as [q Hq].
  pose proof (u64_range (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b))) as Hr.
  rewrite <- (Z.mod_small _ (2 ^ 64) Hr). rewrite Hq. rewrite !u_lit64a.
  rewrite Z_mod_plus_full. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma round16_ge : forall n, (n <= round16 n)%Z.
Proof.
  intros n. unfold round16. pose proof (Z.div_mod (n + 15) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)). lia.
Qed.

Lemma length_file_read : forall data len want,
  (0 <= len < 2 ^ 64)%Z -> (0 <= want < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 len) (Z_to_bv 64 want) = firstn (Z.to_nat want) (skipn (Z.to_nat len) data)
  /\ Z.of_nat (length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)))
     = Z.min want (Z.max 0 (Z.of_nat (length data) - len)).
Proof.
  intros data len want Hl Hw. rewrite file_read_unguarded. unfold word_to_nat. rewrite !u_small by lia.
  split; [reflexivity|]. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma firstn_app_skipn : forall {A} (k w : nat) (l : list A),
  firstn k l ++ firstn w (skipn k l) = firstn (k + w) l.
Proof.
  intros A k. induction k as [|k IH]; intros w l; [reflexivity|].
  destruct l as [|x l]; [cbn; rewrite firstn_nil; reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_extend : forall M (a : Z) (pre bs : list byte),
  (0 <= a)%Z -> (a + Z.of_nat (length pre) + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  bytes_at M a pre ->
  bytes_at (wbytes M (Z_to_bv 64 (a + Z.of_nat (length pre))) bs) a (pre ++ bs).
Proof.
  intros M a pre bs Ha Hnw Hpre i Hi. rewrite length_app, Nat2Z.inj_add in Hi.
  destruct (Z_lt_ge_dec i (Z.of_nat (length pre))) as [Hlt|Hge].
  - rewrite wbytes_outside; [| rewrite u_small by lia; lia | rewrite !u_small by lia; left; lia].
    rewrite (Hpre i ltac:(lia)). rewrite app_nth1 by lia. reflexivity.
  - rewrite wbytes_inside; [| rewrite u_small by lia; lia | rewrite !u_small by lia; lia].
    rewrite !u_small by lia. rewrite app_nth2 by lia. do 2 f_equal. lia.
Qed.

Lemma vals_ev_map : forall E rvl i, (i < length rvl)%nat ->
  vals_ev (map (edenot E) rvl) i = edenot E (nth i rvl (ELit 0)).
Proof.
  intros E rvl i Hi. unfold vals_ev. change (Z_to_bv 64 0) with (edenot E (ELit 0)). apply map_nth.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_same : forall E sr R (rd : reg) e,
  regs_ok E sr R -> rd <> 0%bv -> getr R rd = edenot E e -> regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd e HR Hrd Hv r.
  pose proof (regs_ok_set E sr R rd (getr R rd) e HR Hrd (eq_sym Hv) r) as H.
  rewrite <- H. destruct (Z.eq_dec (bv_unsigned r) (bv_unsigned rd)) as [Hr|Hr].
  - assert (r = rd) by (apply bv_eq; exact Hr). subst r. rewrite getr_same by exact Hrd. reflexivity.
  - rewrite getr_other; [reflexivity|]. intros Hc. apply Hr. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)

Section ReadLoop.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  (* [comment removed for export] *)
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let L : Z := Z.of_nat (length data).

  (* [comment removed for export] *)
  Definition fdsk (off : Z) : list (word * FdEntry) := (Z_to_bv 64 3, FdFile path (Z_to_bv 64 off)) :: V10Open.fds0.
  Definition modelk (off : Z) (vm : VmMaps) : Model := mkModelC (fdsk off) vm stdin0 fs0 None (Some tid) None.
  Definition model2 (vm : VmMaps) : Model := mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None.

  Lemma modelk_pure : forall off vm, md_pure (modelk off vm). Proof. intros; constructor; reflexivity. Qed.
  Lemma model2_pure : forall vm, md_pure (model2 vm). Proof. intros; constructor; reflexivity. Qed.
  Lemma fdsk_insert : forall off e, fd_insert (fdsk off) (Z_to_bv 64 3) e = (Z_to_bv 64 3, e) :: V10Open.fds0.
  Proof. intros; reflexivity. Qed.
  Lemma fdsk_remove : forall off, fd_remove (fdsk off) (Z_to_bv 64 3) = V10Open.fds0.
  Proof. intros; reflexivity. Qed.
  Lemma fdsk_lookup3 : forall off, fd_lookup (fdsk off) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 off)).
  Proof. intros; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition slots (vals : list word) (buf : word) (len cap : Z) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 sp0 a0s path envv /\ vals_ev vals 2 = p1 sp0 a0s path envv
    /\ vals_ev vals 5 = tid /\ vals_ev vals 6 = buf /\ vals_ev vals 7 = Z_to_bv 64 len /\ vals_ev vals 8 = Z_to_bv 64 cap.

  (* [comment removed for export] *)
  Definition vm_ok (vm : VmMaps) (j : nat) (cap : Z) : Prop :=
    vm_limit vm = lim /\ alloc_top vm = (bv_unsigned sp0 - 8388608)%Z /\ vm_init_sp vm = sp0
    /\ vm_reserved vm = segments_reserved RSEGS.
  Definition al_ok (A : AS) (M : word -> option byte) (vm : VmMaps) (buf : word) (cap : Z) (j : nat) : Prop :=
    ainv A M vm /\ live A buf = Some cap /\ (forall q, q <> buf -> live A q = None)
    /\ aroom A vm (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap).
  Definition side (A : AS) (vm : VmMaps) (M : word -> option byte) (buf : word) (cap : Z) (j : nat) : Prop :=
    al_ok A M vm buf cap j /\ vm_ok vm j cap /\ env_ok sp0 mem0 M /\ (cap = (65536 * 2 ^ Z.of_nat j)%Z /\ (Z.of_nat j <= 10)%Z).

  (* [comment removed for export] *)
  Definition at_loop (K : TSet) (j : nat) (buf : word) (cap len : Z) : Prop :=
    forall A vm vals R M,
      length vals = 41%nat -> slots vals buf len cap ->
      regs_ok (ENV vals) sr_L R -> know_ok RSEGS (ENV vals) M kn_ML ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) (firstn (Z.to_nat len) data) ->
      (0 <= len < cap)%Z -> (len <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x152d8) M (seg_rom RSEGS)) (modelk len vm)) K.

  Definition at_header (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 41%nat -> slots vals buf L cap ->
      regs_ok (ENV vals) sr_H R -> know_ok RSEGS (ENV vals) M kn_ML ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15308) M (seg_rom RSEGS)) (model2 vm)) K.

  Definition at_full (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 41%nat -> slots vals buf cap cap ->
      regs_ok (ENV vals) sr_F R -> know_ok RSEGS (ENV vals) M kn_ML ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) (firstn (Z.to_nat cap) data) -> (cap <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x152a0) M (seg_rom RSEGS)) (modelk cap vm)) K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition in_win (x : word) : Prop := (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z.

  (* [comment removed for export] *)
  Lemma buf_facts : forall A M vm buf cap j, side A vm M buf cap j ->
    (65536 <= cap)%Z /\ (0x66000 <= bv_unsigned buf)%Z /\ (bv_unsigned buf + cap <= bv_unsigned sp0 - 8388608)%Z
    /\ (bv_unsigned buf mod 16 = 0)%Z
    /\ (forall x : word, (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M x <> None /\ owned A x).
  Proof.
    intros A M vm buf cap j ((HI & Hl & _) & (_ & Htop & _) & _ & Hcap & _).
    destruct (ai_live_hull A M vm buf cap HI Hl) as (Hc0 & Hal & Hend & Hbytes).
    pose proof (round16_ge cap) as Hr.
    assert (Hc1 : (1 <= 2 ^ Z.of_nat j)%Z).
    { change 1%Z with (2 ^ 0)%Z. apply Z.pow_le_mono_r; lia. }
    split; [lia|]. split.
    { apply (live_big_lo sp0 Hvsp AL_grant A M vm buf cap HI Hl). lia. }
    split; [lia|]. split; [exact Hal|].
    intros x Hx. destruct (Hbytes (bv_unsigned x - bv_unsigned buf)%Z ltac:(lia)) as (Ho & Hs & _).
    unfold at_ in Ho, Hs. replace (bv_unsigned buf + (bv_unsigned x - bv_unsigned buf))%Z with (bv_unsigned x) in Ho, Hs by lia.
    rewrite Z_to_bv_bv_unsigned in Ho, Hs. split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition in_data (x : word) : Prop :=
    (0x34000 <= bv_unsigned x < 0x453b0)%Z \/ (0x65b28 <= bv_unsigned x < 0x66000)%Z
    \/ (0x654c0 <= bv_unsigned x < 0x656e0)%Z.

  Lemma side_frame : forall A vm M M' buf cap j,
    side A vm M buf cap j ->
    (forall x : word, M' x <> M x ->
       in_win x \/ in_data x \/ (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z) ->
    mem_grows M M' ->
    side A vm M' buf cap j.
  Proof.
    intros A vm M M' buf cap j HS Hchg Hgr. pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & _ & Hbb).
    destruct HS as ((HI & Hl & Hlq & Hfr) & HV & (HEa & HEl & HEr) & Hcap').
    pose proof (proj1 (proj2 HV)) as Htop. pose proof SPlo.
    assert (EQ : forall x : word, ~ in_win x -> ~ in_data x ->
                 ~ (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M' x = M x).
    { intros x H1 H2 H3. destruct (M' x) as [b'|] eqn:E1; destruct (M x) as [b|] eqn:E2.
      - destruct (Z.eq_dec (bv_unsigned b') (bv_unsigned b)) as [Hb|Hb]; [f_equal; apply bv_eq; exact Hb|].
        exfalso. destruct (Hchg x ltac:(rewrite E1, E2; intros HH; injection HH as HH; apply Hb; rewrite HH; reflexivity)) as [?|[?|?]]; tauto.
      - exfalso. destruct (Hchg x ltac:(rewrite E1, E2; discriminate)) as [?|[?|?]]; tauto.
      - exfalso. destruct (Hchg x ltac:(rewrite E1, E2; discriminate)) as [?|[?|?]]; tauto.
      - reflexivity. }
    split; [|split; [exact HV | split; [|exact Hcap']]].
    - split; [|split; [exact Hl | split; [exact Hlq | exact Hfr]]].
      apply (ai_frame A M M' vm HI).
      + intros a Ho Hnl. apply EQ.
        * intros Hw. unfold in_win in Hw. destruct (ownedA_range sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
        * intros Hd. unfold in_data in Hd. destruct (ownedA_range sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
        * intros Hk. exact (Hnl buf cap Hl Hk).
      + intros a Ho HM. apply Hgr. exact HM.
      + intros a [Hg Hlt] HM'. pose proof (AL_grant a Hg) as Hg'. rewrite Htop in Hlt.
        destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned buf)) as [H1|H1].
        * rewrite <- (EQ a); [exact HM' | unfold in_win; lia | unfold in_data; lia | lia].
        * destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned buf + cap)) as [H2|H2].
          -- apply (proj1 (Hbb a ltac:(lia))).
          -- rewrite <- (EQ a); [exact HM' | unfold in_win; lia | unfold in_data; lia | lia].
    - split; [|split].
      + intros a Ha. rewrite EQ; [apply HEa; exact Ha | unfold in_win; lia | unfold in_data; lia | lia].
      + intros a H1 H2. rewrite EQ; [apply HEl; assumption | unfold in_win; lia | unfold in_data; lia | lia].
      + intros a Ha. rewrite EQ; [apply HEr; exact Ha | unfold in_win; lia | unfold in_data; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma side_block : forall A vm M buf cap j E log,
    side A vm M buf cap j -> log_win_b 0 log = true -> ev E 0 = sp0 ->
    side A vm (mem_denot E M log) buf cap j
    /\ forall x : word, ~ in_win x -> mem_denot E M log x = M x.
  Proof.
    intros A vm M buf cap j E log HS Hlog HE0. pose proof SPlo.
    assert (OUT : forall x : word, ~ in_win x -> mem_denot E M log x = M x).
    { intros x Hx. apply (mem_denot_out_win E M log 0); [exact Hlog | rewrite HE0; lia | rewrite HE0; unfold WIN; exact Hx]. }
    split; [|exact OUT].
    apply (side_frame A vm M _ buf cap j HS); [| apply mem_denot_grows].
    intros x Hne. destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 8388608)) as [H1|H1];
      [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0)) as [H2|H2]; [left; unfold in_win; lia|]];
      exfalso; apply Hne; apply OUT; unfold in_win; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma side_block_wd : forall A vm M buf cap j E log,
    side A vm M buf cap j -> log_wd_b 0 0x34000 0x453b0 log = true -> ev E 0 = sp0 ->
    side A vm (mem_denot E M log) buf cap j
    /\ forall x : word, ~ in_win x -> ~ (0x34000 <= bv_unsigned x < 0x453b0)%Z -> mem_denot E M log x = M x.
  Proof.
    intros A vm M buf cap j E log HS Hlog HE0. pose proof SPlo. pose proof SPhi.
    assert (OUT : forall x : word, ~ in_win x -> ~ (0x34000 <= bv_unsigned x < 0x453b0)%Z -> mem_denot E M log x = M x).
    { intros x Hx1 Hx2. apply (mem_denot_out_wd E M log 0 0x34000 0x453b0); [exact Hlog | rewrite HE0; lia | lia | unfold WIN; lia | rewrite HE0; unfold WIN; exact Hx1 | exact Hx2]. }
    split; [|exact OUT].
    apply (side_frame A vm M _ buf cap j HS); [| apply mem_denot_grows].
    intros x Hne. destruct (Z_lt_ge_dec (bv_unsigned x) 0x34000) as [H1|H1];
      [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x453b0) as [H2|H2]; [right; left; unfold in_data; lia|]];
      (destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 8388608)) as [H3|H3];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0)) as [H4|H4]; [left; unfold in_win; lia|]]);
      exfalso; apply Hne; apply OUT; unfold in_win; lia.
  Qed.

  (* [comment removed for export] *)
  Definition DATA_RS : list (Z * Z) := [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z.
  Lemma side_block_wdl : forall A vm M buf cap j E log,
    side A vm M buf cap j -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    side A vm (mem_denot E M log) buf cap j
    /\ forall x : word, ~ in_win x -> ~ in_data x -> mem_denot E M log x = M x.
  Proof.
    intros A vm M buf cap j E log HS Hlog HE0. pose proof SPlo. pose proof SPhi.
    assert (OUT : forall x : word, ~ in_win x -> ~ in_data x -> mem_denot E M log x = M x).
    { intros x Hx1 Hx2. apply (mem_denot_out_wdl E M log 0 DATA_RS); [exact Hlog | rewrite HE0; lia | | rewrite HE0; unfold WIN; exact Hx1 |].
      - unfold DATA_RS, WIN. repeat constructor; cbn; lia.
      - unfold DATA_RS. unfold in_data in Hx2. repeat constructor; cbn; lia. }
    split; [|exact OUT].
    apply (side_frame A vm M _ buf cap j HS); [| apply mem_denot_grows].
    intros x Hne.
    destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 8388608)) as [H3|H3];
      [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0)) as [H4|H4]; [left; unfold in_win; lia|]];
      (destruct (Z_lt_ge_dec (bv_unsigned x) 0x34000) as [H1|H1];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x453b0) as [H2|H2]; [right; left; unfold in_data; lia|]]);
      (destruct (Z_lt_ge_dec (bv_unsigned x) 0x65b28) as [H5|H5];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x66000) as [H6|H6]; [right; left; unfold in_data; lia|]]);
      (destruct (Z_lt_ge_dec (bv_unsigned x) 0x654c0) as [H7|H7];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x656e0) as [H8|H8]; [right; left; unfold in_data; lia|]]);
      exfalso; apply Hne; apply OUT; unfold in_win, in_data; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma alu_add_wZ : forall (w : word) z, alu64 ALU_ADD w (Z_to_bv 64 z) = Z_to_bv 64 (bv_unsigned w + z).
  Proof. intros w z. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. apply alu_add_Z. Qed.

  Lemma stage_store_ok : forall vals M n, know_ok RSEGS (ENV vals) M l_knA -> (Z.of_nat n <= 65536)%Z ->
    store_ok RSEGS M (Z_to_bv 64 0x35379) n = true.
  Proof.
    intros vals M n HK Hn.
    apply (kwr_store_ok_lit RSEGS (ENV vals) M l_knA ltac:(let i := kidx l_knA (is_kwr_cov (ELit 0) 0x34000 204800) in exact i)
             0x34000 204800 0x35379 n HK eq_refl); lia.
  Qed.

  Lemma slots_app : forall vals extra buf len cap, (9 <= length vals)%nat ->
    slots vals buf len cap -> slots (vals ++ extra) buf len cap.
  Proof.
    intros vals extra buf len cap HL (P0 & P1 & P2 & P5 & P6 & P7 & P8). unfold slots.
    rewrite !vals_ev_app_l by lia. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma kwr_buf : forall A vm M buf cap j E (e : expr), side A vm M buf cap j -> edenot E e = buf ->
    kentry_ok RSEGS E M (KWr (SA e 0) 65536).
  Proof.
    intros A vm M buf cap j E e HS H6. pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & _ & Hbb). pose proof SPhi.
    cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite H6. split; [lia|].
    intros d m Hd Hm. apply store_ok_of_all; [rewrite u_small by lia; lia|].
    intros x Hx. rewrite u_small in Hx by lia. unfold wview.
    destruct (M x) eqn:EM; [discriminate|]. exfalso. exact (proj1 (Hbb x ltac:(lia)) EM).
  Qed.

  Lemma iter_from_ecall : forall K j buf cap len A vm vals R M (want : Z),
    ((L < cap)%Z -> at_header K j buf cap) -> ((cap <= L)%Z -> at_full K j buf cap) ->
    (forall len', (len < len')%Z -> at_loop K j buf cap len') ->
    length vals = 42%nat -> slots vals buf len cap -> vals_ev vals 41 = Z_to_bv 64 want ->
    want = Z.min (cap - len) 65536 ->
    regs_ok (ENV vals) (sr_upd l_srAn (ridx 12) (EVar 41)) R -> know_ok RSEGS (ENV vals) M l_knA ->
    side A vm M buf cap j -> bytes_at M (bv_unsigned buf) (firstn (Z.to_nat len) data) ->
    (0 <= len < cap)%Z -> (len <= L)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32c5c) M (seg_rom RSEGS)) (modelk len vm)) K.
  Proof.
    intros K j buf cap len A vm vals R M want HDR FULL IH HL SL P41 Hwant HR HK HS HB Hlen HlenL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & Hal & Hbb).
    assert (HLd : (L = Z.of_nat (length data))%Z) by reflexivity.
    assert (Hfl : Z.of_nat (length (firstn (Z.to_nat len) data)) = len) by (rewrite length_firstn; lia).
    assert (Hw : (1 <= want <= 65536)%Z) by lia.
    destruct l_itinA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRA & VLR & VLK).
    (* [comment removed for export] *)
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x32c5c) = Some ECALLW) by (vm_compute; reflexivity).
    assert (A17 : bv_unsigned (getr R 17) = 63%Z) by (regv HR (17 : reg); reflexivity).
    assert (A10 : getr R 10 = Z_to_bv 64 3) by (regv HR (10 : reg); reflexivity).
    assert (A11 : getr R 11 = Z_to_bv 64 0x35379) by (regv HR (11 : reg); reflexivity).
    assert (A12 : getr R 12 = Z_to_bv 64 want) by (regv HR (12 : reg); cbn [edenot ev ENV V10Open.ENV]; exact P41).
    destruct (read_bytes_map_of_store_ok RSEGS M (Z_to_bv 64 0x35379) (Z.to_nat want)
                (stage_store_ok vals M (Z.to_nat want) HK ltac:(lia)) ltac:(lia)) as [wv Hwv].
    rewrite Z2Nat.id in Hwv by lia.
    eapply (rz_read_file_at RSEGS R _ M (modelk len vm) ECALLW (Z_to_bv 64 3) (Z_to_bv 64 0x35379) (Z_to_bv 64 want)
              path (Z_to_bv 64 len) data wv K (modelk_pure len vm) HF is_ecall_ECALLW A17 A10
              ltac:(rewrite u_small by lia; lia) A11 A12 (fdsk_lookup3 len) Hfile Hwv).
    { rewrite u_small by lia. unfold rw_bytes_max. lia. }
    { unfold access_okb. rewrite !u_small by lia. unfold TASK_SIZE. apply andb_true_intro; split; apply Z.leb_le; lia. }
    rewrite v_addi_pc4 by lia. change (0x32c5c + 4)%Z with 0x32c60%Z.
    destruct (length_file_read data len want ltac:(lia) ltac:(lia)) as [Hbs Hn].
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) in *.
    set (n := Z.of_nat (length bs)) in *.
    assert (HnE : n = Z.min want (L - len)) by lia. clear Hn.
    unfold len_word. fold n. rewrite bv_add_Z.
    unfold modelk. rewrite with_fds_C, m_fds_C, fdsk_insert. fold (fdsk (len + n)).
    change (mkModelC (fdsk (len + n)) vm stdin0 fs0 None (Some tid) None) with (modelk (len + n) vm).
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    - (* [comment removed for export] *)
      assert (HlenE : len = L) by lia.
      assert (Hbs0 : bs = []) by (destruct bs; [reflexivity | exfalso; subst n; cbn [length] in Hn0; lia]).
      rewrite Hbs0. cbn [wbytes]. rewrite Hn0, Z.add_0_r.
      pose proof (regs_set_a0 (ENV vals) _ R (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR1. clear HR. rename HR1 into HR.
      change (sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) (ELit 0)) with (l_srR (ELit 0)) in HR.
      assert (HK1 : know_ok RSEGS (ENV vals) M l_knR).
      { rewrite <- FRA. apply (know_ok_frame RSEGS (ENV vals) M M l_knA (ELit 0) 0x35379 65536 HK).
        - unfold flat, estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
        - intros; reflexivity.
        - apply mem_grows_refl. }
      clear HK. rename HK1 into HK.
      (* [comment removed for export] *)
      run_blk_keep scr0 42%nat.
      destruct l_itinC as (IC1 & _ & IC3). apply pair_equal_spec in IC3 as [MIS MISS].
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M buf cap j (ENV vals) log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
      rewrite <- EQM in HS1, OUT1.
      assert (HB1 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT1 by (unfold in_win; rewrite u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      clear EQM HS HB.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (B17 : bv_unsigned (getr Rc 17) = 57%Z) by (regv HR (17 : reg); reflexivity);
        assert (B10 : getr Rc 10 = Z_to_bv 64 3) by (regv HR (10 : reg); reflexivity)
      end.
      eapply (rz_close_at RSEGS _ _ _ (seg_rom RSEGS) (modelk len vm) ECALLW (Z_to_bv 64 3) _ K (modelk_pure len vm) HF
                is_ecall_ECALLW B17 B10 ltac:(rewrite u_small by lia; lia) (fdsk_lookup3 len)).
      rewrite v_addi_pc4 by lia. change (0x32c5c + 4)%Z with 0x32c60%Z.
      unfold modelk. rewrite with_fds_C, m_fds_C, fdsk_remove.
      change (mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None) with (model2 vm).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_set_a0 (ENV vals) sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR1 end.
      clear HR. rename HR1 into HR.
      (* [comment removed for export] *)
      run_blk_keep scr0 42%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (HDR ltac:(lia) A vm (map (edenot (ENV vals)) h_rvl) Rx Mx) end.
      + rewrite length_map. reflexivity.
      + unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth h_rvl rvl9 app tl edenot ev ENV V10Open.ENV].
        rewrite <- HlenE. repeat split; assumption.
      + change (ENV (map (edenot (ENV vals)) h_rvl)) with (xenv (ENV vals) h_rvl (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) h_rvl idb _ (fun k => eq_refl) srb sr_H _ HR eq_refl eq_refl)) end.
        intros i Hi. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) h_rvl)) with (xenv (ENV vals) h_rvl (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals) h_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + exact HS1.
      + rewrite HlenE in HB1. unfold L in HB1. rewrite Nat2Z.id, firstn_all in HB1. exact HB1.
      + lia.
    - (* [comment removed for export] *)
      assert (Hn1 : (1 <= n <= want)%Z) by lia. assert (HlenN : (len + n <= L)%Z) by lia. assert (HlenC : (len + n <= cap)%Z) by lia.
      set (M1 := wbytes M (Z_to_bv 64 0x35379) bs).
      assert (HS1 : side A vm M1 buf cap j).
      { apply (side_frame A vm M _ buf cap j HS); [| apply wbytes_grows].
        intros x Hne. right; left. unfold in_data. destruct (Z_lt_ge_dec (bv_unsigned x) 0x35379); [exfalso | destruct (Z_lt_ge_dec (bv_unsigned x) 0x45379); [lia | exfalso]];
          apply Hne; subst M1; apply wbytes_outside; rewrite u_small by lia; lia. }
      assert (HB1 : bytes_at M1 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. subst M1. rewrite wbytes_outside by (rewrite !u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      assert (Hsrc1 : rdn RSEGS M1 (Z_to_bv 64 0x35379) (length bs) = Some bs) by (apply rdn_wbytes_hit; rewrite u_small by lia; lia).
      assert (HK1 : know_ok RSEGS (ENV vals) M1 l_knR).
      { rewrite <- FRA. apply (know_ok_frame RSEGS (ENV vals) M M1 l_knA (ELit 0) 0x35379 65536 HK).
        - unfold flat, estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
        - intros x Hx. unfold estart in Hx. cbn [a_base a_off edenot] in Hx. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hx.
          subst M1. apply wbytes_outside; rewrite u_small by lia; lia.
        - apply wbytes_grows. }
      clear HK HS HB. clearbody M1.
      (* [comment removed for export] *)
      set (vals2 := vals ++ [Z_to_bv 64 n]).
      assert (HL2 : length vals2 = 43%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (SL2 : slots vals2 buf len cap) by (apply slots_app; [rewrite HL; lia | exact SL0]).
      assert (P42 : vals_ev vals2 42 = Z_to_bv 64 n).
      { subst vals2. replace 42%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      pose proof (env_app_regs vals [Z_to_bv 64 n] (blobs_ev (blobs0 a0s path)) _ R ltac:(rewrite HL; exact VLR) HR) as HR2.
      pose proof (regs_set_a0 (ENV vals2) _ R (Z_to_bv 64 n) (EVar 42) HR2 P42) as HR3. clear HR HR2.
      change (sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) (EVar 42)) with (l_srR (EVar 42)) in HR3. rename HR3 into HR.
      pose proof (env_app_know RSEGS vals [Z_to_bv 64 n] (blobs_ev (blobs0 a0s path)) M1 l_knR ltac:(rewrite HL; exact VLK) HK1) as HK2. clear HK1.
      assert (HK : know_ok RSEGS (ENV vals2) M1 l_knRB).
      { apply Forall_cons; [| exact HK2]. cbn [kentry_ok edenot ev ENV V10Open.ENV]. fold vals2. rewrite P42, u_small by lia. lia. }
      clear HK2. destruct SL2 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      (* [comment removed for export] *)
      run_blk_keep (SCR [false; true] [] []) 43%nat.
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M1 buf cap j (ENV vals2) log HS1 ltac:(vm_compute; reflexivity) Q0) as [HS2 OUT2] end.
      rewrite <- EQM in HS2, OUT2.
      assert (HB2 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT2 by (unfold in_win; rewrite u_small by lia; lia). apply HB1. rewrite Hfl. exact Hi. }
      assert (Hsrc2 : rdn RSEGS M0 (Z_to_bv 64 0x35379) (length bs) = Some bs).
      { rewrite <- Hsrc1. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply OUT2. unfold in_win. rewrite u_small by lia. lia. }
      clear EQM HS1 HB1 Hsrc1.
      pose proof (buf_facts A M0 vm buf cap j HS2) as (_ & _ & _ & _ & Hbb2).
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned buf + len)).
      assert (Hdst : store_ok RSEGS M0 dst (length bs) = true).
      { apply store_ok_of_all; [subst dst; rewrite u_small by lia; lia|]. intros x Hx. subst dst. rewrite u_small in Hx by lia.
        unfold wview. destruct (M0 x) eqn:EM; [discriminate|]. exfalso. exact (proj1 (Hbb2 x ltac:(lia)) EM). }
      assert (MC : mcH M0 dst (Z_to_bv 64 0x35379) n bs).
      { constructor; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hsrc2.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = Z_to_bv 64 0x1528c) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; fold vals2; rewrite Q6, Q7; subst dst; apply alu_add_wZ);
        assert (B11 : getr Rc 11 = Z_to_bv 64 0x35379) by (regv HR (11 : reg); reflexivity);
        assert (B12 : getr Rc 12 = Z_to_bv 64 n) by (regv HR (12 : reg); cbn [edenot ev ENV V10Open.ENV]; exact P42);
        destruct (ref_memcpy M0 dst (Z_to_bv 64 0x35379) n bs (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x1528c)
                    ltac:(apply ret_ok_even; reflexivity) A1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear A1 B10 B11 B12
      end.
      replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
      set (M2 := wbytes M0 dst bs).
      assert (HS3 : side A vm M2 buf cap j).
      { apply (side_frame A vm M0 _ buf cap j HS2); [| apply wbytes_grows].
        intros x Hne. right; right.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned buf + len)); [exfalso | destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned buf + len + n)); [lia | exfalso]];
          apply Hne; subst M2 dst; apply wbytes_outside; rewrite u_small by lia; lia. }
      assert (HB3 : bytes_at M2 (bv_unsigned buf) (firstn (Z.to_nat (len + n)) data)).
      { replace (firstn (Z.to_nat (len + n)) data) with (firstn (Z.to_nat len) data ++ bs).
        2:{ rewrite Hbs, firstn_app_skipn. rewrite <- (State.firstn_min_length _ data (Z.to_nat len + Z.to_nat want)), <- (State.firstn_min_length _ data (Z.to_nat (len + n))).
            f_equal. lia. }
        subst M2 dst. replace (bv_unsigned buf + len)%Z with (bv_unsigned buf + Z.of_nat (length (firstn (Z.to_nat len) data)))%Z by lia.
        apply bytes_at_extend; [lia | lia | exact HB2]. }
      (* [comment removed for export] *)
      destruct l_itinB as (_ & _ & VLB & _ & SRD & KND & VLD).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm callee_kept ltac:(rewrite HL2; exact VLB) HR Hkeep callee_kept_no0) as HR4 end.
      rewrite HL2 in HR4. lazymatch type of HR4 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR4 end.
      clear HR Hkeep.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_ok_call RSEGS (ENV vals2) M0 M2 [] 0 0 IHI 0x34000) as KC;
        specialize (KC ltac:(cbn [ev ENV V10Open.ENV]; fold vals2; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK4; clear KC
      end.
      specialize (HK4 ltac:(intros x Hnt; subst M2 dst; apply wbytes_outside; [rewrite u_small by lia; lia|]; rewrite u_small by lia;
                              unfold touched, IHI, WIN in Hnt; cbn [ev ENV V10Open.ENV] in Hnt; fold vals2 in Hnt; rewrite Q0 in Hnt; lia)
                      ltac:(intros x _ Hx; apply (wbytes_grows bs M0 dst); exact Hx)
                      ltac:(intros m a k H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
      lazymatch type of HK4 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK4 end. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) M2 _ ltac:(rewrite HL2; exact VLD) HK4) as HK. clear HK4.
      rename HR4 into HR.
      set (vals3 := vals2 ++ junk_vals Rm) in *.
      assert (HL3 : length vals3 = 75%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (SL3 : slots vals3 buf len cap) by (subst vals3; apply slots_app; [rewrite HL2; lia | repeat split; assumption]).
      assert (R42 : vals_ev vals3 42 = Z_to_bv 64 n) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact P42).
      clearbody vals3. clear Q0 Q1 Q2 Q5 Q6 Q7 Q8. destruct SL3 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clearbody M2. clear Hdst MC Hsrc2 HB2 HS2 Hbb2.
      destruct l_itinD as (_ & _ & _ & IDn & IDt & S19).
      apply pair_equal_spec in IDn as [MISn MISSn]. apply pair_equal_spec in IDt as [MISt MISSt].
      destruct (Z.eq_dec (len + n) cap) as [Hfull|Hnf].
      + (* [comment removed for export] *)
        run_blk_keep (SCR [true] [] []) 75%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite Q7, Q8, R42, alu_add_Z.
          unfold bv_eqb. rewrite !u_small by lia. apply Z.eqb_eq. exact Hfull. }
        cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end. rewrite Hfull.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (FULL ltac:(lia) A vm (map (edenot (ENV vals3)) f_rvl) Rx Mx) end.
        * rewrite length_map. reflexivity.
        * unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth f_rvl rvl9 app tl edenot ev ENV V10Open.ENV].
          repeat split; assumption.
        * change (ENV (map (edenot (ENV vals3)) f_rvl)) with (xenv (ENV vals3) f_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) f_rvl idb _ (fun k => eq_refl) srb sr_F _ HR eq_refl eq_refl)) end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[Hi|[]]]; [exfalso; lia|]. subst i.
          cbn [nth sr_F emap rv f_rvl rvl9 app tl idb edenot ev ENV V10Open.ENV]. rewrite Q7, Q8, R42, alu_add_Z. f_equal. lia.
        * change (ENV (map (edenot (ENV vals3)) f_rvl)) with (xenv (ENV vals3) f_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) f_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply (kwr_buf A vm M2 buf cap j _ (EVar 6) HS3). cbn [edenot ev ENV V10Open.ENV]. exact Q6.
        * exact HS3.
        * rewrite <- Hfull. exact HB3.
        * lia.
        (* [comment removed for export] *)
      + (* [comment removed for export] *)
        run_blk_keep (SCR [false] [] []) 75%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite Q7, Q8, R42, alu_add_Z.
          unfold bv_eqb. rewrite !u_small by lia. apply Z.eqb_neq. exact Hnf. }
        cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (IH (len + n)%Z ltac:(lia) A vm (map (edenot (ENV vals3)) d_rvl) Rx Mx) end.
        * rewrite length_map. reflexivity.
        * unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth d_rvl rvl9 app tl edenot ev ENV V10Open.ENV].
          rewrite Q7, R42, alu_add_Z. repeat split; assumption || reflexivity.
        * change (ENV (map (edenot (ENV vals3)) d_rvl)) with (xenv (ENV vals3) d_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) d_rvl idb _ (fun k => eq_refl) srb sr_L _ HR eq_refl eq_refl)) end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * change (ENV (map (edenot (ENV vals3)) d_rvl)) with (xenv (ENV vals3) d_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) d_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply (kwr_buf A vm M2 buf cap j _ (EVar 6) HS3). cbn [edenot ev ENV V10Open.ENV]. exact Q6.
        * exact HS3.
        * exact HB3.
        * lia.
        * lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma want_x_val : forall vals len cap,
    vals_ev vals 7 = Z_to_bv 64 len -> vals_ev vals 8 = Z_to_bv 64 cap ->
    edenot (ENV vals) want_x = Z_to_bv 64 (cap - len).
  Proof.
    intros vals len cap H7 H8. cbn [edenot want_x ev ENV V10Open.ENV]. rewrite H7, H8, md_mul_Z, alu_add_Z. f_equal. lia.
  Qed.

  Theorem read_loop : forall K j buf cap,
    ((L < cap)%Z -> at_header K j buf cap) -> ((cap <= L)%Z -> at_full K j buf cap) ->
    forall len, at_loop K j buf cap len.
  Proof.
    intros K j buf cap HDR FULL len0.
    enough (G : forall fuel len, (cap - len <= Z.of_nat fuel)%Z -> at_loop K j buf cap len) by (apply (G (Z.to_nat (cap - len0))); lia).
    induction fuel as [|fuel IHf]; intros len Hle A vm vals R M HL SL HR HK HS HB Hlen HlenL; [exfalso; lia|].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts A M vm buf cap j HS) as (Hcap & Hb0 & Hb1 & Hal & Hbb).
    assert (Hfl : Z.of_nat (length (firstn (Z.to_nat len) data)) = len) by (rewrite length_firstn; unfold L in HlenL; lia).
    assert (IH : forall len', (len < len')%Z -> at_loop K j buf cap len') by (intros len' Hlt; apply IHf; lia).
    destruct l_itinA as (_ & _ & _ & _ & WX & SRU & VLn & VLt & VLK & _).
    pose proof (want_x_val vals len cap P7 P8) as HWX. unfold want_x in HWX.
    unfold modelk.
    destruct (Z_lt_ge_dec (cap - len) 65536) as [Hlt|Hge].
    - (* [comment removed for export] *)
      run_blk_keep (SCR [true] [] []) 41%nat.
      { cbn [sc_denot branch_taken]. rewrite HWX. cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. apply Z.ltb_lt. lia. }
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M buf cap j (ENV vals) log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
      rewrite <- EQM in HS1, OUT1.
      assert (HB1 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT1 by (unfold in_win; rewrite u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      clear EQM HS HB.
      set (vals1 := vals ++ [Z_to_bv 64 (cap - len)]).
      assert (P41 : vals_ev vals1 41 = Z_to_bv 64 (cap - len)).
      { subst vals1. replace 41%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [Z_to_bv 64 (cap - len)] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; exact VLt) HR) as HR1;
        pose proof (regs_ok_same (ENV vals1) sr Rc 12 (EVar 41) HR1 ltac:(intros H12; apply (f_equal bv_unsigned) in H12; discriminate H12)
                      ltac:(let e := eval vm_compute in (sr_get sr (12 : reg)) in
                            rewrite (HR (12 : reg)); change (sr_get sr (12 : reg)) with e;
                            rewrite HWX; cbn [edenot ev ENV V10Open.ENV]; symmetry; exact P41)) as HR2
      end.
      clear HR HR1.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      apply (iter_from_ecall K j buf cap len A vm vals1 _ M0 (cap - len) HDR FULL IH); try assumption.
      + subst vals1. rewrite length_app, HL. reflexivity.
      + subst vals1. apply slots_app; [rewrite HL; lia | exact SL0].
      + lia.
      + apply (env_app_know RSEGS vals _ (blobs_ev (blobs0 a0s path)) M0 _ ltac:(rewrite HL; exact VLK)). exact HK.
    - (* [comment removed for export] *)
      run_blk_keep (SCR [false] [] []) 41%nat.
      { cbn [sc_denot branch_taken]. rewrite HWX. cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. apply Z.ltb_ge. lia. }
      lazymatch type of EQM with _ = mem_denot _ _ ?log =>
        destruct (side_block A vm M buf cap j (ENV vals) log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
      rewrite <- EQM in HS1, OUT1.
      assert (HB1 : bytes_at M0 (bv_unsigned buf) (firstn (Z.to_nat len) data)).
      { intros i Hi. rewrite Hfl in Hi. rewrite OUT1 by (unfold in_win; rewrite u_small by lia; lia). apply HB. rewrite Hfl. exact Hi. }
      clear EQM HS HB.
      set (vals1 := vals ++ [Z_to_bv 64 65536]).
      assert (P41 : vals_ev vals1 41 = Z_to_bv 64 65536).
      { subst vals1. replace 41%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [Z_to_bv 64 65536] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; exact VLn) HR) as HR1;
        pose proof (regs_ok_same (ENV vals1) sr Rc 12 (EVar 41) HR1 ltac:(intros H12; apply (f_equal bv_unsigned) in H12; discriminate H12)
                      ltac:(let e := eval vm_compute in (sr_get sr (12 : reg)) in
                            rewrite (HR (12 : reg)); change (sr_get sr (12 : reg)) with e;
                            cbn [edenot ev ENV V10Open.ENV]; symmetry; exact P41)) as HR2
      end.
      clear HR HR1.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      apply (iter_from_ecall K j buf cap len A vm vals1 _ M0 65536 HDR FULL IH); try assumption.
      + subst vals1. rewrite length_app, HL. reflexivity.
      + subst vals1. apply slots_app; [rewrite HL; lia | exact SL0].
      + lia.
      + apply (env_app_know RSEGS vals _ (blobs_ev (blobs0 a0s path)) M0 _ ltac:(rewrite HL; exact VLK)). exact HK.
  Qed.

  (* [comment removed for export] *)
  Theorem read_k0_entry : forall K,
    (forall buf, at_loop K 0 buf 65536 0) ->
    V10Malloc65536.at_buf sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (FdFile path (Z_to_bv 64 0)) K.
  Proof.
    intros K HLOOP A1 vm1 vals R M HL P0 P1 P2 P5 HI Hlive Hlq Hroom Hvl Htop Hisp Hres HR HK HE.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    unfold V10Open.model1g. rewrite with_vmmaps_C.
    change (mkModelC (V10Open.fds1g (FdFile path (Z_to_bv 64 0))) vm1 stdin0 fs0 None (Some tid) None) with (modelk 0 vm1).
    change V10Malloc65536.ok_sr with ok_sr in HR. change V10Malloc65536.ok_kn with ok_kn in HK.
    unfold modelk.
    run_blk_keep (SCR [false] [] []) 70%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct e_itin as [_ IE]. apply pair_equal_spec in IE as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
      apply (HLOOP (vals_ev vals 48) A1 vm1 (map (edenot (ENV vals)) e_rvl) Rx Mx) end.
    - rewrite length_map. reflexivity.
    - unfold slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth e_rvl rvl9 app tl edenot ev ENV V10Open.ENV].
      repeat split; assumption || reflexivity.
    - change (ENV (map (edenot (ENV vals)) e_rvl)) with (xenv (ENV vals) e_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HR with regs_ok _ ?sr _ =>
        p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) e_rvl idb _ (fun k => eq_refl) srb sr_L _ HR eq_refl eq_refl)) end.
      intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
      destruct Hi as [Hi|[]]. exfalso; lia.
    - change (ENV (map (edenot (ENV vals)) e_rvl)) with (xenv (ENV vals) e_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (know_ok_xfer_entails RSEGS (ENV vals) e_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
      lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - split; [|split; [|split; [exact HE | split; [reflexivity | lia]]]].
      + split; [exact HI|]. split; [exact Hlive|]. split; [exact Hlq|]. exact Hroom.
      + split; [exact Hvl|]. split; [exact Htop|]. split; [exact Hisp|]. exact Hres.
    - intros i Hi. change (firstn (Z.to_nat 0) data) with (@nil byte) in Hi. cbn [length Z.of_nat] in Hi. lia.
    - lia.
    - unfold L. lia.
  Qed.
End ReadLoop.
End V10ReadLoop.


Module V10TRun_defs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import V10MainEntry.
Import V10Kit.
Import V10OpenFail_defs.
Import V10Open_defs.
Import V10Oom_defs.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10Hdr_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import V10Kit.V10LibStdioCall.

Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPST : list Z := (0x15594 :: 0x15664 :: 0x15400 :: STOPS2)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPST scr ss [].
(* [comment removed for export] *)
Definition STOPSP : list Z := [0x2d23c; 0x15594; 0x15400; 0x2b208]%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSP scr ss [].

(* [comment removed for export] *)
Definition t_ss1 := SS 0x154dc sr_R [] kn_R 45.
Definition t_r1a := Eval vm_compute in runT (SCR [false; false] [] []) t_ss1.   (* [comment removed for export] *)
Definition t_r1b := Eval vm_compute in runT (SCR [false; true] [] []) t_ss1.    (* [comment removed for export] *)
Definition t_r1c := Eval vm_compute in runT (SCR [true; true] [] []) t_ss1.     (* [comment removed for export] *)
Definition t_r1d := Eval vm_compute in runT (SCR [true; false] [] []) t_ss1.    (* [comment removed for export] *)
Definition t_sr1a := Eval vm_compute in s_regs (fst (fst t_r1a)).
Definition t_sr1b := Eval vm_compute in s_regs (fst (fst t_r1b)).
Definition t_sr1c := Eval vm_compute in s_regs (fst (fst t_r1c)).
Definition t_sr1d := Eval vm_compute in s_regs (fst (fst t_r1d)).
Definition t_kn1 := Eval vm_compute in kn_after t_r1a kn_R.
Definition calls_x : expr := Eval vm_compute in nth 21 t_sr1a (ELit 0).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_fix (K : kentry) : list kentry :=
  match K with
  | KImg 0x10000 0x35330 => [KImg 0x10000 0x34e08; KImg 0x34e10 0x35330]
  | KImg 0x65b28 0x66000 => [KImg 0x65b28 0x65b50; KImg 0x65f50 0x66000]
  | _ => [K]
  end.

Definition keepT (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) k) _ _ => (-208 <=? k)%Z | _ => true end.
Definition kn_T0 : list kentry := Eval vm_compute in flat_map kimg_fix (List.filter keepT (List.filter (kentry_vars_lt 13) t_kn1)).

Definition sav (v6 v7 : nat) : list kentry :=
  [KWord (SA (EVar 0) (-192)) 8 (EVar v6); KWord (SA (EVar 0) (-200)) 8 (EVar v7)].
Definition is_sav (K : kentry) : bool :=
  match K with
  | KWord (SA (EVar 0) (-192)) 8 (EVar 40) => true
  | KWord (SA (EVar 0) (-200)) 8 (EVar 41) => true
  | _ => false
  end.
Definition sav_sr (e6 e7 : expr) (sr : list expr) : list expr := sr_upd (sr_upd sr 22 e6) 23 e7.
Definition kn_T : list kentry := Eval vm_compute in sav 36 37 ++ kn_T0.

(* [comment removed for export] *)
Definition JM (i : nat) : expr := EVar (14 + i).
Definition sr_TM : list expr :=
  [ELit 0; ELit 0x15540; spx (-208); ELit 0x10800; ELit 0x45480; JM 5; JM 6; JM 7;
   EVar 9; EVar 12; EVar 9; JM 11; JM 12; JM 13; JM 14; JM 15;
   JM 16; JM 17; JM 18; JM 19; ELit 0x45380; EVar 13; JM 22; JM 23;
   JM 24; JM 25; JM 26; JM 27; JM 28; JM 29; JM 30; JM 31].
Definition rvl13 (ecalls : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; ecalls] ++ (ELit 0 :: tl sr).
Definition tm_rvla : list expr := rvl13 calls_x t_sr1a.
Definition tm_rvlc : list expr := rvl13 (ELit 1) t_sr1c.
(* [comment removed for export] *)
Definition kn_acallT (kn : list kentry) : list kentry := kn_call GLOB (-208 - 1024) (-208) IHI 0x34000 kn.
(* [comment removed for export] *)
Definition tm_srM : list expr := sr_after_call_j sr_TM KEPT_AL 46.
Definition tm_knM : list kentry := Eval vm_compute in KRange (EVar 56) 0x1000 0x7fffff800000 :: kn_acallT kn_T.
Definition tm_r2 := Eval vm_compute in runT scr0 (SS 0x15540 tm_srM [] tm_knM 78).
Definition tm_sr2 := Eval vm_compute in s_regs (fst (fst tm_r2)).
Definition tm_kn2 := Eval vm_compute in kn_after tm_r2 tm_knM.
(* [comment removed for export] *)
Definition tm_sr3i := Eval vm_compute in sr_after_call_j tm_sr2 KEPT_MC 78.
Definition tm_kn3i := Eval vm_compute in kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x34000 tm_kn2.
Definition tm_r3 := Eval vm_compute in runT scr0 (SS 0x15554 tm_sr3i [] tm_kn3i 110).
Definition tm_sr3 := Eval vm_compute in s_regs (fst (fst tm_r3)).
Definition tm_kn3 := Eval vm_compute in kn_after tm_r3 tm_kn3i.
(* [comment removed for export] *)
Definition tn_sr1i := sr_upd tm_srM (ridx 10) (ELit 0).
Definition tn_kn1i : list kentry := Eval vm_compute in kn_acallT kn_T.
Definition tn_r1n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x15540 tn_sr1i [] tn_kn1i 78).  (* [comment removed for export] *)
Definition tn_r1c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x15540 tn_sr1i [] tn_kn1i 78).   (* [comment removed for export] *)
Definition tn_sr1n := Eval vm_compute in s_regs (fst (fst tn_r1n)).
Definition tn_sr1c := Eval vm_compute in s_regs (fst (fst tn_r1c)).
Definition tn_kn1 := Eval vm_compute in kn_after tn_r1n tn_kn1i.

(* [comment removed for export] *)
Definition JN (i : nat) : expr := EVar (8 + i).
Definition sr_FN : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x45480; JN 5; JN 6; JN 7;
   EVar 7; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
Definition kn_FN : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) tn_kn1.
Definition fn_rvln : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 2] ++ (ELit 0 :: tl tn_sr1n).
Definition fn_rvlc : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 0] ++ (ELit 0 :: tl tn_sr1c).
Definition fn_r1 := Eval vm_compute in runT scr0 (SS 0x15400 sr_FN [] kn_FN 40).
Definition fn_sr1 := Eval vm_compute in s_regs (fst (fst fn_r1)).
Definition fn_kn1 := Eval vm_compute in kn_after fn_r1 kn_FN.
Definition fn_sr2i := Eval vm_compute in sr_after_call_j fn_sr1 KEPT_AL 40.
Definition fn_kn2i := Eval vm_compute in kn_acall fn_kn1.
Definition fn_r2 := Eval vm_compute in runT scr0 (SS 0x15408 fn_sr2i [] fn_kn2i 72).
Definition fn_sr2 := Eval vm_compute in s_regs (fst (fst fn_r2)).
Definition fn_kn2 := Eval vm_compute in kn_after fn_r2 fn_kn2i.

(* [comment removed for export] *)
Definition keepTL (K : kentry) : bool :=
  match K with KWord (SA (EVar 6) _) _ _ => false | KWr (SA (EVar 6) _) _ => false | _ => true end.
Definition kn_TL : list kentry := Eval vm_compute in sav 40 41 ++ List.filter keepTL kn_T0.
Definition JL (i : nat) : expr := EVar (18 + i).
Definition sr_TL : list expr :=
  [ELit 0; JL 1; spx (-208); ELit 0x10800; ELit 0x45480; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; JL 10; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; EVar 17; ELit 0x45380; EVar 16; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition rvl18 (e13 e14 e15 e16 e17 : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17] ++ (ELit 0 :: tl sr).
Definition tl_rvlb : list expr := rvl18 calls_x (ELit 0x45390) (ELit 0) calls_x (nth 19 t_sr1b (ELit 0)) (sav_sr (EVar 35) (EVar 36) t_sr1b).
Definition tl_rvld : list expr := rvl18 (ELit 1) (ELit 0x45390) (ELit 0) (ELit 1) (nth 19 t_sr1d (ELit 0)) (sav_sr (EVar 35) (EVar 36) t_sr1d).
Definition tl_rvlm : list expr := rvl18 (EVar 13) (EVar 56) (EVar 56) (EVar 13) (nth 19 tm_sr3 (ELit 0)) (sav_sr (EVar 36) (EVar 37) tm_sr3).
(* [comment removed for export] *)
Definition tl_r1 := Eval vm_compute in runT scr0 (SS 0x15594 sr_TL [] kn_TL 50).
Definition tl_sr1 := Eval vm_compute in s_regs (fst (fst tl_r1)).
Definition tl_kn1 := Eval vm_compute in kn_after tl_r1 kn_TL.
(* [comment removed for export] *)
Definition LGLOB : list (Z * Z) := ((0x34e08, 0x34e10) :: GLOB)%Z.
Definition kn_fcall (kn : list kentry) : list kentry := kn_call LGLOB (-208 - 16384) (-208) IHI 0x34000 kn.
(* [comment removed for export] *)
Definition tl_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl_kn2i : list kentry := Eval vm_compute in kn_fcall tl_kn1.
Definition tl_r2 := Eval vm_compute in runT scr0 (SS 0x155a8 tl_sr2i [] tl_kn2i 82).
Definition tl_sr2 := Eval vm_compute in s_regs (fst (fst tl_r2)).
Definition tl_kn2 := Eval vm_compute in kn_after tl_r2 tl_kn2i.
(* [comment removed for export] *)
Definition p_r1 := Eval vm_compute in runP scr0 (SS 0x15664 tl_sr2 [] tl_kn2 82).
Definition p_sr1 := Eval vm_compute in s_regs (fst (fst p_r1)).
Definition p_kn1 := Eval vm_compute in kn_after p_r1 tl_kn2.
(* [comment removed for export] *)
Definition p_r2 := Eval vm_compute in runP scr0 (SS 0x2d7a4 (sr_upd p_sr1 (ridx 10) (ELit (2^64 - 25))) [] p_kn1 82).
Definition p_sr2 := Eval vm_compute in s_regs (fst (fst p_r2)).
Definition p_kn2 := Eval vm_compute in kn_after p_r2 p_kn1.
Definition p_sc : stdio_res := Eval vm_compute in sc_of 82 p_sr2 p_kn2.
(* [comment removed for export] *)
Definition p_sr3i := Eval vm_compute in sc_sr p_sc.
Definition p_kn3i := Eval vm_compute in sc_kn p_sc.
Definition p_r3l := Eval vm_compute in runP (SCR [true] [] []) (SS (sc_ret p_sc) p_sr3i [] p_kn3i 114).   (* [comment removed for export] *)
Definition p_r3e := Eval vm_compute in runP (SCR [false] [] []) (SS (sc_ret p_sc) p_sr3i [] p_kn3i 114).  (* [comment removed for export] *)
Definition p_sr3l := Eval vm_compute in s_regs (fst (fst p_r3l)).
Definition p_sr3e := Eval vm_compute in s_regs (fst (fst p_r3e)).
Definition p_kn3 := Eval vm_compute in kn_after p_r3l p_kn3i.


(* [comment removed for export] *)
Definition keepTL1 (K : kentry) : bool :=
  is_sav K ||
  kentry_vars_lt 18 K &&
  match K with
  | KWord (SA (EVar 0) k) _ _ => (-208 <=? k)%Z
  | KWord (SA (ELit 0) 416592) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | _ => true
  end.
Definition fixw (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 217688) 8 _ => KWord (SA (ELit 0) 217688) 8 (EVar 18) | _ => K end.
Definition kn_TL1 : list kentry := Eval vm_compute in KRange (EVar 18) 0x65b50 0x65f48 :: map fixw (List.filter keepTL1 p_kn3).
(* [comment removed for export] *)
Definition rvl18w (e13 e14 e15 e16 e17 ew : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17; ew] ++ tl sr.
Definition tl1_rvl0 : list expr :=      (* [comment removed for export] *)
  rvl18w (EVar 13) (EVar 14) (EVar 15) (EAluw ALU_ADD (EVar 16) (ELit (-1))) (nth 19 p_sr3l (ELit 0)) (ELit 0x65b50) (sav_sr (EVar 40) (EVar 41) p_sr3l).
(* [comment removed for export] *)
Definition tl1_r1 := Eval vm_compute in runT scr0 (SS 0x15594 sr_TL [] kn_TL1 50).
Definition tl1_sr1 := Eval vm_compute in s_regs (fst (fst tl1_r1)).
Definition tl1_kn1 := Eval vm_compute in kn_after tl1_r1 kn_TL1.
Definition tl1_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl1_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl1_kn2i : list kentry := Eval vm_compute in kn_fcall tl1_kn1.
Definition tl1_r2 := Eval vm_compute in runT scr0 (SS 0x155a8 tl1_sr2i [] tl1_kn2i 82).
Definition tl1_sr2 := Eval vm_compute in s_regs (fst (fst tl1_r2)).
Definition tl1_kn2 := Eval vm_compute in kn_after tl1_r2 tl1_kn2i.
(* [comment removed for export] *)
Definition tl1_sr3i : list expr := Eval vm_compute in sr_after_call_j tl1_sr2 KEPT_CS 82.
Definition tl1_kn3i : list kentry := Eval vm_compute in
  KWord (SA (ELit 0) 217688) 8 (EAlu ALU_ADD (EVar 18) (ELit 2)) :: KWord (SA (ELit 0) 217648) 4 (ELit 5)
  :: kn_call [(0x35230, 0x35234); (0x35258, 0x35260); (0x65b50, 0x65f50)]%Z (-208 - 1056) (-208) IHI 0x34000 tl1_kn2.
Definition tl1_r3l := Eval vm_compute in runT (SCR [true] [] []) (SS 0x155b8 tl1_sr3i [] tl1_kn3i 114).
Definition tl1_r3e := Eval vm_compute in runT (SCR [false] [] []) (SS 0x155b8 tl1_sr3i [] tl1_kn3i 114).
Definition tl1_sr3l := Eval vm_compute in s_regs (fst (fst tl1_r3l)).
Definition tl1_sr3e := Eval vm_compute in s_regs (fst (fst tl1_r3e)).
Definition tl1_kn3 := Eval vm_compute in kn_after tl1_r3l tl1_kn3i.
Definition tl1_rvl : list expr :=
  rvl18w (EVar 13) (EVar 14) (EVar 15) (EAluw ALU_ADD (EVar 16) (ELit (-1))) (nth 19 tl1_sr3l (ELit 0)) (EAlu ALU_ADD (EVar 18) (ELit 2)) (sav_sr (EVar 40) (EVar 41) tl1_sr3l).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keepFN1 (K : kentry) : bool :=
  kentry_vars_lt 19 K &&
  match K with
  | KWord (SA (EVar 0) k) _ _ => (-128 <=? k)%Z
  | KWord (SA (ELit 0) 416592) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | KRange (EVar i) _ _ => Nat.ltb i 8
  | KAlign (EVar i) _ => Nat.ltb i 8
  | KDisj _ _ (SA (EVar i) _) _ => Nat.ltb i 8
  | _ => true
  end.
Definition fixw7 (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 217688) 8 _ => KWord (SA (ELit 0) 217688) 8 (EVar 7) | _ => K end.
Definition kn_FN1 : list kentry := Eval vm_compute in KRange (EVar 7) 0x65b50 0x65f50 :: map fixw7 (List.filter keepFN1 (kn_acallT tl1_kn3)).
Definition sr_FN1 : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x45480; JN 5; JN 6; JN 7;
   ELit 0; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
(* [comment removed for export] *)
Definition e_sr1p : list expr := Eval vm_compute in sr_after_call_j p_sr3e KEPT_AL 114.
Definition e_kn1p : list kentry := Eval vm_compute in kn_acallT p_kn3.
Definition e_r2pn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x155d4 e_sr1p [] e_kn1p 146).
Definition e_r2pc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x155d4 e_sr1p [] e_kn1p 146).
Definition e_sr1t : list expr := Eval vm_compute in sr_after_call_j tl1_sr3e KEPT_AL 114.
Definition e_kn1t : list kentry := Eval vm_compute in kn_acallT tl1_kn3.
Definition e_r2tn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x155d4 e_sr1t [] e_kn1t 146).
Definition e_r2tc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x155d4 e_sr1t [] e_kn1t 146).
Definition fn1_rvl (ew : expr) (sr : list expr) : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ew] ++ (ELit 0 :: tl sr).
(* [comment removed for export] *)
Definition fn1_r1 := Eval vm_compute in runT scr0 (SS 0x15400 sr_FN1 [] kn_FN1 40).
Definition fn1_sr1 := Eval vm_compute in s_regs (fst (fst fn1_r1)).
Definition fn1_kn1 := Eval vm_compute in kn_after fn1_r1 kn_FN1.
Definition fn1_sr2i := Eval vm_compute in sr_after_call_j fn1_sr1 KEPT_AL 40.
Definition fn1_kn2i := Eval vm_compute in kn_acall fn1_kn1.
Definition fn1_r2 := Eval vm_compute in runT scr0 (SS 0x15408 fn1_sr2i [] fn1_kn2i 72).
Definition fn1_sr2 := Eval vm_compute in s_regs (fst (fst fn1_r2)).
Definition fn1_kn2 := Eval vm_compute in kn_after fn1_r2 fn1_kn2i.

Section VP1.
Lemma t_itin1 :
  (s_pc (fst (fst t_r1a)), snd (fst t_r1a), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst t_r1a))))
    = (0x2b348%Z, [SCBr false BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1c)), snd (fst t_r1c), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst t_r1c))))
    = (0x2b348%Z, [SCBr true BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1b)), snd (fst t_r1b), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst t_r1b))))
    = (0x15594%Z, [SCBr true BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1d)), snd (fst t_r1d), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst t_r1d))))
    = (0x15594%Z, [SCBr false BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (sr_mismatch tm_rvla idb t_sr1a sr_TM 0, kn_missing t_kn1 (map (kmap tm_rvla idb) kn_T)) = ([], [])
  /\ (sr_mismatch tm_rvlc idb t_sr1c sr_TM 0, kn_missing (kn_after t_r1c kn_R) (map (kmap tm_rvlc idb) kn_T)) = ([], [])
  /\ (sr_mismatch tl_rvlb idb t_sr1b sr_TL 0, kn_missing (kn_after t_r1b kn_R) (map (kmap tl_rvlb idb) kn_TL)) = ([], [])
  /\ (sr_mismatch tl_rvld idb t_sr1d sr_TL 0, kn_missing (kn_after t_r1d kn_R) (map (kmap tl_rvld idb) kn_TL)) = ([], [])
  /\ calls_x = EAlu ALU_ADD (EAlu ALU_AND (EExt false 0 1 (EVar 11)) (ELit 3)) (ELit 1)
  /\ nth 19 t_sr1b (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2) /\ nth 19 t_sr1d (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma tm_itin :
  (s_pc (fst (fst tm_r2)), snd (fst tm_r2), s_log (fst (fst tm_r2))) = (0x3233c%Z, [], [])
  /\ (nth 1 tm_sr2 (ELit 0), nth 10 tm_sr2 (ELit 0), nth 11 tm_sr2 (ELit 0), nth 12 tm_sr2 (ELit 0)) = (ELit 0x15554, EVar 56, EVar 12, EVar 9)
  /\ kn_vars_lt 46 kn_T = true /\ sr_vars_lt 78 tm_sr2 = true /\ kn_vars_lt 78 tm_kn2 = true
  /\ sr_after_call_j tm_sr2 KEPT_MC 78 = tm_sr3i /\ kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x34000 tm_kn2 = tm_kn3i /\ kn_vars_lt 78 tm_kn3i = true
  /\ (s_pc (fst (fst tm_r3)), snd (fst tm_r3), s_log (fst (fst tm_r3))) = (0x15594%Z, [], [])
  /\ (sr_mismatch tl_rvlm idb tm_sr3 sr_TL 0, kn_missing tm_kn3 (map (kmap tl_rvlm idb) kn_TL)) = ([0%nat], [])
  /\ nth 19 tm_sr3 (ELit 0) = EVar 33.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma tn_itin :
  (s_pc (fst (fst tn_r1n)), snd (fst tn_r1n), log_win_b 0 (s_log (fst (fst tn_r1n)))) = (0x15400%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst tn_r1c)), snd (fst tn_r1c), log_win_b 0 (s_log (fst (fst tn_r1c)))) = (0x15400%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (sr_mismatch fn_rvln idb tn_sr1n sr_FN 0, kn_missing tn_kn1 (map (kmap fn_rvln idb) kn_FN)) = ([0%nat], [])
  /\ (sr_mismatch fn_rvlc idb tn_sr1c sr_FN 0, kn_missing (kn_after tn_r1c tn_kn1i) (map (kmap fn_rvlc idb) kn_FN)) = ([0%nat], [])
  /\ kn_acallT kn_T = tn_kn1i.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fn_itin :
  (s_pc (fst (fst fn_r1)), snd (fst fn_r1), s_log (fst (fst fn_r1))) = (0x2b208%Z, [], [])
  /\ (nth 1 fn_sr1 (ELit 0), nth 10 fn_sr1 (ELit 0), nth 2 fn_sr1 (ELit 0), nth 4 fn_sr1 (ELit 0))
     = (ELit 0x15408, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x45480)
  /\ kn_vars_lt 40 fn_kn1 = true /\ kn_acall fn_kn1 = fn_kn2i
  /\ (s_pc (fst (fst fn_r2)), snd (fst fn_r2), s_log (fst (fst fn_r2))) = (0x2aed0%Z, [], [])
  /\ (nth 10 fn_sr2 (ELit 0), nth 2 fn_sr2 (ELit 0), nth 4 fn_sr2 (ELit 0)) = (EVar 7, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x45480).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma tl_itin :
  (s_pc (fst (fst tl_r1)), snd (fst tl_r1), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst tl_r1)))) = (0x156ac%Z, [], true)
  /\ (nth 1 tl_sr1 (ELit 0), nth 10 tl_sr1 (ELit 0), nth 11 tl_sr1 (ELit 0), nth 2 tl_sr1 (ELit 0), nth 3 tl_sr1 (ELit 0), nth 4 tl_sr1 (ELit 0))
     = (ELit 0x155a8, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x45480)
  /\ kn_vars_lt 50 tl_kn1 = true /\ sr_vars_lt 50 tl_sr1 = true /\ kn_fcall tl_kn1 = tl_kn2i
  /\ (s_pc (fst (fst tl_r2)), snd (fst tl_r2), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst tl_r2)))) = (0x15664%Z, [], true)
  /\ (s_pc (fst (fst p_r1)), snd (fst p_r1), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst p_r1))))
     = (0x2d7a0%Z, [], true)
  /\ (nth 17 p_sr1 (ELit 0), nth 10 p_sr1 (ELit 0), nth 11 p_sr1 (ELit 0)) = (ELit 29, ELit 1, ELit 0x5413)
  /\ (s_pc (fst (fst p_r2)), snd (fst p_r2), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst p_r2))))
     = (0x2d23c%Z, [], true)
  /\ stdio_call 82 p_sr2 p_kn2 = Some p_sc
  /\ (sc_ret p_sc, sc_f p_sc, sc_fd p_sc, sc_s p_sc, sc_l p_sc, sc_wb p_sc, sc_wp p_sc) = (0x2d7c4%Z, 0x35230%Z, 1%Z, ELit 0x1074a, ELit 1, ELit 0x65b50, ELit 0x65b51)
  /\ (s_pc (fst (fst p_r3l)), snd (fst p_r3l), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst p_r3l))))
     = (0x15594%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ (s_pc (fst (fst p_r3e)), snd (fst p_r3e), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst p_r3e))))
     = (0x2b208%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ kn_after p_r3e p_kn3i = p_kn3
  /\ (nth 10 p_sr3e (ELit 0), nth 1 p_sr3e (ELit 0), nth 2 p_sr3e (ELit 0), nth 4 p_sr3e (ELit 0)) = (EVar 15, ELit 0x155d4, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x45480).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma tl1_itin :
  (sr_mismatch tl1_rvl0 idb p_sr3l sr_TL 0, kn_missing p_kn3 (map (kmap tl1_rvl0 idb) kn_TL1)) = ([0%nat], [KRange (ELit 0x65b50) 0x65b50 0x65f48])
  /\ (s_pc (fst (fst tl1_r1)), snd (fst tl1_r1), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst tl1_r1)))) = (0x156ac%Z, [], true)
  /\ (nth 1 tl1_sr1 (ELit 0), nth 10 tl1_sr1 (ELit 0), nth 11 tl1_sr1 (ELit 0), nth 2 tl1_sr1 (ELit 0), nth 3 tl1_sr1 (ELit 0), nth 4 tl1_sr1 (ELit 0))
     = (ELit 0x155a8, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x45480)
  /\ kn_vars_lt 50 tl1_kn1 = true /\ sr_vars_lt 50 tl1_sr1 = true /\ kn_fcall tl1_kn1 = tl1_kn2i
  /\ (s_pc (fst (fst tl1_r2)), snd (fst tl1_r2), log_wdl_b 0 [(0x34000, 0x453b0); (0x65b28, 0x66000); (0x654c0, 0x656e0)]%Z (s_log (fst (fst tl1_r2)))) = (0x15664%Z, [], true)
  /\ (nth 1 tl1_sr2 (ELit 0), nth 2 tl1_sr2 (ELit 0), nth 11 tl1_sr2 (ELit 0)) = (ELit 0x155b8, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0)
  /\ sr_vars_lt 82 tl1_sr2 = true /\ kn_vars_lt 82 tl1_kn2 = true
  /\ (s_pc (fst (fst tl1_r3l)), snd (fst tl1_r3l), s_log (fst (fst tl1_r3l))) = (0x15594%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst tl1_r3e)), snd (fst tl1_r3e), s_log (fst (fst tl1_r3e))) = (0x2b208%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ kn_after tl1_r3e tl1_kn3i = tl1_kn3
  /\ (nth 10 tl1_sr3e (ELit 0), nth 1 tl1_sr3e (ELit 0), nth 2 tl1_sr3e (ELit 0), nth 4 tl1_sr3e (ELit 0)) = (EVar 15, ELit 0x155d4, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x45480)
  /\ (sr_mismatch tl1_rvl idb tl1_sr3l sr_TL 0, kn_missing tl1_kn3 (map (kmap tl1_rvl idb) kn_TL1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x65b50 0x65f48]).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma e_itin :
  (s_pc (fst (fst e_r2pn)), snd (fst e_r2pn), log_win_b 0 (s_log (fst (fst e_r2pn)))) = (0x15400%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2pc)), snd (fst e_r2pc), log_win_b 0 (s_log (fst (fst e_r2pc)))) = (0x15400%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tn)), snd (fst e_r2tn), log_win_b 0 (s_log (fst (fst e_r2tn)))) = (0x15400%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tc)), snd (fst e_r2tc), log_win_b 0 (s_log (fst (fst e_r2tc)))) = (0x15400%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := e_r2pc in
       (sr_mismatch (fn1_rvl (ELit 0x65b50) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x65b50) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x65b50) 0x65b50 0x65f50]))
  /\ (let r := e_r2pn in
       (sr_mismatch (fn1_rvl (ELit 0x65b50) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x65b50) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x65b50) 0x65b50 0x65f50]))
  /\ (let r := e_r2tc in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x65b50 0x65f50]))
  /\ (let r := e_r2tn in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x65b50 0x65f50]))
  /\ kn_vars_lt 114 p_kn3 = true /\ kn_acallT p_kn3 = e_kn1p /\ kn_vars_lt 114 tl1_kn3 = true /\ kn_acallT tl1_kn3 = e_kn1t.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fn1_itin :
  (s_pc (fst (fst fn1_r1)), snd (fst fn1_r1), s_log (fst (fst fn1_r1))) = (0x2b208%Z, [], [])
  /\ (nth 1 fn1_sr1 (ELit 0), nth 10 fn1_sr1 (ELit 0), nth 2 fn1_sr1 (ELit 0), nth 4 fn1_sr1 (ELit 0))
     = (ELit 0x15408, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x45480)
  /\ kn_vars_lt 40 fn1_kn1 = true /\ kn_acall fn1_kn1 = fn1_kn2i
  /\ (s_pc (fst (fst fn1_r2)), snd (fst fn1_r2), s_log (fst (fst fn1_r2))) = (0x2aed0%Z, [], [])
  /\ (nth 10 fn1_sr2 (ELit 0), nth 2 fn1_sr2 (ELit 0), nth 4 fn1_sr2 (ELit 0)) = (ELit 0, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x45480).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.

(* [comment removed for export] *)
Definition sr_FE : list expr :=
  [ELit 0; ELit 0x155d4; spx (-208); ELit 0x10800; ELit 0x45480; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; EVar 15; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; ELit 18446744073709551615; ELit 0x45380; ELit 0; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition kn_FE : list kentry := kn_TL1.
Definition fe_rvlp : list expr :=
  rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 p_sr3e (ELit 0)) (ELit 0x65b50) (sav_sr (EVar 40) (EVar 41) p_sr3e).
Definition fe_rvlt : list expr :=
  rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 tl1_sr3e (ELit 0)) (EAlu ALU_ADD (EVar 18) (ELit 2)) (sav_sr (EVar 40) (EVar 41) tl1_sr3e).
Definition fe_sr1i : list expr := Eval vm_compute in sr_after_call_j sr_FE KEPT_AL 50.
Definition fe_kn1i : list kentry := Eval vm_compute in kn_acallT kn_FE.
Definition fe_r2n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x155d4 fe_sr1i [] fe_kn1i 82).
Definition fe_r2c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x155d4 fe_sr1i [] fe_kn1i 82).

Section VP2.
Lemma fe_itin :
  (sr_mismatch fe_rvlp idb p_sr3e sr_FE 0, kn_missing p_kn3 (map (kmap fe_rvlp idb) kn_FE)) = ([0; 21]%nat, [KRange (ELit 0x65b50) 0x65b50 0x65f48])
  /\ (sr_mismatch fe_rvlt idb tl1_sr3e sr_FE 0, kn_missing tl1_kn3 (map (kmap fe_rvlt idb) kn_FE)) = ([0; 21]%nat, [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x65b50 0x65f48])
  /\ kn_vars_lt 50 kn_FE = true /\ kn_acallT kn_FE = fe_kn1i
  /\ (s_pc (fst (fst fe_r2n)), snd (fst fe_r2n), log_win_b 0 (s_log (fst (fst fe_r2n)))) = (0x15400%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst fe_r2c)), snd (fst fe_r2c), log_win_b 0 (s_log (fst (fst fe_r2c)))) = (0x15400%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := fe_r2n in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ (let r := fe_r2c in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ nth 19 p_sr3e (ELit 0) = ELit 18446744073709551615 /\ nth 19 tl1_sr3e (ELit 0) = ELit 18446744073709551615
  /\ tl1_sr1 = tl_sr1 /\ tl1_sr2i = tl_sr2i.
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP2.
End V10TRun_defs.

Module V10Grow.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10ReadErr_defs.
Import V10ReadErr.
Import V10Refused_defs.
Import V10Refused.
Import V10Grow_defs.
Import V10FuzzIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPSG scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSG scr NX true.

(* [comment removed for export] *)
Lemma bytes_at_rdn : forall M (a : Z) (bs : list byte),
  (0 <= a)%Z -> (a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  bytes_at M a bs -> rdn RSEGS M (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros M a bs Ha Hnw HB.
  rewrite <- (rdn_wbytes_hit RSEGS bs M (Z_to_bv 64 a)) by (rewrite u_small by lia; lia).
  apply rdn_agree. intros j Hj. rewrite u_small by lia.
  rewrite wbytes_inside by (rewrite ?u_small by lia; lia). rewrite !u_small by lia.
  rewrite (HB (Z.of_nat j) ltac:(lia)). do 2 f_equal. lia.
Qed.

Definition is_kblob_at (a : Z) (K : kentry) : bool :=
  match K with KBlob (SA (ELit 0) k) _ _ => (k =? a)%Z | _ => false end.

Section Grow.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let L : Z := Z.of_nat (length data).
  Let modelk := modelk path tid fs0 stdin0.
  Let at_loop := at_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let at_full := at_full sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let side := side sp0 mem0 lim.
  Let slots := slots sp0 a0s path envv tid.

  Lemma ownedA_rangeG : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z
                 \/ ((0x66000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
  Proof. exact (ownedA_range sp0 Hvsp AL_glob AL_grant). Qed.

  (* [comment removed for export] *)
  Lemma regs_after_allocG : forall vals sr R R',
    sr_vars_lt (length vals) sr = true -> regs_ok (ENV vals) sr R ->
    (forall r, callee_saved r -> getr R' r = getr R r) ->
    regs_ok (ENV (vals ++ junk_vals R')) (sr_after_call_j sr KEPT_AL (length vals)) R'.
  Proof.
    intros vals sr R R' HL HR Hcs.
    apply (regs_after_call vals _ sr R R' KEPT_AL); [exact HL | exact HR | | apply kept_al_no0].
    intros i Hi. destruct (kept_al_saved i Hi) as [H32 Hc]. split; [exact H32|]. apply Hcs. exact Hc.
  Qed.

  Lemma know_after_allocG : forall (A A' : AS) vals (M M' : word -> option byte) vm vm' R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 128 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 128)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acall kn).
  Proof.
    intros A A' vals M M' vm vm' R' kn HLv P0 Hlt HK HIA HtopA HI Htop Hfr Hgr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    unfold kn_acall. apply (know_ok_call RSEGS (ENV (vals ++ junk_vals R')) M M' GLOB A_SLO A_SHI IHI 0x34000).
    - cbn [ev ENV V10Open.ENV]. rewrite vals_ev_app_l by lia. rewrite P0. lia.
    - unfold IHI, WIN. lia.
    - unfold A_SLO, A_SHI, WIN. lia.
    - intros x Hnt. unfold touched in Hnt. cbn [ev ENV V10Open.ENV] in Hnt.
      rewrite vals_ev_app_l in Hnt by lia. rewrite P0 in Hnt.
      unfold IHI, WIN, A_SLO, A_SHI, GLOB in Hnt.
      apply Hfr.
      + intros Ho. destruct (ownedA_rangeG A M vm x HIA HtopA Ho) as [Hg|[Hh|Hl]].
        * apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [left; reflexivity | cbn; lia].
        * apply Hnt. right. left. lia.
        * apply Hnt. left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [right; right; left; reflexivity | cbn; lia].
      + intros Ho. destruct (ownedA_rangeG A' M' vm' x HI Htop Ho) as [Hg|[Hh|Hl]].
        * apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [left; reflexivity | cbn; lia].
        * apply Hnt. right. left. lia.
        * apply Hnt. left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [right; right; left; reflexivity | cbn; lia].
      + intros He. apply AL_errno in He. apply Hnt. left. split; [lia|]. exists (0x453dc, 0x453e0)%Z.
        split; [right; left; reflexivity | cbn; lia].
      + intros Hs. apply Hnt. right. right. unfold ALLOC_STACK in Hs. lia.
    - intros x Hx HM. cbn [ev ENV V10Open.ENV] in Hx. rewrite vals_ev_app_l in Hx by lia.
      rewrite P0 in Hx. unfold WIN in Hx. destruct (Hgr x HM) as [H|[H|H]]; [| | exact H].
      + pose proof AL_hi. exfalso. lia.
      + destruct (ownedA_rangeG A M vm x HIA HtopA H); exfalso; lia.
    - intros m a n H1 H2. apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2].
    - apply (env_app_know RSEGS vals (junk_vals R') _ M kn); [exact Hlt | exact HK].
  Qed.

  (* [comment removed for export] *)
  Lemma env_ok_alloc : forall A A' M M' vm vm',
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 128 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 128)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
  Proof.
    intros A A' M M' vm vm' (HEa & HEl & HEr) HIA HtopA HI Htop Hfr. pose proof SPlo.
    assert (FR : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z \/ (0x10000 <= bv_unsigned a < 0x65778)%Z ->
                 ~ (0x453dc <= bv_unsigned a < 0x453e0)%Z -> M' a = M a).
    { intros a Ha Hne. apply Hfr.
      - intros Ho. destruct (ownedA_rangeG A M vm a HIA HtopA Ho); lia.
      - intros Ho. destruct (ownedA_rangeG A' M' vm' a HI Htop Ho); lia.
      - intros He. apply AL_errno in He. lia.
      - unfold ALLOC_STACK. lia. }
    split; [|split].
    - intros a Ha. rewrite FR by lia. apply HEa. exact Ha.
    - intros a H1 H2. rewrite FR by lia. apply HEl; assumption.
    - intros a Ha. rewrite FR by lia. apply HEr. exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kimg_clearG : forall E M kn lo hi,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
  Proof.
    intros E M kn lo hi HK Hex. apply existsb_exists in Hex as (K & Hin & Hc).
    destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hn).
    intros i Hi. apply Hn. lia.
  Qed.

  Theorem full_refused : forall j buf cap, (2 ^ 26 <= cap)%Z -> at_full (t_die msg_refused fs0) j buf cap.
  Proof.
    intros j buf cap Hcap A vm vals R M HL SL HR HK HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    unfold V10ReadLoop.modelk.
    run_blk_keep (SCR [true] [] []) 41%nat.
    { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. match goal with |- ?g => idtac g end. unfold bv_eqb. rewrite u_srl64. rewrite P8, !u_small by lia.
      change (26 mod 64)%Z with 26%Z. apply (f_equal negb (y := false)). apply Z.eqb_neq.
      intros H0. pose proof (Z.div_le_mono (2 ^ 26) cap (2 ^ 26) ltac:(lia) Hcap) as Hd. rewrite Z.div_same in Hd by lia. lia. }
    cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    change fs0 with (m_fs (mkModelC (fdsk path cap) vm stdin0 fs0 None (Some tid) None)).
    lazymatch type of HR with regs_ok _ _ ?Rc => lazymatch type of HK with know_ok _ _ ?Mc _ =>
      apply (ref_refused_tail sp0 (blobs0 a0s path) (mkModelC (fdsk path cap) vm stdin0 fs0 None (Some tid) None) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) Rc Mc) end end.
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV V10Open.ENV].
      rewrite P0. first [reflexivity | f_equal; lia].
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ (-8388608 + d) m HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
      replace (bv_unsigned sp0 + (-8388608 + d))%Z with (bv_unsigned sp0 - 8388608 + d)%Z in Hst by lia. exact Hst.
    - unfold re_ivs. repeat (apply Forall_cons; [eapply kimg_clearG; [exact HK | vm_compute; reflexivity] |]). apply Forall_nil.
    - unfold cell. krd HK 0x453d8%Z 4%nat Htc. rewrite Htc. cbn [edenot ev ENV V10Open.ENV]. rewrite P5.
      rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact Htid.
    - unfold cell. krd HK 0x453b8%Z 8%nat Hsf. rewrite Hsf. reflexivity.
    - unfold cell. krd HK 0x65738%Z 8%nat Hpg. rewrite Hpg. reflexivity.
    - cbn. apply (length_guard_bytes a_draw).
    - lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kblob_at 0x656e8) in exact i) _ HK eq_refl) as KB end.
      cbn [kentry_ok] in KB. destruct KB as (_ & _ & KB). unfold elenZ, estart in KB. cbn [a_base a_off edenot eb ENV V10Open.ENV blobs_ev blobs0 nth] in KB.
      rewrite (u_small 8), (u_small 0) in KB by lia.
      intros i Hi. change (nth 2 (blobs0 a0s path) []) with (guard_bytes a_draw) in Hi |- *.
      rewrite Z.add_0_l in KB. apply KB. rewrite length_guard_bytes in Hi. exact Hi.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem full_grow : forall K j buf cap,
    (cap < 2 ^ 26)%Z ->
    (forall nb, at_loop K (S j) nb (2 * cap) cap) ->
    at_full K j buf cap.
  Proof.
    intros K j buf cap Hcap26 HLOOP A vm vals R M HL SL HR HK HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    assert (Hj : (Z.of_nat j <= 9)%Z).
    { destruct (Z_lt_ge_dec (Z.of_nat j) 10) as [|Hge]; [lia|]. exfalso.
      pose proof (Z.pow_le_mono_r 2 10 (Z.of_nat j) ltac:(lia) ltac:(lia)). change (2 ^ 10)%Z with 1024%Z in *. lia. }
    unfold V10ReadLoop.modelk.
    (* [comment removed for export] *)
    run_blk_keep (SCR [false] [] []) 41%nat.
    { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. unfold bv_eqb. rewrite u_srl64. rewrite P8, !u_small by lia.
      change (26 mod 64)%Z with 26%Z. rewrite Z.div_small by lia. reflexivity. }
    cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct g_itin1 as (_ & _ & CAP2 & _ & _ & _ & VLK1 & KNM).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (R10 : getr Rc 10 = Z_to_bv 64 (2 * cap)) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; rewrite P8; apply md_mul_Z);
      assert (R1 : getr Rc 1 = Z_to_bv 64 0x152b4) by (regv HR (1 : reg); reflexivity);
      assert (R4 : getr Rc 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity);
      assert (R2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
            rewrite P0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (EQcfg : mkst Rc (Z_to_bv 64 0x2b348) M (seg_rom RSEGS) = mkst Rc al_malloc_pc M al_rom)
        by (rewrite AL_malloc, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
    rewrite <- AL_segs.
    set (md := mkModelC (fdsk path cap) vm stdin0 fs0 None (Some tid) None).
    pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 9 ltac:(lia) Hj) as HP9. change (2 ^ 9)%Z with 512%Z in HP9.
    assert (Hcap25 : (cap <= 2 ^ 25)%Z) by (rewrite Hcapj; clear -HP9; lia).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (alloc_margin_le (2 * cap)) as HMG.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (ai_malloc_sure fx0 A M md Rc (2 * cap) (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap)
              (Z_to_bv 64 0x152b4) sp0 [a0s; path] envv K HI) end.
    - constructor; reflexivity.
    - apply AL_env. exact HE.
    - exact R10.
    - clear -Hcap25 Hc0. lia.
    - change (m_vmmaps md) with vm. exact Hroom.
    - unfold need_k. clear -Hj HFC0. lia.
    - unfold need_b. clear -Hcap25 Hc0 HMG Hj HFB0. lia.
    - unfold ROOM_NMAX. clear -Hcap25. lia.
    - exact R1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, R2, u_small by lia. lia.
    - rewrite R2, u_small by lia. lia.
    - (* [comment removed for export] *)
      intros a Ha. rewrite R2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeG A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - (* [comment removed for export] *)
      intros A' m' vm' regs' res HI' Ha0 Hcs Hnz Hl0 Hl1 Hlq' Hnew Hfr Hlm Hgr Hvl' Htop' Hisp' Hres' Hroom'.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop', Hvl', Hisp', Hres'. rewrite Htop in Htop'.
      unfold md. rewrite with_vmmaps_C. clear md.
      pose proof (u64_range res) as Hrr. pose proof (u64_range buf) as Hbr0.
      (* [comment removed for export] *)
      assert (Hbr : buf <> res) by (intros Heq; rewrite <- Heq in Hl0; rewrite Hl in Hl0; discriminate Hl0).
      assert (Hlbuf' : live A' buf = Some cap) by (rewrite (Hlq' buf Hbr); exact Hl).
      assert (HE' : env_ok sp0 mem0 m').
      { apply (env_ok_alloc A A' M m' vm vm' HE HI Htop HI' Htop'). intros a H1 H2 H3 H4. apply Hfr; try assumption.
        rewrite R2, u_small by lia. exact H4. }
      destruct (ai_live_hull A' m' vm' res (2 * cap) HI' Hl1) as (_ & Hres16 & Hend & HbytesN).
      pose proof (round16_ge (2 * cap)) as Hr2.
      assert (Hres31 : (0x66000 <= bv_unsigned res)%Z) by (apply (live_big_lo sp0 Hvsp AL_grant A' m' vm' res (2 * cap) HI' Hl1); lia).
      assert (HsomeN : forall x : word, (bv_unsigned res <= bv_unsigned x < bv_unsigned res + 2 * cap)%Z -> m' x <> None).
      { intros x Hx. destruct (HbytesN (bv_unsigned x - bv_unsigned res)%Z ltac:(lia)) as (_ & Hs & _ & _).
        unfold at_ in Hs. replace (bv_unsigned res + (bv_unsigned x - bv_unsigned res))%Z with (bv_unsigned x) in Hs by lia.
        rewrite Z_to_bv_bv_unsigned in Hs. exact Hs. }
      assert (Hfl : Z.of_nat (length (firstn (Z.to_nat cap) data)) = cap) by (rewrite length_firstn; unfold L in HcapL; lia).
      assert (HB' : bytes_at m' (bv_unsigned buf) (firstn (Z.to_nat cap) data)).
      { intros i Hi. rewrite Hfl in Hi. unfold bytes_at in HB. rewrite <- (HB i ltac:(rewrite Hfl; exact Hi)).
        pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq. }
      pose proof (ai_live_disjoint A' m' vm' res (2 * cap) buf cap HI' Hl1 Hlbuf' ltac:(intros Heq; apply Hbr; symmetry; exact Heq)) as Hdisj.
      pose proof (round16_ge cap) as Hr1.
      (* [comment removed for export] *)
      set (vals2 := vals ++ junk_vals regs').
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (A51 : vals_ev vals2 51 = res).
      { subst vals2. replace 51%nat with (length vals + 10)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r.
        unfold junk_vals, vals_ev. rewrite (nth_map_seq_gen _ 32 0 10) by lia. cbn [Nat.add]. rewrite <- Ha0. reflexivity. }
      assert (SL2 : slots vals2 buf cap cap) by (subst vals2; apply (slots_app sp0 a0s path envv tid data vals); [rewrite HL; lia | exact SL0]).
      destruct SL2 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG vals sr Rc regs' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs) as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2. change (sr_after_call_j g_sr1 KEPT_AL 41) with g_srM in HR2. clear HR. rename HR2 into HR.
      assert (HK2 : know_ok RSEGS (ENV vals2) m' g_knOK).
      { unfold g_knOK. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]]].
        * cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite A51. lia.
        * cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite A51. split; [lia | exact Hres16].
        * cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot ev ENV V10Open.ENV]. rewrite A51. split; [lia|].
          intros d m Hd Hm. apply store_ok_of_all; [rewrite u_small by lia; lia|].
          intros x Hx. rewrite u_small in Hx by lia. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)].
        * cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev ENV V10Open.ENV].
          rewrite Q0, A51. right. lia.
        * rewrite <- KNM. subst vals2.
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            eapply (know_after_allocG A A' vals M m' vm vm' regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK1) HK HI Htop HI' Htop') end.
          -- intros a H1 H2 H3 H4. apply Hfr; try assumption. rewrite R2, u_small by lia. exact H4.
          -- exact Hgr. }
      clear HK. rename HK2 into HK. clearbody vals2. clear KW R10 R1 R4 R2.
      (* [comment removed for export] *)
      run_blk_keep (SCR [false; false] [] []) 73%nat.
      { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite Q8. unfold bv_eqb. rewrite !u_small by lia. apply Z.eqb_neq. lia. }
      cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      (* [comment removed for export] *)
      set (bs0 := firstn (Z.to_nat cap) data) in *.
      assert (MC : mcH m' res buf cap bs0).
      { constructor; try lia.
        - apply (bytes_at_rdn m' (bv_unsigned buf) bs0 ltac:(lia) ltac:(lia)) in HB'. rewrite Z_to_bv_bv_unsigned in HB'. exact HB'.
        - apply store_ok_of_all; [lia|]. intros x Hx. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)]. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = Z_to_bv 64 0x152d0) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = res) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact A51);
        assert (B11 : getr Rc 11 = buf) by (regv HR (11 : reg); cbn [edenot ev ENV V10Open.ENV]; exact Q6);
        assert (B12 : getr Rc 12 = Z_to_bv 64 cap) by (regv HR (12 : reg); cbn [edenot ev ENV V10Open.ENV]; exact Q8);
        destruct (ref_memcpy m' res buf cap bs0 (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x152d0)
                    ltac:(apply ret_ok_even; reflexivity) A1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear A1 B10 B11 B12
      end.
      replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
      set (M2 := wbytes m' res bs0).
      assert (OUT2 : forall x : word, ~ (bv_unsigned res <= bv_unsigned x < bv_unsigned res + cap)%Z -> M2 x = m' x).
      { intros x Hx. subst M2. apply wbytes_outside; lia. }
      assert (HI2 : ainv A' M2 vm').
      { apply (ainv_frame_driver sp0 Hvsp AL_glob AL_grant A' m' M2 vm' HI' Htop'); [| apply wbytes_grows |].
        - intros a Ha. right; right. exists res, (2 * cap)%Z. split; [exact Hl1|].
          destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res)); [exfalso; apply Ha; apply OUT2; lia|].
          destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res + cap)); [lia | exfalso; apply Ha; apply OUT2; lia].
        - intros a Ha HM2. destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res)); [rewrite <- OUT2 by lia; exact HM2|].
          destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res + cap)); [apply HsomeN; lia | rewrite <- OUT2 by lia; exact HM2]. }
      assert (HE2 : env_ok sp0 mem0 M2).
      { destruct HE' as (E1 & E2 & E3). split; [|split].
        - intros a Ha. rewrite OUT2 by lia. apply E1. exact Ha.
        - intros a H1 H2. rewrite OUT2 by lia. apply E2; assumption.
        - intros a Ha. rewrite OUT2 by lia. apply E3. exact Ha. }
      assert (HBres : bytes_at M2 (bv_unsigned res) bs0).
      { intros i Hi. subst M2. rewrite wbytes_inside by (rewrite ?u_small by lia; lia). rewrite !u_small by lia. do 2 f_equal. lia. }
      (* [comment removed for export] *)
      destruct g_itin2 as (_ & _ & VLB & _ & SR3 & KN3 & VLK3).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm callee_kept ltac:(rewrite HL2; exact VLB) HR Hkeep callee_kept_no0) as HR3 end.
      rewrite HL2 in HR3. lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
      clear HR Hkeep.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_ok_call RSEGS (ENV vals2) m' M2 [] 0 0 IHI 0x34000) as KC;
        specialize (KC ltac:(cbn [ev ENV V10Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK3; clear KC
      end.
      specialize (HK3 ltac:(intros x Hnt; apply OUT2; unfold touched, IHI, WIN in Hnt; cbn [ev ENV V10Open.ENV] in Hnt; rewrite Q0 in Hnt; lia)
                      ltac:(intros x _ Hx; apply (wbytes_grows bs0 m' res); exact Hx)
                      ltac:(intros m a k H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
      lazymatch type of HK3 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK3 end. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) M2 _ ltac:(rewrite HL2; exact VLK3) HK3) as HK. clear HK3.
      rename HR3 into HR.
      set (vals3 := vals2 ++ junk_vals Rm) in *.
      assert (HL3 : length vals3 = 105%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (SL3 : slots vals3 buf cap cap) by (subst vals3; apply (slots_app sp0 a0s path envv tid data vals2); [rewrite HL2; lia | repeat split; assumption]).
      assert (R51 : vals_ev vals3 51 = res) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact A51).
      clearbody vals3. clear Q0 Q1 Q2 Q5 Q6 Q7 Q8. destruct SL3 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
      change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clearbody M2. clear MC HB'.
      (* [comment removed for export] *)
      run_blk_keep scr0 105%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      destruct g_itin3 as (_ & _ & VLK4 & KNL & IDL). apply pair_equal_spec in IDL as [MIS MISS].
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (F10 : getr Rc 10 = buf) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact Q6);
        assert (F1 : getr Rc 1 = Z_to_bv 64 0x152d8) by (regv HR (1 : reg); reflexivity);
        assert (F4 : getr Rc 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity);
        assert (F2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
          by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
              rewrite Q0; first [reflexivity | f_equal; lia])
      end.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals3) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                        _ _ _ d m HK eq_refl Hd Hm) as KW end.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (EQcfg : mkst Rc (Z_to_bv 64 0x2b208) M2 (seg_rom RSEGS) = mkst Rc al_free_pc M2 al_rom)
          by (rewrite AL_free, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
      rewrite <- AL_segs.
      set (md := mkModelC (fdsk path cap) vm' stdin0 fs0 None (Some tid) None).
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      eapply (ai_free_l fx0 A' M2 md Rc buf (Z_to_bv 64 0x152d8) sp0 [a0s; path] envv K HI2) end.
      + constructor; reflexivity.
      + apply AL_env. exact HE2.
      + exact F10.
      + right. exists cap. exact Hlbuf'.
      + exact F1.
      + apply AL_ret. apply ret_ok_even. reflexivity.
      + rewrite F4. symmetry. exact AL_tp.
      + rewrite F2. rewrite u_small by lia.
        replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
      + change (m_vmmaps md) with vm'. rewrite Htop', F2, u_small by lia. lia.
      + rewrite F2, u_small by lia. lia.
      + intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
        * pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
          unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite Q0 in Hst.
          replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
          rewrite Z_to_bv_bv_unsigned in Hst.
          pose proof (store_ok_all RSEGS M2 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
          rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
        * intros Ho. destruct (ownedA_rangeG A' M2 vm' a HI2 Htop' Ho); lia.
        * intros Hro. apply AL_ro in Hro. lia.
        * intros Hrw. apply AL_rw in Hrw. lia.
      + (* [comment removed for export] *)
        intros A'' m'' vm'' regs'' HI'' Hcs'' Hlbuf'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hvlb'' Hroom''.
        rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm' in Htop'', Hvl'', Hisp'', Hres'', Hvlb'', Hroom''. rewrite Htop' in Htop''.
        unfold md. rewrite with_vmmaps_C. clear md.
        assert (Hlres'' : live A'' res = Some (2 * cap)%Z) by (rewrite (Hlq'' res ltac:(intros Heq; apply Hbr; symmetry; exact Heq)); exact Hl1).
        assert (HS'' : side A'' vm'' m'' res (2 * cap) (S j)).
        { split; [|split; [|split]].
          - split; [exact HI''|]. split; [exact Hlres''|]. split.
            + intros q Hq. destruct (Z.eq_dec (bv_unsigned q) (bv_unsigned buf)) as [Heq|Hne].
              * assert (q = buf) by (apply bv_eq; exact Heq). subst q. exact Hlbuf''.
              * assert (Hqb : q <> buf) by (intros HH; apply Hne; rewrite HH; reflexivity).
                rewrite (Hlq'' q Hqb), (Hlq' q Hq). apply Hlq. exact Hqb.
            + (* [comment removed for export] *)
              destruct (need_grow FUZZ_CALLS FUZZ_BMAX j cap) as (EK & EB).
              pose proof (need_lo FUZZ_CALLS FUZZ_BMAX (S j) (2 * cap) HFC0 ltac:(clear -HFB0; lia)
                            ltac:(rewrite Nat2Z.inj_succ; clear -Hj; lia) ltac:(clear -Hcap25 Hc0; lia)) as (HK1 & HB1).
              apply (aroom_mono A'' vm'' _ _ _ _ (Hroom'' _ _ Hroom')); clear -EK EB HK1 HB1 HMG HFC0 HFB0; lia.
          - split; [rewrite Hvl'', Hvl'; exact Hvl|]. split; [exact Htop''|]. split; [rewrite Hisp'', Hisp'; exact Hisp|].
            rewrite Hres'', Hres'; exact Hres.
          - apply (env_ok_alloc A' A'' M2 m'' vm' vm'' HE2 HI2 Htop' HI'' Htop''). intros a H1 H2 H3 H4. apply Hfr''; try assumption.
            rewrite F2, u_small by lia. exact H4.
          - split; [rewrite Hcapj, Nat2Z.inj_succ, Z.pow_succ_r by lia; lia | rewrite Nat2Z.inj_succ; lia]. }
        assert (HB'' : bytes_at m'' (bv_unsigned res) (firstn (Z.to_nat cap) data)).
        { intros i Hi. fold bs0. fold bs0 in Hi. rewrite <- (HBres i Hi).
          pose proof (Hlm'' res (2 * cap)%Z i Hlres'' ltac:(subst bs0; lia)) as Hq. unfold at_ in Hq. exact Hq. }
        (* [comment removed for export] *)
        set (vals4 := vals3 ++ junk_vals regs'').
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (regs_after_allocG vals3 sr Rc regs'' ltac:(rewrite HL3; vm_compute; reflexivity) HR Hcs'') as HR4 end.
        rewrite HL3 in HR4. fold vals4 in HR4.
        lazymatch type of HR4 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR4 end.
        clear HR. rename HR4 into HR.
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          pose proof (know_after_allocG A' A'' vals3 M2 m'' vm' vm'' regs'' kn ltac:(rewrite HL3; lia) Q0 ltac:(rewrite HL3; exact VLK4) HK HI2 Htop' HI'' Htop'') as HK4 end.
        specialize (HK4 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                        ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
        lazymatch type of HK4 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK4 end.
        fold vals4 in HK4. clear HK. rename HK4 into HK.
        assert (HL4 : length vals4 = 137%nat) by (subst vals4; rewrite length_app, junk_vals_length, HL3; reflexivity).
        assert (SL4 : slots vals4 buf cap cap) by (subst vals4; apply (slots_app sp0 a0s path envv tid data vals3); [rewrite HL3; lia | repeat split; assumption]).
        assert (S51 : vals_ev vals4 51 = res) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact R51).
        clearbody vals4. clear Q0 Q1 Q2 Q5 Q6 Q7 Q8. destruct SL4 as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8).
        apply (HLOOP res A'' vm'' (map (edenot (ENV vals4)) g_rvl) regs'' m'').
        * rewrite length_map. reflexivity.
        * unfold V10ReadLoop.slots. rewrite !vals_ev_map by (cbn; lia). cbn [nth g_rvl rvl9 app tl cap2_x edenot ev ENV V10Open.ENV].
          rewrite Q8, md_mul_Z. repeat split; assumption || reflexivity.
        * change (ENV (map (edenot (ENV vals4)) g_rvl)) with (xenv (ENV vals4) g_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals4) g_rvl idb _ (fun k => eq_refl) srb sr_L _ HR eq_refl eq_refl)) end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * change (ENV (map (edenot (ENV vals4)) g_rvl)) with (xenv (ENV vals4) g_rvl (blobs_ev (blobs0 a0s path))).
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals4) g_rvl idb _ _ kn kn_ML (fun k => eq_refl) HK) end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply (kwr_buf sp0 mem0 lim Hvsp data AL_grant A'' vm'' m'' res (2 * cap) (S j) _ (EVar 51) HS'').
          cbn [edenot ev ENV V10Open.ENV]. exact S51.
        * exact HS''.
        * exact HB''.
        * lia.
        * exact HcapL.
  Qed.
End Grow.
End V10Grow.

Module V10MainDir.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10ReadErr.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10DirRead.
Import V10OpenFailBranch.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section MainDir.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model1g := V10Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall z, In z [0x15260; 0x1528c; 0x15308; 0x15408; 0x15538]%Z -> al_ret_ok (Z_to_bv 64 z).
  Hypothesis AL_env : forall M, V10Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let model0 := V10Open.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem ref_dir_path :
    path = dot_path ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0)
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
  Proof.
    intros Hdot. unfold t_opened_dir.
    apply (V10Open.open_dir_pipeline sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Htid ME _ _ Hdot).
    - apply (open_err_branch_cannot_open sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp ME Hfits).
    - intros vals R M HL P0 P1 P2 P5 HR HK HOW.
      apply (V10Malloc65536.malloc65536_node sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hvsp Htid ME Hbrk Hlim
               AL_segs AL_rom AL_malloc AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret AL_env FdDir _
               (dir_read_error sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Htid ME Hdot)
               vals R M HL P0 P1 P2 P5 HR HK HOW).
  Qed.
End MainDir.
End V10MainDir.

Module V10Hdr.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Oom.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10Hdr_defs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPSH scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSH scr NX true.
Tactic Notation "run_blk2_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSH2 scr NX true.

(* [comment removed for export] *)
Ltac close_exit_gen HR HK P0 Hh Hlazy sp0 OFF WLO WP2 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V10Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V10Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev V10Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | left; unfold atexit_none; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Definition MSG_SHORT : list byte := msg_short.
Definition MSG_OVERRUN : list byte := msg_overrun.
Lemma MSG_SHORT_len : length MSG_SHORT = 31%nat. Proof. reflexivity. Qed.
Lemma MSG_OVERRUN_len : length MSG_OVERRUN = 31%nat. Proof. reflexivity. Qed.
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x114cc) 31 = Some MSG_SHORT.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x108c8) 31 = Some MSG_OVERRUN.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof cfgF_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). rewrite forallb_forall in T.
  specialize (T b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  apply bv_eq. rewrite T. symmetry. apply u_small.
  pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)). lia.
Qed.
Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 41) (vals_ev vals 42).
Proof. intros. reflexivity. Qed.

Section Hdr.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let L : Z := Z.of_nat (length data).
  Let model2 := model2 tid fs0 stdin0.
  Let at_header := at_header sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let side := side sp0 mem0 lim.
  Let slots := slots sp0 a0s path envv tid.

  (* [comment removed for export] *)
  Definition hdr_b0 : Z := bv_unsigned (nth 0 data (Z_to_bv 8 0)).
  Definition hdr_b1 : Z := bv_unsigned (nth 1 data (Z_to_bv 8 0)).
  Definition hdr_b2 : Z := bv_unsigned (nth 2 data (Z_to_bv 8 0)).
  Definition hdr_cfg : Z := ((hdr_b0 + 256 * hdr_b1) mod 32768)%Z.
  Definition hdr_b1s : Z := bv_swrap 8 hdr_b1.       (* [comment removed for export] *)
  Lemma b0_rng : (0 <= hdr_b0 < 256)%Z. Proof. unfold hdr_b0. pose proof (bv_unsigned_in_range _ (nth 0 data (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256%Z in H. lia. Qed.
  Lemma b1_rng : (0 <= hdr_b1 < 256)%Z. Proof. unfold hdr_b1. pose proof (bv_unsigned_in_range _ (nth 1 data (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256%Z in H. lia. Qed.
  Lemma b2_rng : (0 <= hdr_b2 < 256)%Z. Proof. unfold hdr_b2. pose proof (bv_unsigned_in_range _ (nth 2 data (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256%Z in H. lia. Qed.
  Lemma cfg_rng : (0 <= hdr_cfg < 32768)%Z. Proof. unfold hdr_cfg. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Definition slotsR (vals : list word) (buf : word) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 sp0 a0s path envv /\ vals_ev vals 2 = p1 sp0 a0s path envv
    /\ vals_ev vals 5 = tid /\ vals_ev vals 6 = buf /\ vals_ev vals 7 = Z_to_bv 64 L
    /\ vals_ev vals 8 = Z_to_bv 64 hdr_cfg /\ vals_ev vals 9 = Z_to_bv 64 (L - 6 - hdr_cfg)
    /\ vals_ev vals 10 = Z_to_bv 64 hdr_b1s /\ vals_ev vals 11 = Z_to_bv 64 hdr_b2
    /\ vals_ev vals 12 = Z_to_bv 64 (bv_unsigned buf + 6 + hdr_cfg).

  Definition at_trun (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 45%nat -> slotsR vals buf ->
      regs_ok (ENV vals) sr_R R -> know_ok RSEGS (ENV vals) M kn_R ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z -> (6 + hdr_cfg <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x154dc) M (seg_rom RSEGS)) (model2 vm)) K.

  Definition hdr_shape (K : TSet) : TSet :=
    if (L <? 6)%Z then t_die msg_short fs0 else if (L <? 6 + hdr_cfg)%Z then t_die msg_overrun fs0 else K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ownedA_rangeH : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z
                 \/ ((0x66000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
  Proof. exact (ownedA_range sp0 Hvsp AL_glob AL_grant). Qed.

  Lemma msg_tail : forall j buf cap A vm vals R M,
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 5 = tid -> vals_ev vals 6 = buf ->
    regs_ok (ENV vals) sr_F2 R -> know_ok RSEGS (ENV vals) M kn_F2 -> side A vm M buf cap j ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x15400) M (seg_rom RSEGS)) (model2 vm)) (t_exit (exit_code 2) fs0).
  Proof.
    intros j buf cap A vm vals R M HL P0 P5 P6 HR HK HS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    unfold model2, V10ReadLoop.model2.
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct f_itin as (_ & _ & VLK1 & KNF & _ & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (F10 : getr Rc 10 = buf) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact P6);
      assert (F1 : getr Rc 1 = Z_to_bv 64 0x15408) by (regv HR (1 : reg); reflexivity);
      assert (F4 : getr Rc 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity);
      assert (F2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
            rewrite P0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (EQcfg : mkst Rc (Z_to_bv 64 0x2b208) M (seg_rom RSEGS) = mkst Rc al_free_pc M al_rom)
        by (rewrite AL_free, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
    rewrite <- AL_segs.
    set (md := mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (ai_free fx0 A M md Rc buf (Z_to_bv 64 0x15408) sp0 [a0s; path] envv (t_exit (exit_code 2) fs0) HI) end.
    - constructor; reflexivity.
    - apply AL_env. exact HE.
    - exact F10.
    - right. exists cap. exact Hl.
    - exact F1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite F4. symmetry. exact AL_tp.
    - rewrite F2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, F2, u_small by lia. lia.
    - rewrite F2, u_small by lia. lia.
    - intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeH A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - (* [comment removed for export] *)
      intros A'' m'' vm'' regs'' HI'' Hcs'' Hlbuf'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hvlb''.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      set (vals2 := vals ++ junk_vals regs'').
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs'' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs'') as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_after_allocG sp0 a0s path Hvsp data AL_glob AL_grant AL_errno AL_hi A A'' vals M m'' vm vm'' regs'' kn
                      ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK1) HK HI Htop HI'' Htop'') as HK2 end.
      specialize (HK2 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                      ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
      lazymatch type of HK2 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK2 end.
      fold vals2 in HK2. clear HK. rename HK2 into HK.
      assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      (* [comment removed for export] *)
      run_blk_keep scr0 71%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      assert (Hh : m_halted (mkModelC V10Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = None) by reflexivity.
      assert (Hlazy : m_vm_lazy (mkModelC V10Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = []) by reflexivity.
      close_exit_gen HR HK Q0 Hh Hlazy sp0 48%Z (-192)%Z (Z_to_bv 64 0x65b48).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma kimg_rdn_msg : forall E M kn (a : Z) bs,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov a 31) kn = true ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 31 = Some bs -> (0 <= a)%Z -> (a + 31 < 2 ^ 64)%Z ->
    rdn RSEGS M (Z_to_bv 64 a) 31 = Some bs.
  Proof.
    intros E M kn a bs HK Hex Himg Ha0 Ha1. apply existsb_exists in Hex as (K & Hin & Hc).
    destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hn).
    rewrite <- Himg. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply Hn. lia.
  Qed.

  Theorem header_short : forall j buf cap, (L < 6)%Z -> at_header (t_die msg_short fs0) j buf cap.
  Proof.
    intros j buf cap HL6 A vm vals R M HL SL HR HK HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    unfold V10ReadLoop.model2. unfold t_die.
    (* [comment removed for export] *)
    run_blk_keep (SCR [true] [] []) 41%nat.
    { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite P7. unfold bv_ltu. rewrite !u_small by (unfold L in *; lia).
      cbn. apply (f_equal negb (y := false)). apply Z.ltb_ge. unfold L in HL6 |- *. lia. }
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (side_block_wd sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap j E log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
    rewrite <- EQM in HS1, OUT1.
    assert (HB1 : bytes_at M0 (bv_unsigned buf) data).
    { intros i Hi. unfold L in *. pose proof (u_small (bv_unsigned buf + i) ltac:(lia)) as Hu.
      rewrite OUT1; [apply HB; exact Hi | unfold V10ReadLoop.in_win; rewrite Hu; lia | rewrite Hu; lia]. }
    clear EQM HS HB.
    assert (Hsrc : rdn RSEGS M0 (Z_to_bv 64 0x114cc) 31 = Some MSG_SHORT).
    { lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (kimg_rdn_msg (ENV vals) M0 kn 0x114cc MSG_SHORT HK ltac:(vm_compute; reflexivity) msg_short_img); lia end. }
    replace (W 2 msg_short) with (map (WriteEv (Z_to_bv 64 2)) ([] ++ MSG_SHORT)) by reflexivity.
    pose proof h_itinS as (_ & SC & _ & _ & IF). apply pair_equal_spec in IF as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?md) _ =>
    apply (stdio_call_sound_fr vals (blobs_ev (blobs0 a0s path)) h_srS h_knS Rc Mc md h_scS [] MSG_SHORT
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n h_srS h_knS) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn h_scS length Z.of_nat] end.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - lia.
    - cbn [edenot]. rewrite MSG_SHORT_len. apply u_small. lia.
    - rewrite MSG_SHORT_len. cbn [length Z.of_nat]. lia.
    - rewrite MSG_SHORT_len. cbn [length Z.of_nat]. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V10Open.ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V10Open.ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [edenot]. rewrite MSG_SHORT_len. exact Hsrc.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK HPOST.
      (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows _ _ _]. cbn [edenot ev ENV V10Open.ENV] in Pagree. rewrite P0 in Pagree.
      rewrite alu_add_wZ, u_small in Pagree by lia.
      assert (HS2 : side A vm M2 buf cap j).
      { apply (side_frame sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M0 M2 buf cap j HS1); [| exact Pgrows].
        intros x Hne.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192 - 112)) as [H1|H1];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192)) as [H2|H2]; [left; unfold V10ReadLoop.in_win; lia|]];
          (destruct (Z_lt_ge_dec (bv_unsigned x) (0x35140 + 32)) as [H3|H3];
            [| destruct (Z_lt_ge_dec (bv_unsigned x) (0x35140 + 64)) as [H4|H4]; [right; left; unfold V10ReadLoop.in_data; lia|]]);
          exfalso; apply Hne; apply Pagree; lia. }
      assert (HB2 : bytes_at M2 (bv_unsigned buf) data).
      { intros i Hi. unfold L in *. pose proof (u_small (bv_unsigned buf + i) ltac:(lia)) as Hu.
        rewrite Pagree; [apply HB1; exact Hi | rewrite Hu; lia | rewrite Hu; lia | rewrite Hu; lia]. }
      clear HS1 HB1 Pagree Pgrows.
      set (vals2 := vals ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = buf) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      (* [comment removed for export] *)
      run_blk2_keep scr0 73%nat.
      lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
        destruct (side_block sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M2 buf cap j E log HS2 ltac:(vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
      rewrite <- EQM in HS3, OUT3. clear EQM.
      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (msg_tail j buf cap A vm (map (edenot (ENV vals2)) f_rvlS) Rx Mx) end.
      + rewrite length_map. reflexivity.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlS app edenot ev ENV V10Open.ENV]. exact Q0.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlS app edenot ev ENV V10Open.ENV]. exact Q5.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlS app edenot ev ENV V10Open.ENV]. exact Q6.
      + change (ENV (map (edenot (ENV vals2)) f_rvlS)) with (xenv (ENV vals2) f_rvlS (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) f_rvlS idb _ (fun k => eq_refl) srb sr_F2 _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + change (ENV (map (edenot (ENV vals2)) f_rvlS)) with (xenv (ENV vals2) f_rvlS (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals2) f_rvlS idb _ _ kn kn_F2 (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + exact HS3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kwordv1_of_mem : forall E M (e : expr) (a : word) off (i : nat) (z : Z),
    edenot E e = a -> ev E i = Z_to_bv 64 z -> (0 <= z < 256)%Z ->
    (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + 1 <= 2 ^ 64)%Z ->
    M (Z_to_bv 64 (bv_unsigned a + off)) = Some (Z_to_bv 8 z) ->
    kentry_ok RSEGS E M (KWord (SA e off) 1 (EVar i)).
  Proof.
    intros E M e a off i z He Hi Hz H1 H2 Hm.
    eapply (kword_intro RSEGS E M e a off 1 (EVar i) (Z_to_bv 64 z)); try assumption; try reflexivity; try lia.
    rewrite (rdn_1_of_mem RSEGS M _ _ Hm). cbn. rewrite u_small by lia. reflexivity.
  Qed.

  Lemma cfgx_val : forall vals, vals_ev vals 41 = Z_to_bv 64 hdr_b0 -> vals_ev vals 42 = Z_to_bv 64 hdr_b1 ->
    edenot (ENV vals) cfglen_x = Z_to_bv 64 hdr_cfg.
  Proof.
    intros vals H41 H42. unfold ENV, V10Open.ENV. rewrite cfglen_x_cfgF, H41, H42. unfold hdr_cfg. apply cfgF_val; [apply b0_rng | apply b1_rng].
  Qed.

  (* [comment removed for export] *)
  Lemma hdr6_entry : forall A vm vals R M buf cap j,
    length vals = 41%nat -> slots vals buf L cap ->
    regs_ok (ENV vals) sr_H R -> know_ok RSEGS (ENV vals) M kn_ML -> side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data ->
    (6 <= L)%Z ->
    let vals3 := vals ++ [Z_to_bv 64 hdr_b0; Z_to_bv 64 hdr_b1; Z_to_bv 64 hdr_b2] in
    length vals3 = 44%nat /\ slots vals3 buf L cap
    /\ vals_ev vals3 41 = Z_to_bv 64 hdr_b0 /\ vals_ev vals3 42 = Z_to_bv 64 hdr_b1 /\ vals_ev vals3 43 = Z_to_bv 64 hdr_b2
    /\ regs_ok (ENV vals3) sr_H R /\ know_ok RSEGS (ENV vals3) M kn_H6.
  Proof.
    intros A vm vals R M buf cap j HL SL HR HK HS HB HL6 vals3.
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb). pose proof SPlo.
    pose proof b0_rng as R0. pose proof b1_rng as R1. pose proof b2_rng as R2.
    assert (E41 : vals_ev vals3 41 = Z_to_bv 64 hdr_b0) by (subst vals3; replace 41%nat with (length vals + 0)%nat by (rewrite HL; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (E42 : vals_ev vals3 42 = Z_to_bv 64 hdr_b1) by (subst vals3; replace 42%nat with (length vals + 1)%nat by (rewrite HL; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (E43 : vals_ev vals3 43 = Z_to_bv 64 hdr_b2) by (subst vals3; replace 43%nat with (length vals + 2)%nat by (rewrite HL; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (SL3 : slots vals3 buf L cap) by (subst vals3; apply (slots_app sp0 a0s path envv tid data vals); [rewrite HL; lia | exact SL]).
    split; [subst vals3; rewrite length_app, HL; reflexivity|]. split; [exact SL3|]. split; [exact E41|]. split; [exact E42|]. split; [exact E43|].
    split.
    - apply (env_app_regs vals _ (blobs_ev (blobs0 a0s path)) sr_H R ltac:(rewrite HL; vm_compute; reflexivity) HR).
    - destruct SL3 as (Q0 & _ & _ & _ & Q6 & Q7 & _). unfold L in *.
      assert (BY : forall k, (0 <= k < 3)%Z -> M (Z_to_bv 64 (bv_unsigned buf + k)) = Some (nth (Z.to_nat k) data (Z_to_bv 8 0))).
      { intros k Hk. apply HB. lia. }
      unfold kn_H6. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]]]]].
      + apply (kwordv1_of_mem (ENV vals3) M (EVar 6) buf 0 41 hdr_b0); [cbn [edenot ev ENV V10Open.ENV]; exact Q6 | exact E41 | lia | lia | lia |].
        rewrite BY by lia. unfold hdr_b0. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + apply (kwordv1_of_mem (ENV vals3) M (EVar 6) buf 1 42 hdr_b1); [cbn [edenot ev ENV V10Open.ENV]; exact Q6 | exact E42 | lia | lia | lia |].
        rewrite BY by lia. unfold hdr_b1. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + apply (kwordv1_of_mem (ENV vals3) M (EVar 6) buf 2 43 hdr_b2); [cbn [edenot ev ENV V10Open.ENV]; exact Q6 | exact E43 | lia | lia | lia |].
        rewrite BY by lia. unfold hdr_b2. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite E41, u_small by lia. lia.
      + cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite E42, u_small by lia. lia.
      + cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite E43, u_small by lia. lia.
      + apply (env_app_know RSEGS vals _ (blobs_ev (blobs0 a0s path)) M kn_ML ltac:(rewrite HL; vm_compute; reflexivity) HK).
  Qed.

  Theorem header_overrun : forall j buf cap, (6 <= L)%Z -> (L < 6 + hdr_cfg)%Z -> at_header (t_die msg_overrun fs0) j buf cap.
  Proof.
    intros j buf cap HL6 HLc A vm vals0 R M HL0 SL0 HR0 HK0 HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (hdr6_entry A vm vals0 R M buf cap j HL0 SL0 HR0 HK0 HS HB HL6) as (HL & SL & E41 & E42 & E43 & HR & HK).
    set (vals := vals0 ++ _) in HL, SL, E41, E42, E43, HR, HK. clearbody vals. clear HL0 SL0 HR0 HK0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof (cfgx_val vals E41 E42) as CFG. pose proof cfg_rng as Hcr.
    unfold V10ReadLoop.model2. unfold t_die.
    (* [comment removed for export] *)
    run_blk_keep (SCR [false; true] [] []) 44%nat.
    { cbn [sc_denot branch_taken]. fold cfglen_x. cbn [edenot]. rewrite CFG. cbn [ev ENV V10Open.ENV]. rewrite P7, alu_add_Z.
      unfold bv_ltu. rewrite !u_small by (unfold L in *; lia). apply Z.ltb_lt. unfold L in *. lia. }
    { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite P7. unfold bv_ltu. rewrite !u_small by (unfold L in *; lia).
      cbn. apply (f_equal negb (y := true)). apply Z.ltb_lt. unfold L in *. lia. }
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (side_block_wd sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap j E log HS ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end.
    rewrite <- EQM in HS1, OUT1.
    clear EQM HS HB.
    assert (Hsrc : rdn RSEGS M0 (Z_to_bv 64 0x108c8) 31 = Some MSG_OVERRUN).
    { lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (kimg_rdn_msg (ENV vals) M0 kn 0x108c8 MSG_OVERRUN HK ltac:(vm_compute; reflexivity) msg_overrun_img); lia end. }
    replace (W 2 msg_overrun) with (map (WriteEv (Z_to_bv 64 2)) ([] ++ MSG_OVERRUN)) by reflexivity.
    pose proof h_itinO as (_ & SC & _ & _ & IF). apply pair_equal_spec in IF as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?md) _ =>
    apply (stdio_call_sound_fr vals (blobs_ev (blobs0 a0s path)) h_srO h_knO Rc Mc md h_scO [] MSG_OVERRUN
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n h_srO h_knO) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn h_scO length Z.of_nat] end.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - lia.
    - cbn [edenot]. rewrite MSG_OVERRUN_len. apply u_small. lia.
    - rewrite MSG_OVERRUN_len. cbn [length Z.of_nat]. lia.
    - rewrite MSG_OVERRUN_len. cbn [length Z.of_nat]. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V10Open.ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V10Open.ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [edenot]. rewrite MSG_OVERRUN_len. exact Hsrc.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK HPOST.
      destruct HPOST as [Pagree Pgrows _ _ _]. cbn [edenot ev ENV V10Open.ENV] in Pagree. rewrite P0 in Pagree.
      rewrite alu_add_wZ, u_small in Pagree by lia.
      assert (HS2 : side A vm M2 buf cap j).
      { apply (side_frame sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M0 M2 buf cap j HS1); [| exact Pgrows].
        intros x Hne.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192 - 112)) as [H1|H1];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 192)) as [H2|H2]; [left; unfold V10ReadLoop.in_win; lia|]];
          (destruct (Z_lt_ge_dec (bv_unsigned x) (0x35140 + 32)) as [H3|H3];
            [| destruct (Z_lt_ge_dec (bv_unsigned x) (0x35140 + 64)) as [H4|H4]; [right; left; unfold V10ReadLoop.in_data; lia|]]);
          exfalso; apply Hne; apply Pagree; lia. }
      clear HS1 Pagree Pgrows.
      set (vals2 := vals ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 76%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = buf) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      (* [comment removed for export] *)
      run_blk2_keep scr0 76%nat.
      lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
        destruct (side_block sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M2 buf cap j E log HS2 ltac:(vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
      rewrite <- EQM in HS3, OUT3. clear EQM.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (msg_tail j buf cap A vm (map (edenot (ENV vals2)) f_rvlO) Rx Mx) end.
      + rewrite length_map. reflexivity.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlO app edenot ev ENV V10Open.ENV]. exact Q0.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlO app edenot ev ENV V10Open.ENV]. exact Q5.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth f_rvlO app edenot ev ENV V10Open.ENV]. exact Q6.
      + change (ENV (map (edenot (ENV vals2)) f_rvlO)) with (xenv (ENV vals2) f_rvlO (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) f_rvlO idb _ (fun k => eq_refl) srb sr_F2 _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + change (ENV (map (edenot (ENV vals2)) f_rvlO)) with (xenv (ENV vals2) f_rvlO (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals2) f_rvlO idb _ _ kn kn_F2 (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + exact HS3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bytes_le_to_Z_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
  Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

  Theorem header_ok : forall K j buf cap, (6 + hdr_cfg <= L)%Z -> at_trun K j buf cap -> at_header K j buf cap.
  Proof.
    intros K j buf cap HLc HTR A vm vals0 R M HL0 SL0 HR0 HK0 HS HB HcapL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof cfg_rng as Hcr.
    destruct (hdr6_entry A vm vals0 R M buf cap j HL0 SL0 HR0 HK0 HS HB ltac:(lia)) as (HL3 & SL3 & E41 & E42 & E43 & HR3 & HK3).
    set (vals3 := vals0 ++ _) in HL3, SL3, E41, E42, E43, HR3, HK3. clearbody vals3. clear HL0 SL0 HR0 HK0.
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    (* [comment removed for export] *)
    set (byte := fun k : Z => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat k) data (Z_to_bv 8 0)))).
    set (vals := vals3 ++ [byte (hdr_cfg + 3); byte (hdr_cfg + 2); byte (hdr_cfg + 4); byte (hdr_cfg + 5)]%Z).
    assert (HL : length vals = 48%nat) by (subst vals; rewrite length_app, HL3; reflexivity).
    assert (SL : slots vals buf L cap) by (subst vals; apply (slots_app sp0 a0s path envv tid data vals3); [rewrite HL3; lia | exact SL3]).
    assert (P41 : vals_ev vals 41 = Z_to_bv 64 hdr_b0) by (subst vals; rewrite vals_ev_app_l by (rewrite HL3; lia); exact E41).
    assert (P42 : vals_ev vals 42 = Z_to_bv 64 hdr_b1) by (subst vals; rewrite vals_ev_app_l by (rewrite HL3; lia); exact E42).
    assert (P43 : vals_ev vals 43 = Z_to_bv 64 hdr_b2) by (subst vals; rewrite vals_ev_app_l by (rewrite HL3; lia); exact E43).
    assert (P44 : vals_ev vals 44 = byte (hdr_cfg + 3)%Z) by (subst vals; replace 44%nat with (length vals3 + 0)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (P45 : vals_ev vals 45 = byte (hdr_cfg + 2)%Z) by (subst vals; replace 45%nat with (length vals3 + 1)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (P46 : vals_ev vals 46 = byte (hdr_cfg + 4)%Z) by (subst vals; replace 46%nat with (length vals3 + 2)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    assert (P47 : vals_ev vals 47 = byte (hdr_cfg + 5)%Z) by (subst vals; replace 47%nat with (length vals3 + 3)%nat by (rewrite HL3; reflexivity); rewrite vals_ev_app_r; reflexivity).
    pose proof (env_app_regs vals3 [byte (hdr_cfg + 3); byte (hdr_cfg + 2); byte (hdr_cfg + 4); byte (hdr_cfg + 5)]%Z (blobs_ev (blobs0 a0s path)) sr_H R ltac:(rewrite HL3; vm_compute; reflexivity) HR3) as HR.
    pose proof (env_app_know RSEGS vals3 [byte (hdr_cfg + 3); byte (hdr_cfg + 2); byte (hdr_cfg + 4); byte (hdr_cfg + 5)]%Z (blobs_ev (blobs0 a0s path)) M kn_H6 ltac:(rewrite HL3; vm_compute; reflexivity) HK3) as HK.
    fold vals in HR, HK. change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) with (ENV vals) in HR, HK.
    clear HR3 HK3. clearbody vals. destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8).
    pose proof (cfgx_val vals P41 P42) as CFG.
    assert (ACFG : edenot (ENV vals) (EAlu ALU_ADD (EVar 6) cfglen_x) = Z_to_bv 64 (bv_unsigned buf + hdr_cfg)).
    { cbn [edenot]. rewrite CFG. cbn [ev ENV V10Open.ENV]. rewrite P6. apply alu_add_wZ. }
    assert (RB : forall k, (2 <= k <= 5)%Z ->
      (exists bs, rdn RSEGS M (adenot (ENV vals) (SA (EAlu ALU_ADD (EVar 6) cfglen_x) k)) 1 = Some bs
                  /\ Z_to_bv 64 (extz false 1 (bytes_le_to_Z bs)) = byte (hdr_cfg + k)%Z)
      /\ flat (ENV vals) (SA (EAlu ALU_ADD (EVar 6) cfglen_x) k) (elenZ (ENV vals) (ELit 1))).
    { intros k Hk. unfold adenot, flat, estart, elenZ. cbn [a_base a_off]. rewrite ACFG. unfold v_addi. rewrite !u_small by lia.
      cbn [edenot]. rewrite u_small by lia. split; [|lia].
      exists [nth (Z.to_nat (hdr_cfg + k)) data (Z_to_bv 8 0)]. split.
      - apply rdn_1_of_mem. replace (bv_unsigned buf + hdr_cfg + k)%Z with (bv_unsigned buf + (hdr_cfg + k))%Z by lia. apply HB. unfold L in *. lia.
      - unfold extz. rewrite bytes_le_to_Z_1. reflexivity. }
    unfold V10ReadLoop.model2.
    (* [comment removed for export] *)
    run_blk_keep (SCR [false; false] [] []) 44%nat;
      try (lazymatch goal with
           | |- sc_denot _ _ _ (SCReadBase (SA _ ?k) _ _ (EVar ?v)) =>
               cbn [sc_denot]; destruct (RB k ltac:(lia)) as [[bs [Hr Hv]] _]; exists bs; split; [exact Hr | rewrite Hv; cbn [edenot ev ENV V10Open.ENV]; symmetry; assumption]
           | |- sc_denot _ _ _ (SCFlat (SA _ ?k) _) => cbn [sc_denot]; exact (proj2 (RB k ltac:(lia)))
           end).
    { cbn [sc_denot branch_taken]. fold cfglen_x. cbn [edenot]. rewrite CFG. cbn [ev ENV V10Open.ENV]. rewrite P7, alu_add_Z.
      unfold bv_ltu. rewrite !u_small by (unfold L in *; lia). apply Z.ltb_ge. unfold L in *. lia. }
    { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite P7. unfold bv_ltu. rewrite !u_small by (unfold L in *; lia).
      cbn. apply (f_equal negb (y := true)). apply Z.ltb_lt. unfold L in *. lia. }
    cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    (* [comment removed for export] *)
    destruct h_itinK as (_ & PAYL & PAY & IK). apply pair_equal_spec in IK as [MIS MISS].
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
      apply (HTR A vm (map (edenot (ENV vals)) r_rvl) Rx Mx) end.
    - rewrite length_map. reflexivity.
    - unfold slotsR. rewrite !vals_ev_map by (cbn; lia). unfold r_rvl. rewrite PAYL, PAY. cbn [nth app].
      repeat split.
      + exact P0. + exact P1. + exact P2. + exact P5. + exact P6. + exact P7.
      + exact CFG.
      + cbn [edenot]. rewrite CFG. cbn [ev ENV V10Open.ENV]. rewrite P7, md_mul_Z, !alu_add_Z. f_equal. lia.
      + unfold b1s_x. cbn [edenot ev ENV V10Open.ENV]. rewrite P42. unfold ext_val, ext_Z, hdr_b1s. pose proof b1_rng.
        rewrite u_small by lia. rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z. rewrite Z.mod_small by lia. reflexivity.
      + cbn [edenot ev ENV V10Open.ENV]. exact P43.
      + cbn [edenot]. rewrite CFG. cbn [ev ENV V10Open.ENV]. rewrite P6. rewrite !alu_add_wZ. rewrite ?u_small by lia. f_equal. lia.
    - change (ENV (map (edenot (ENV vals)) r_rvl)) with (xenv (ENV vals) r_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HR with regs_ok _ ?sr _ =>
        p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) r_rvl idb _ (fun k => eq_refl) srb sr_R _ HR eq_refl eq_refl)) end.
      intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
    - change (ENV (map (edenot (ENV vals)) r_rvl)) with (xenv (ENV vals) r_rvl (blobs_ev (blobs0 a0s path))).
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (know_ok_xfer_entails RSEGS (ENV vals) r_rvl idb _ _ kn kn_R (fun k => eq_refl) HK) end.
      lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - exact HS.
    - exact HB.
    - exact HcapL.
    - exact HLc.
  Qed.

  (* [comment removed for export] *)
  Theorem header_cases : forall K,
    (forall j buf cap, at_trun K j buf cap) -> forall j buf cap, at_header (hdr_shape K) j buf cap.
  Proof.
    intros K HTR j buf cap. unfold hdr_shape.
    destruct (Z.ltb_spec L 6) as [H6|H6].
    - apply header_short. exact H6.
    - destruct (Z.ltb_spec L (6 + hdr_cfg)) as [Hc|Hc].
      + apply header_overrun; lia.
      + apply header_ok; [lia | apply HTR].
  Qed.
End Hdr.
End V10Hdr.

Module V10ReadPhase.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10Open.
Import V10Malloc65536.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10MallocLayout. Import V10Kit.V10Startup.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section ReadPhase.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let L : Z := Z.of_nat (length data).
  Let at_loop := at_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let at_header := at_header sp0 a0s path envv tid mem0 fs0 stdin0 lim data.
  Let at_full := at_full sp0 a0s path envv tid mem0 fs0 stdin0 lim data.

  Variable HDRK : TSet.      (* [comment removed for export] *)
  Hypothesis HDR : forall j buf cap, at_header HDRK j buf cap.

  Definition capj (j : nat) : Z := (65536 * 2 ^ Z.of_nat j)%Z.

  Fixpoint rshape (fuel j : nat) : TSet :=
    match fuel with
    | O => t_die msg_refused fs0
    | S f => if (L <? capj j)%Z then HDRK
             else if (2 ^ 26 <=? capj j)%Z then t_die msg_refused fs0
             else rshape f (S j)
    end.

  Lemma capj_S : forall j, capj (S j) = (2 * capj j)%Z.
  Proof. intros j. unfold capj. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.

  Lemma capj_10 : forall j n, (j + n = 10)%nat -> (capj j * 2 ^ Z.of_nat n = 2 ^ 26)%Z.
  Proof.
    intros j n H. unfold capj. change 65536%Z with (2 ^ 16)%Z. rewrite <- !Z.pow_add_r by lia.
    replace (16 + Z.of_nat j + Z.of_nat n)%Z with 26%Z by lia. reflexivity.
  Qed.

  Lemma loop_gen : forall n j, (j + n = 10)%nat -> forall buf len, at_loop (rshape (S n) j) j buf (capj j) len.
  Proof.
    induction n as [|n IH]; intros j Hjn buf len.
    - (* [comment removed for export] *)
      pose proof (capj_10 j 0 Hjn) as Hc. rewrite Z.pow_0_r, Z.mul_1_r in Hc.
      cbn [rshape]. rewrite Hc. destruct (Z.ltb_spec L (2 ^ 26)) as [Hlt|Hge].
      + apply (read_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data Hfile AL_glob AL_grant);
          [intros _; apply HDR | intros Hc2; exfalso; unfold L in Hlt; lia].
      + change (2 ^ 26 <=? 2 ^ 26)%Z with true. cbn.
        apply (read_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data Hfile AL_glob AL_grant);
          [intros Hc2; exfalso; unfold L in Hge; lia |].
        intros _. apply (full_refused sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_grant). lia.
    - (* [comment removed for export] *)
      assert (Hcap : (capj j < 2 ^ 26)%Z).
      { pose proof (capj_10 j (S n) Hjn) as Hc. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc by lia.
        pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). unfold capj in *. nia. }
      cbn [rshape]. fold (rshape (S n) (S j)).
      destruct (Z.ltb_spec L (capj j)) as [Hlt|Hge].
      + apply (read_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data Hfile AL_glob AL_grant);
          [intros _; apply HDR | intros Hc2; exfalso; unfold L in Hlt; lia].
      + replace (2 ^ 26 <=? capj j)%Z with false by (symmetry; apply Z.leb_gt; lia).
        apply (read_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data Hfile AL_glob AL_grant);
          [intros Hc2; exfalso; unfold L in Hge; lia |].
        intros _. apply (full_grow sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data
                          AL_segs AL_rom AL_malloc AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret AL_env); [exact Hcap|].
        intros nb. rewrite <- capj_S. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem read_phase :
    V10Malloc65536.at_buf sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (FdFile path (Z_to_bv 64 0)) (rshape 11 0).
  Proof.
    apply (read_k0_entry sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim Hvsp data).
    intros buf. change 65536%Z with (capj 0). apply (loop_gen 10 0). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem rshape_collapse : forall n j, (j + n = 10)%nat ->
    rshape (S n) j = (if (2 ^ 26 <=? L)%Z then t_die msg_refused fs0 else HDRK).
  Proof.
    induction n as [|n IH]; intros j Hjn.
    - pose proof (capj_10 j 0 Hjn) as Hc. rewrite Z.pow_0_r, Z.mul_1_r in Hc. cbn [rshape]. rewrite Hc.
      change (2 ^ 26 <=? 2 ^ 26)%Z with true.
      destruct (Z.ltb_spec L (2 ^ 26)) as [Hlt|Hge].
      + replace (2 ^ 26 <=? L)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + replace (2 ^ 26 <=? L)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - assert (Hcap : (capj j < 2 ^ 26)%Z).
      { pose proof (capj_10 j (S n) Hjn) as Hc. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc by lia.
        pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). unfold capj in *. nia. }
      cbn [rshape]. fold (rshape (S n) (S j)).
      destruct (Z.ltb_spec L (capj j)) as [Hlt|Hge].
      + replace (2 ^ 26 <=? L)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + replace (2 ^ 26 <=? capj j)%Z with false by (symmetry; apply Z.leb_gt; lia).
        apply IH. lia.
  Qed.
End ReadPhase.
End V10ReadPhase.


Module V10TRun.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Oom.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10Hdr_defs.
Import V10Hdr.
Import V10FuzzIface.
Import V10TRun_defs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FPSteps.
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX true.
Tactic Notation "run_blkP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSP scr NX true.

(* [comment removed for export] *)
Ltac close_exit_code HR HK P0 Hh Hlazy sp0 OFF WLO WP2 CODE :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) with (exit_code CODE) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V10Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V10Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V10Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev V10Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | right; unfold atexit_one; repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Lemma bytes_at_skipn : forall M (a : Z) (bs : list byte) (k : nat),
  bytes_at M a bs -> bytes_at M (a + Z.of_nat k)%Z (skipn k bs).
Proof.
  intros M a bs k HB i Hi. rewrite length_skipn in Hi.
  replace (a + Z.of_nat k + i)%Z with (a + (Z.of_nat k + i))%Z by lia. rewrite (HB (Z.of_nat k + i)%Z ltac:(lia)).
  rewrite nth_skipn. do 2 f_equal. lia.
Qed.

Section TRun.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let side := side sp0 mem0 lim.
  Let slotsR := slotsR sp0 a0s path envv tid data.
  Let at_trun := at_trun sp0 a0s path envv tid mem0 fs0 stdin0 lim data.

  Definition L : Z := Z.of_nat (length data).
  Definition cfg : Z := hdr_cfg data.
  Definition paylen : Z := (L - 6 - cfg)%Z.
  Definition payload : list byte := skipn (Z.to_nat (6 + cfg)) data.
  Definition calls : Z := (if cfg =? 0 then 1 else 1 + hdr_b2 data mod 4)%Z.
  Definition counting : bool := (128 <=? hdr_b1 data)%Z.

  (* [comment removed for export] *)
  Definition tr_shape (K : TSet) : TSet := K.

  (* [comment removed for export] *)
  Definition roomT (A : AS) (vm : VmMaps) (rem : Z) : Prop :=
    aroom A vm (fuzz_k FUZZ_CALLS rem) (fuzz_b FUZZ_BMAX rem).

  Definition slotsT (vals : list word) (buf aligned owned : word) (rem : Z) : Prop :=
    slotsR vals buf /\ vals_ev vals 13 = Z_to_bv 64 calls /\ vals_ev vals 14 = aligned /\ vals_ev vals 15 = owned
    /\ vals_ev vals 16 = Z_to_bv 64 rem.

  (* [comment removed for export] *)
  Definition sideW (A : AS) (vm : VmMaps) (M : word -> option byte) (buf : word) (cap : Z) : Prop :=
    ainv A M vm /\ live A buf = Some cap
    /\ vm_limit vm = lim /\ alloc_top vm = (bv_unsigned sp0 - 8388608)%Z /\ vm_init_sp vm = sp0
    /\ vm_reserved vm = segments_reserved RSEGS
    /\ env_ok sp0 mem0 M /\ (65536 <= cap)%Z.
  (* [comment removed for export] *)
  Definition sideT (A : AS) (vm : VmMaps) (M : word -> option byte) (buf : word) (cap : Z) (owned : word) : Prop :=
    sideW A vm M buf cap
    /\ ((0 < paylen)%Z -> live A owned = Some paylen)
    /\ (forall q, q <> buf -> ((0 < paylen)%Z -> q <> owned) -> live A q = None).

  Lemma side_W : forall A vm M buf cap j, side A vm M buf cap j -> sideW A vm M buf cap.
  Proof.
    intros A vm M buf cap j HS. pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & _).
    destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    split; [exact HI|]. split; [exact Hl|]. split; [exact Hvl|]. split; [exact Htop|]. split; [exact Hisp|]. split; [exact Hres|].
    split; [exact HE | exact Hc0].
  Qed.

  Lemma bufW_facts : forall A vm M buf cap, sideW A vm M buf cap ->
    (0x66000 <= bv_unsigned buf)%Z /\ (bv_unsigned buf + cap <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned buf mod 16 = 0)%Z
    /\ (forall x : word, (bv_unsigned buf <= bv_unsigned x < bv_unsigned buf + cap)%Z -> M x <> None /\ owned A x).
  Proof.
    intros A vm M buf cap (HI & Hl & _ & Htop & _ & _ & _ & Hcap).
    destruct (ai_live_hull A M vm buf cap HI Hl) as (Hc0 & Hal & Hend & Hbytes). pose proof (round16_ge cap) as Hr.
    split.
    { apply (live_big_lo sp0 Hvsp AL_grant A M vm buf cap HI Hl). lia. }
    split; [lia|]. split; [exact Hal|].
    intros x Hx. destruct (Hbytes (bv_unsigned x - bv_unsigned buf)%Z ltac:(lia)) as (Ho & Hs & _).
    unfold at_ in Ho, Hs. replace (bv_unsigned buf + (bv_unsigned x - bv_unsigned buf))%Z with (bv_unsigned x) in Ho, Hs by lia.
    rewrite Z_to_bv_bv_unsigned in Ho, Hs. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition copyP (M : word -> option byte) (aligned owned : word) : Prop :=
    ((0 < paylen)%Z -> aligned = owned /\ bytes_at M (bv_unsigned aligned) payload
                     /\ (0x1000 <= bv_unsigned aligned)%Z /\ (bv_unsigned aligned + paylen <= bv_unsigned sp0 - 8388608)%Z
                     /\ (bv_unsigned aligned mod 16 = 0)%Z)
    /\ (paylen = 0%Z -> owned = Z_to_bv 64 0 /\ aligned = Z_to_bv 64 A_EMPTY).

  (* [comment removed for export] *)
  Definition at_tl0 (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M aligned owned,
      frm_zero (@fp_csr fxp) ->
      length vals = 50%nat -> slotsT vals buf aligned owned calls ->
      regs_ok (ENV vals) sr_TL R -> know_ok RSEGS (ENV vals) M kn_TL ->
      sideT A vm M buf cap owned -> roomT A vm calls -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
      (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x15594) M (seg_rom RSEGS)) (model2 vm)) K.

  Lemma paylen_facts : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
  Proof.
    intros H1 H2. pose proof (cfg_rng sp0 data) as Hc. unfold paylen, payload, cfg, L in *. rewrite length_skipn. lia.
  Qed.

  Lemma calls_rng : (1 <= calls <= 4)%Z.
  Proof. unfold calls, cfg. pose proof (b2_rng sp0 data). destruct (hdr_cfg data =? 0)%Z; [lia|]. pose proof (Z.mod_pos_bound (hdr_b2 data) 4 ltac:(lia)). lia. Qed.

  Lemma calls_x_val : forall vals, vals_ev vals 11 = Z_to_bv 64 (hdr_b2 data) -> cfg <> 0%Z ->
    edenot (ENV vals) calls_x = Z_to_bv 64 calls.
  Proof.
    intros vals H11 Hc. destruct t_itin1 as (_ & _ & _ & _ & _ & _ & _ & _ & CX & _). rewrite CX.
    cbn [edenot ev ENV V10Open.ENV]. rewrite H11. pose proof (b2_rng sp0 data) as Hb.
    unfold ext_val, ext_Z. rewrite u_small by lia. rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z.
    rewrite Z.mod_small by lia. cbn [negb]. rewrite alu_and3_Z by lia. rewrite alu_add_Z. unfold calls.
    replace (cfg =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hc). f_equal. lia.
  Qed.

  Lemma ownedA_rangeT : forall A m vm a, ainv A m vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    owned A a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z
                 \/ ((0x66000 <= bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (0x1000 <= bv_unsigned a < 0x10000)%Z).
  Proof. exact (ownedA_range sp0 Hvsp AL_glob AL_grant). Qed.

  Lemma know_after_allocT : forall (A A' : AS) vals (M M' : word -> option byte) vm vm' R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    (forall a, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ owned A a \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_acallT kn).
  Proof.
    intros A A' vals M M' vm vm' R' kn HLv P0 Hlt HK HIA HtopA HI Htop Hfr Hgr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    unfold kn_acallT. apply (know_ok_call RSEGS (ENV (vals ++ junk_vals R')) M M' GLOB (-208 - 1024) (-208) IHI 0x34000).
    - cbn [ev ENV V10Open.ENV]. rewrite vals_ev_app_l by lia. rewrite P0. lia.
    - unfold IHI, WIN. lia.
    - unfold WIN. lia.
    - intros x Hnt. unfold touched in Hnt. cbn [ev ENV V10Open.ENV] in Hnt.
      rewrite vals_ev_app_l in Hnt by lia. rewrite P0 in Hnt.
      unfold IHI, WIN, GLOB in Hnt.
      apply Hfr.
      + intros Ho. destruct (ownedA_rangeT A M vm x HIA HtopA Ho) as [Hg|[Hh|Hl]].
        * apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [left; reflexivity | cbn; lia].
        * apply Hnt. right. left. lia.
        * apply Hnt. left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [right; right; left; reflexivity | cbn; lia].
      + intros Ho. destruct (ownedA_rangeT A' M' vm' x HI Htop Ho) as [Hg|[Hh|Hl]].
        * apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [left; reflexivity | cbn; lia].
        * apply Hnt. right. left. lia.
        * apply Hnt. left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [right; right; left; reflexivity | cbn; lia].
      + intros He. apply AL_errno in He. apply Hnt. left. split; [lia|]. exists (0x453dc, 0x453e0)%Z.
        split; [right; left; reflexivity | cbn; lia].
      + intros Hs. apply Hnt. right. right. unfold ALLOC_STACK in Hs. lia.
    - intros x Hx HM. cbn [ev ENV V10Open.ENV] in Hx. rewrite vals_ev_app_l in Hx by lia.
      rewrite P0 in Hx. unfold WIN in Hx. destruct (Hgr x HM) as [H|[H|H]]; [| | exact H].
      + pose proof AL_hi. exfalso. lia.
      + destruct (ownedA_rangeT A M vm x HIA HtopA H); exfalso; lia.
    - intros m a n H1 H2. apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2].
    - apply (env_app_know RSEGS vals (junk_vals R') _ M kn); [exact Hlt | exact HK].
  Qed.


  Lemma env_ok_allocT : forall A A' M M' vm vm',
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    ainv A' M' vm' -> alloc_top vm' = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
               ~ (bv_unsigned sp0 - 208 - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
  Proof.
    intros A A' M M' vm vm' (HEa & HEl & HEr) HIA HtopA HI Htop Hfr. pose proof SPlo.
    assert (FR : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z \/ (0x10000 <= bv_unsigned a < 0x65778)%Z ->
                 ~ (0x453dc <= bv_unsigned a < 0x453e0)%Z -> M' a = M a).
    { intros a Ha Hne. apply Hfr.
      - intros Ho. destruct (ownedA_rangeT A M vm a HIA HtopA Ho); lia.
      - intros Ho. destruct (ownedA_rangeT A' M' vm' a HI Htop Ho); lia.
      - intros He. apply AL_errno in He. lia.
      - unfold ALLOC_STACK. lia. }
    split; [|split].
    - intros a Ha. rewrite FR by lia. apply HEa. exact Ha.
    - intros a H1 H2. rewrite FR by lia. apply HEl; assumption.
    - intros a Ha. rewrite FR by lia. apply HEr. exact Ha.
  Qed.


  (* [comment removed for export] *)
  Lemma sgn_tab : forallb (fun b => Bool.eqb (bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0)) (128 <=? b)%Z) (zseq 256) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma sgn_val : forall b, (0 <= b < 256)%Z -> bv_lts (Z_to_bv 64 (bv_swrap 8 b)) (Z_to_bv 64 0) = (128 <=? b)%Z.
  Proof.
    intros b Hb. pose proof sgn_tab as T. rewrite forallb_forall in T.
    specialize (T b (proj2 (in_zseq 256 b) ltac:(cbn; lia))). apply Bool.eqb_prop in T. exact T.
  Qed.

  (* [comment removed for export] *)
  Lemma sideW_frame : forall A vm M M' buf cap,
    sideW A vm M buf cap ->
    (forall x : word, M' x <> M x -> V10ReadLoop.in_win sp0 x \/ in_data x \/ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z)) ->
    mem_grows M M' ->
    sideW A vm M' buf cap.
  Proof.
    intros A vm M M' buf cap HS Hchg Hgr. pose proof (bufW_facts A vm M buf cap HS) as (Hb0 & Hb1 & Hal & Hbb).
    destruct HS as (HI & Hl & Hvl & Htop & Hisp & Hres & (HEa & HEl & HEr) & Hc0). pose proof SPlo.
    assert (EQ : forall x : word, ~ V10ReadLoop.in_win sp0 x -> ~ in_data x ->
                 ~ (exists p n, live A p = Some n /\ (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z) -> M' x = M x).
    { intros x H1 H2 H3. destruct (M' x) as [b'|] eqn:E1; destruct (M x) as [b|] eqn:E2.
      - destruct (Z.eq_dec (bv_unsigned b') (bv_unsigned b)) as [Hb|Hb]; [f_equal; apply bv_eq; exact Hb|].
        exfalso. destruct (Hchg x ltac:(rewrite E1, E2; intros HH; injection HH as HH; apply Hb; rewrite HH; reflexivity)) as [?|[?|?]]; tauto.
      - exfalso. destruct (Hchg x ltac:(rewrite E1, E2; discriminate)) as [?|[?|?]]; tauto.
      - exfalso. destruct (Hchg x ltac:(rewrite E1, E2; discriminate)) as [?|[?|?]]; tauto.
      - reflexivity. }
    assert (LIVEB : forall p n x, live A p = Some n -> (bv_unsigned p <= bv_unsigned x < bv_unsigned p + n)%Z -> M x <> None /\ owned A x).
    { intros p n x Hp Hx. destruct (ai_live_hull A M vm p n HI Hp) as (Hn0 & _ & _ & Hbytes). pose proof (round16_ge n).
      destruct (Hbytes (bv_unsigned x - bv_unsigned p)%Z ltac:(lia)) as (Ho & Hs & _).
      unfold at_ in Ho, Hs. replace (bv_unsigned p + (bv_unsigned x - bv_unsigned p))%Z with (bv_unsigned x) in Ho, Hs by lia.
      rewrite Z_to_bv_bv_unsigned in Ho, Hs. split; assumption. }
    split; [|split; [exact Hl | split; [exact Hvl | split; [exact Htop | split; [exact Hisp | split; [exact Hres | split; [|exact Hc0]]]]]]].
    - apply (ai_frame A M M' vm HI).
      + intros a Ho Hnl. apply EQ.
        * intros Hw. unfold V10ReadLoop.in_win in Hw. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
        * intros Hd. unfold V10ReadLoop.in_data in Hd. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
        * intros (p & n & Hp & Hk). exact (Hnl p n Hp Hk).
      + intros a Ho HM. apply Hgr. exact HM.
      + intros a [Hg Hlt] HM'. pose proof (AL_grant a Hg) as Hg'. rewrite Htop in Hlt.
        destruct (M a) eqn:EM; [discriminate|]. exfalso.
        assert (NE : M' a <> M a) by (rewrite EM; exact HM').
        destruct (Hchg a NE) as [Hw|[Hd|(p & n & Hp & Hk)]]; [unfold V10ReadLoop.in_win in Hw; lia | unfold V10ReadLoop.in_data in Hd; lia |].
        exact (proj1 (LIVEB p n a Hp Hk) EM).
    - split; [|split].
      + intros a Ha. rewrite EQ; [apply HEa; exact Ha | unfold V10ReadLoop.in_win; lia | unfold V10ReadLoop.in_data; lia |].
        intros (p & n & Hp & Hk). destruct (ai_live_hull A M vm p n HI Hp) as (_ & _ & Hend & _). pose proof (round16_ge n). lia.
      + intros a H1 H2. rewrite EQ; [apply HEl; assumption | unfold V10ReadLoop.in_win; lia | unfold V10ReadLoop.in_data; lia |].
        intros (p & n & Hp & Hk). destruct (LIVEB p n a Hp Hk) as [_ Ho]. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
      + intros a Ha. rewrite EQ; [apply HEr; exact Ha | unfold V10ReadLoop.in_win; lia | unfold V10ReadLoop.in_data; lia |].
        intros (p & n & Hp & Hk). destruct (LIVEB p n a Hp Hk) as [_ Ho]. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
  Qed.

  Lemma sideW_block : forall A vm M buf cap E log,
    sideW A vm M buf cap -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideW A vm (mem_denot E M log) buf cap
    /\ forall x : word, ~ V10ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
  Proof.
    intros A vm M buf cap E log HS Hlog HE0. pose proof SPlo. pose proof SPhi.
    assert (OUT : forall x : word, ~ V10ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x).
    { intros x Hx1 Hx2. apply (mem_denot_out_wdl E M log 0 DATA_RS); [exact Hlog | rewrite HE0; lia | | rewrite HE0; unfold WIN; exact Hx1 |].
      - unfold DATA_RS, WIN. repeat constructor; cbn; lia.
      - unfold DATA_RS. unfold V10ReadLoop.in_data in Hx2. repeat constructor; cbn; lia. }
    split; [|exact OUT].
    apply (sideW_frame A vm M _ buf cap HS); [| apply mem_denot_grows].
    intros x Hne.
    destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 8388608)) as [H3|H3];
      [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0)) as [H4|H4]; [left; unfold V10ReadLoop.in_win; lia|]];
      (destruct (Z_lt_ge_dec (bv_unsigned x) 0x34000) as [H1|H1];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x453b0) as [H2|H2]; [right; left; unfold V10ReadLoop.in_data; lia|]]);
      (destruct (Z_lt_ge_dec (bv_unsigned x) 0x65b28) as [H5|H5];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x66000) as [H6|H6]; [right; left; unfold V10ReadLoop.in_data; lia|]]);
      (destruct (Z_lt_ge_dec (bv_unsigned x) 0x654c0) as [H7|H7];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x656e0) as [H8|H8]; [right; left; unfold V10ReadLoop.in_data; lia|]]);
      exfalso; apply Hne; apply OUT; unfold V10ReadLoop.in_win, V10ReadLoop.in_data; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma log_win_wdl : forall log, log_win_b 0 log = true -> log_wdl_b 0 DATA_RS log = true.
  Proof.
    intros log H. unfold log_win_b, log_wdl_b in *. rewrite forallb_forall in H |- *. intros e He. specialize (H e He).
    destruct e as [[b k] w v]. destruct b; try discriminate H. cbn [entry_win_b entry_wdl_b] in *. exact H.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition slotsM (vals : list word) (buf : word) : Prop := slotsR vals buf /\ vals_ev vals 13 = Z_to_bv 64 calls.

  Definition at_tm (K : TSet) (j : nat) (buf : word) (cap : Z) : Prop :=
    forall A vm vals R M,
      length vals = 46%nat -> slotsM vals buf ->
      regs_ok (ENV vals) sr_TM R -> know_ok RSEGS (ENV vals) M kn_T ->
      side A vm M buf cap j -> bytes_at M (bv_unsigned buf) data -> (L < cap)%Z -> (6 + cfg <= L)%Z -> (0 < paylen)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b348) M (seg_rom RSEGS)) (model2 vm)) K.

  Lemma tm_step : forall K j buf cap,
    at_tl0 K j buf cap -> at_tm K j buf cap.
  Proof.
    intros K j buf cap HTL A vm vals R M HL SL HR HK HS HB HcapL HLc Hpay.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13).
    pose proof (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS) as (Hc0 & Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    assert (Hcap26 : (cap <= 67108864)%Z).
    { rewrite Hcapj. pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 10 ltac:(lia) Hj10) as Hp. change (2 ^ 10)%Z with 1024%Z in Hp.
      change 67108864%Z with (65536 * 1024)%Z. apply Z.mul_le_mono_nonneg_l; lia. }
    destruct (paylen_facts HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    assert (PLdef : paylen = (L - 6 - cfg)%Z) by reflexivity. assert (Ldef : L = Z.of_nat (length data)) by reflexivity.
    unfold model2, V10ReadLoop.model2.
    assert (R10 : getr R 10 = Z_to_bv 64 paylen) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x15540) by (regv HR (1 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (EQcfg : mkst R (Z_to_bv 64 0x2b348) M (seg_rom RSEGS) = mkst R al_malloc_pc M al_rom) by (rewrite AL_malloc, AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None).
    destruct tm_itin as (I2 & R2s & VLKT & VLS2 & VLK2 & SR3 & KN3 & VLK3 & I3 & IX & S19).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (alloc_margin_le paylen) as HMG. pose proof calls_rng as Hcalls.
    pose proof (need_lo FUZZ_CALLS FUZZ_BMAX j cap HFC0 ltac:(clear -HFB0; lia) Hj10 ltac:(change (2 ^ 26)%Z with 67108864%Z; clear -Hcap26 Hc0; lia))
      as (HNK & HNB).
    eapply (ai_malloc_sure fx0 A M md R paylen (need_k FUZZ_CALLS j) (need_b FUZZ_BMAX j cap)
              (Z_to_bv 64 0x15540) sp0 [a0s; path] envv K HI).
    - constructor; reflexivity.
    - apply AL_env. exact HE.
    - exact R10.
    - clear -Hpl. lia.
    - change (m_vmmaps md) with vm. exact Hroom.
    - clear -HNK HFC0. lia.
    - clear -HNB HMG Hpl HFB0. lia.
    - unfold ROOM_NMAX. clear -Hpl. lia.
    - exact R1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, R2, u_small by lia. lia.
    - rewrite R2, u_small by lia. lia.
    - intros a Ha. rewrite R2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - (* [comment removed for export] *)
      intros A' m' vm' regs' res HI' Ha0 Hcs Hnz Hl0 Hl1 Hlq' Hnew Hfr Hlm Hgr Hvl' Htop' Hisp' Hres' Hroom'.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop', Hvl', Hisp', Hres'. rewrite Htop in Htop'.
      unfold md. rewrite with_vmmaps_C. clear md.
      pose proof (u64_range res) as Hrr. pose proof (u64_range buf) as Hbr0.
      assert (Hbr : buf <> res) by (intros Heq; rewrite <- Heq in Hl0; rewrite Hl in Hl0; discriminate Hl0).
      assert (Hlbuf' : live A' buf = Some cap) by (rewrite (Hlq' buf Hbr); exact Hl).
      assert (HE' : env_ok sp0 mem0 m').
      { apply (env_ok_allocT A A' M m' vm vm' HE HI Htop HI' Htop'). intros a H1 H2 H3 H4. apply Hfr; try assumption.
        rewrite R2, u_small by lia. unfold ALLOC_STACK in *. lia. }
      (* [comment removed for export] *)
      assert (HRT : roomT A' vm' calls).
      { unfold roomT.
        destruct (fuzz_le4 FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK4 & HB4).
        destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK0 & HB0).
        apply (aroom_mono A' vm' _ _ _ _ Hroom'); clear -HNK HNB HMG Hpl HK4 HB4 HK0 HB0; lia. }
      destruct (ai_live_hull A' m' vm' res paylen HI' Hl1) as (_ & Hres16 & Hend & HbytesN).
      pose proof (round16_ge paylen) as Hr2.
      assert (Hres31 : (0x1000 <= bv_unsigned res)%Z) by (apply (live_lo sp0 Hvsp AL_grant A' m' vm' res paylen HI' Hl1); lia).
      assert (HsomeN : forall x : word, (bv_unsigned res <= bv_unsigned x < bv_unsigned res + paylen)%Z -> m' x <> None).
      { intros x Hx. destruct (HbytesN (bv_unsigned x - bv_unsigned res)%Z ltac:(lia)) as (_ & Hs & _ & _).
        unfold at_ in Hs. replace (bv_unsigned res + (bv_unsigned x - bv_unsigned res))%Z with (bv_unsigned x) in Hs by lia.
        rewrite Z_to_bv_bv_unsigned in Hs. exact Hs. }
      assert (HB' : bytes_at m' (bv_unsigned buf) data).
      { intros i Hi. unfold L in *. rewrite <- (HB i Hi). pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq. }
      assert (HP' : bytes_at m' (bv_unsigned buf + 6 + cfg) payload).
      { unfold payload. replace (bv_unsigned buf + 6 + cfg)%Z with (bv_unsigned buf + Z.of_nat (Z.to_nat (6 + cfg)))%Z by lia.
        apply bytes_at_skipn. exact HB'. }
      pose proof (ai_live_disjoint A' m' vm' res paylen buf cap HI' Hl1 Hlbuf' ltac:(intros Heq; apply Hbr; symmetry; exact Heq)) as Hdisj.
      pose proof (round16_ge cap) as Hr1.
      (* [comment removed for export] *)
      set (vals2 := vals ++ junk_vals regs').
      assert (HL2 : length vals2 = 78%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (A56 : vals_ev vals2 56 = res).
      { subst vals2. replace 56%nat with (length vals + 10)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r.
        unfold junk_vals, vals_ev. rewrite (nth_map_seq_gen _ 32 0 10) by lia. cbn [Nat.add]. rewrite <- Ha0. reflexivity. }
      assert (SL2 : slotsM vals2 buf) by (subst vals2; destruct SL0 as [SLR S13]; split; [repeat split|]; rewrite vals_ev_app_l by (rewrite HL; lia); try assumption;
                                          destruct SLR as (Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12); assumption).
      destruct SL2 as ((Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) & Q13).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs) as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2. change (sr_after_call_j sr_TM KEPT_AL 46) with tm_srM in HR2. clear HR. rename HR2 into HR.
      destruct tn_itin as (_ & _ & _ & _ & KNT).
      assert (HK2 : know_ok RSEGS (ENV vals2) m' tm_knM).
      { unfold tm_knM. apply Forall_cons.
        - cbn [kentry_ok edenot ev ENV V10Open.ENV]. rewrite A56. lia.
        - subst vals2.
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            pose proof (know_after_allocT A A' vals M m' vm vm' regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLKT) HK HI Htop HI' Htop') as HK5 end.
          specialize (HK5 ltac:(intros a H1 H2 H3 H4; apply Hfr; try assumption; rewrite R2, u_small by lia; exact H4) Hgr).
          rewrite KNT in HK5. match goal with |- ?g => idtac g end. exact HK5. }
      clear HK. rename HK2 into HK. clearbody vals2. clear KW R10 R1 R4 R2.
      (* [comment removed for export] *)
      run_blk_keep scr0 78%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      assert (MC : mcH m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload).
      { assert (NW : (bv_unsigned buf + 6 + cfg + Z.of_nat (length payload) < 2 ^ 64)%Z) by (rewrite Hplen; lia).
        constructor; rewrite ?u_small by lia; try lia.
        - pose proof (u64_range buf). match goal with |- ?g => idtac g end. exact (bytes_at_rdn m' (bv_unsigned buf + 6 + cfg)%Z payload ltac:(lia) NW HP').
        - apply store_ok_of_all; [lia|]. intros x Hx. unfold wview.
          destruct (m' x) eqn:EM; [discriminate | exfalso; exact (HsomeN x ltac:(lia) EM)]. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (B1 : getr Rc 1 = Z_to_bv 64 0x15554) by (regv HR (1 : reg); reflexivity);
        assert (B10 : getr Rc 10 = res) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact A56);
        assert (B11 : getr Rc 11 = Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) by (regv HR (11 : reg); cbn [edenot ev ENV V10Open.ENV]; rewrite Q12; reflexivity);
        assert (B12 : getr Rc 12 = Z_to_bv 64 paylen) by (regv HR (12 : reg); cbn [edenot ev ENV V10Open.ENV]; rewrite Q9; reflexivity);
        destruct (ref_memcpy m' res (Z_to_bv 64 (bv_unsigned buf + 6 + cfg)) paylen payload (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x15554)
                    ltac:(apply ret_ok_even; reflexivity) B1 B10 B11 B12) as (Rm & Hms & Hkeep);
        clear B1 B10 B11 B12
      end.
      replace (Z_to_bv 64 205628) with (0x3233c : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
      set (M2 := wbytes m' res payload).
      assert (OUT2 : forall x : word, ~ (bv_unsigned res <= bv_unsigned x < bv_unsigned res + paylen)%Z -> M2 x = m' x).
      { intros x Hx. subst M2. apply wbytes_outside; lia. }
      assert (HW' : sideW A' vm' m' buf cap).
      { split; [exact HI'|]. split; [exact Hlbuf'|]. split; [rewrite Hvl'; exact Hvl|]. split; [exact Htop'|].
        split; [rewrite Hisp'; exact Hisp|]. split; [rewrite Hres'; exact Hres|]. split; [exact HE' | exact Hc0]. }
      assert (HW2 : sideW A' vm' M2 buf cap).
      { apply (sideW_frame A' vm' m' M2 buf cap HW'); [| apply wbytes_grows].
        intros a Ha. right; right. exists res, paylen. split; [exact Hl1|].
        destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res)); [exfalso; apply Ha; apply OUT2; lia|].
        destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned res + paylen)); [lia | exfalso; apply Ha; apply OUT2; lia]. }
      assert (HBres : bytes_at M2 (bv_unsigned res) payload).
      { intros i Hi. subst M2. rewrite wbytes_inside by (rewrite ?u_small by lia; lia). rewrite !u_small by lia. do 2 f_equal. lia. }
      assert (HB2 : bytes_at M2 (bv_unsigned buf) data).
      { intros i Hi. unfold L in *. rewrite OUT2 by (rewrite u_small by lia; lia). apply HB'. exact Hi. }
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm callee_kept ltac:(rewrite HL2; exact VLS2) HR Hkeep callee_kept_no0) as HR3 end.
      rewrite HL2 in HR3. lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
      clear HR Hkeep.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_ok_call RSEGS (ENV vals2) m' M2 [(0x1000, 0x10000)%Z] 0 0 IHI 0x34000) as KC;
        specialize (KC ltac:(cbn [ev ENV V10Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
        specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HK3; clear KC
      end.
      assert (OUT2t : forall x : word, ~ touched (ENV vals2) [(0x1000, 0x10000)%Z] 0 0 IHI (bv_unsigned x) -> M2 x = m' x).
      { intros x Hnt. apply OUT2. unfold touched, IHI, WIN in Hnt. cbn [ev ENV V10Open.ENV] in Hnt. rewrite Q0 in Hnt. intros Hx. apply Hnt.
        destruct (live_where sp0 Hvsp AL_grant A' m' vm' res paylen HI' Hl1 ltac:(lia) Htop') as [[W1 W2]|[W1 W2]].
        - left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [left; reflexivity | cbn; lia].
        - right. left. lia. }
      specialize (HK3 OUT2t
                      ltac:(intros x _ Hx; apply (wbytes_grows payload m' res); exact Hx)
                      ltac:(intros m a k H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
      lazymatch type of HK3 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK3 end. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) M2 _ ltac:(rewrite HL2; exact VLK3) HK3) as HK. clear HK3.
      rename HR3 into HR.
      set (vals3 := vals2 ++ junk_vals Rm) in *.
      assert (HL3 : length vals3 = 110%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (T0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q0).
      assert (T56 : vals_ev vals3 56 = res) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact A56).
      assert (SL3 : slotsM vals3 buf) by (subst vals3; split; [repeat split|]; rewrite vals_ev_app_l by (rewrite HL2; lia); assumption).
      clearbody vals3. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clearbody M2. clear MC HP' HB' HW' Q0 Q1 Q2 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13.
      destruct SL3 as ((Q0 & Q1 & Q2 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) & Q13).
      (* [comment removed for export] *)
      run_blk_keep scr0 110%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      apply pair_equal_spec in IX as [MIS MISS].
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (HTL fx0 A' vm' (map (edenot (ENV vals3)) tl_rvlm) Rx Mx res res fp_frm_zero_fx0) end.
      + rewrite length_map. reflexivity.
      + unfold slotsT, V10Hdr.slotsR. rewrite !vals_ev_map by (cbn; lia). cbn [nth tl_rvlm rvl18 app tl tm_sr3 edenot ev ENV V10Open.ENV].
        repeat split; assumption.
      + change (ENV (map (edenot (ENV vals3)) tl_rvlm)) with (xenv (ENV vals3) tl_rvlm (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ =>
          p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) tl_rvlm idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + change (ENV (map (edenot (ENV vals3)) tl_rvlm)) with (xenv (ENV vals3) tl_rvlm (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn =>
          apply (know_ok_xfer_entails RSEGS (ENV vals3) tl_rvlm idb _ _ kn kn_TL (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + split; [exact HW2|]. split; [intros _; exact Hl1|].
        intros q Hq Hqr. rewrite (Hlq' q (Hqr Hpay)). apply Hlq. exact Hq.
      + exact HRT.
      + split; [| intros H0; exfalso; lia]. intros _. split; [reflexivity|]. split; [exact HBres|]. split; [exact Hres31|]. split; [lia | exact Hres16].
      + exact HB2.
      + exact HcapL.
      + exact Hcap26.
      + exact HLc.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem trun_entry : forall K j buf cap, at_tl0 K j buf cap -> at_trun (tr_shape K) j buf cap.
  Proof.
    intros K j buf cap HTL A vm vals R M HL SL HR HK HS HB HcapL HLc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as (P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hlq & Hroom) & (Hvl & Htop & Hisp & Hres) & HE & Hcapj & Hj10).
    pose proof (bufW_facts A vm M buf cap (side_W A vm M buf cap j HS0)) as (Hb0 & Hb1 & Hal & Hbb).
    assert (Hcap26 : (cap <= 67108864)%Z).
    { rewrite Hcapj. pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 10 ltac:(lia) Hj10) as Hp. change (2 ^ 10)%Z with 1024%Z in Hp.
      change 67108864%Z with (65536 * 1024)%Z. apply Z.mul_le_mono_nonneg_l; lia. }
    destruct (paylen_facts HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    assert (PLdef : paylen = (L - 6 - cfg)%Z) by reflexivity. assert (Ldef : L = Z.of_nat (length data)) by reflexivity.
    destruct t_itin1 as (Ia & Ic & Ib & Id & XA & XC & XB & XD & CX & S19b & S19d).
    apply pair_equal_spec in XA as [MISa MISSa]. apply pair_equal_spec in XC as [MISc MISSc].
    apply pair_equal_spec in XB as [MISb MISSb]. apply pair_equal_spec in XD as [MISd MISSd].
    unfold model2, V10ReadLoop.model2. unfold tr_shape.
    assert (CZ : forall b, bv_eqb (Z_to_bv 64 cfg) (Z_to_bv 64 0) = b <-> (if b then cfg = 0 else cfg <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    assert (PZ : forall b, bv_eqb (Z_to_bv 64 paylen) (Z_to_bv 64 0) = b <-> (if b then paylen = 0 else paylen <> 0)%Z).
    { intros b. unfold bv_eqb. rewrite !u_small by lia. destruct b; [apply Z.eqb_eq | apply Z.eqb_neq]. }
    (* [comment removed for export] *)
    assert (GO_M : forall rvl Rx Mx, (0 < paylen)%Z ->
      length rvl = 46%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TM Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_T ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x2b348) Mx (seg_rom RSEGS)) (mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 HRx HKx HSx HBx.
      apply (tm_step K j buf cap HTL A vm (map (edenot (ENV vals)) rvl) Rx Mx); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite vals_ev_map by lia; rewrite ?Hid by lia; cbn [edenot ev ENV V10Open.ENV]; try assumption. }
    assert (GO_L : forall rvl Rx Mx, paylen = 0%Z ->
      length rvl = 50%nat ->
      (forall i, (i < 13)%nat -> nth i rvl (ELit 0) = EVar i) -> edenot (ENV vals) (nth 13 rvl (ELit 0)) = Z_to_bv 64 calls ->
      nth 14 rvl (ELit 0) = ELit A_EMPTY -> nth 15 rvl (ELit 0) = ELit 0 -> edenot (ENV vals) (nth 16 rvl (ELit 0)) = Z_to_bv 64 calls ->
      regs_ok (ENV (map (edenot (ENV vals)) rvl)) sr_TL Rx -> know_ok RSEGS (ENV (map (edenot (ENV vals)) rvl)) Mx kn_TL ->
      side A vm Mx buf cap j -> bytes_at Mx (bv_unsigned buf) data ->
      realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x15594) Mx (seg_rom RSEGS)) (mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None)) K).
    { intros rvl Rx Mx Hp Hlen Hid H13 H14 H15 H16 HRx HKx HSx HBx.
      apply (HTL fx0 A vm (map (edenot (ENV vals)) rvl) Rx Mx (Z_to_bv 64 A_EMPTY) (Z_to_bv 64 0) fp_frm_zero_fx0); try assumption.
      - rewrite length_map. exact Hlen.
      - split; [repeat split|]; rewrite ?vals_ev_map by lia; rewrite ?Hid by lia; rewrite ?H14, ?H15; cbn [edenot ev ENV V10Open.ENV]; try assumption; try reflexivity.
        repeat split; rewrite ?vals_ev_map by lia; rewrite ?H14, ?H15; try assumption; reflexivity.
      - split; [exact (side_W A vm Mx buf cap j HSx)|]. split; [intros Hc; exfalso; lia|]. intros q Hq _. apply Hlq. exact Hq.
      - (* [comment removed for export] *)
        unfold roomT. pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0. pose proof calls_rng as Hcalls.
        pose proof (need_lo FUZZ_CALLS FUZZ_BMAX j cap HFC0 ltac:(clear -HFB0; lia) Hj10
                      ltac:(change (2 ^ 26)%Z with 67108864%Z; pose proof (proj1 (buf_facts sp0 mem0 lim Hvsp data AL_grant A M vm buf cap j HS0)); lia)) as (HNK & HNB).
        destruct (fuzz_le4 FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK4 & HB4).
        destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX calls HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hcalls; lia)) as (HK0 & HB0).
        apply (aroom_mono A vm _ _ _ _ Hroom); clear -HNK HNB HK4 HB4 HK0 HB0; lia.
      - split; [intros Hc; exfalso; lia|]. intros _. split; reflexivity. }
    assert (P8' : vals_ev vals 8 = Z_to_bv 64 cfg) by exact P8.
    assert (P9' : vals_ev vals 9 = Z_to_bv 64 paylen) by exact P9.
    Ltac t1_sc P8' P9' :=
      cbn [sc_denot branch_taken edenot ev V10Open.ENV]; rewrite ?P8', ?P9'; unfold bv_eqb; rewrite !u_small by lia;
      lazymatch goal with
      | |- context [(paylen =? 0)%Z] => destruct (Z.eqb_spec paylen 0); cbn [negb]; first [reflexivity | exfalso; lia]
      | |- context [(cfg =? 0)%Z] => destruct (Z.eqb_spec cfg 0); cbn [negb]; first [reflexivity | exfalso; lia]
      end.
    (* [comment removed for export] *)
    destruct (Z.eq_dec paylen 0) as [Hp0|Hp0];
      (destruct (Z.eq_dec cfg 0) as [Hc0|Hc0]);
      [ run_blk_keep (SCR [true; false] [] []) 45%nat
      | run_blk_keep (SCR [false; true] [] []) 45%nat
      | run_blk_keep (SCR [true; true] [] []) 45%nat
      | run_blk_keep (SCR [false; false] [] []) 45%nat ];
      try (t1_sc P8' P9');
      (lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
         destruct (side_block_wdl sp0 tid mem0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap j E log HS0 ltac:(vm_compute; reflexivity) P0) as [HS1 OUT1] end);
      rewrite <- EQM in HS1, OUT1;
      (assert (HB1 : bytes_at M0 (bv_unsigned buf) data) by
        (intros i Hi; rewrite OUT1; [apply HB; exact Hi | unfold V10ReadLoop.in_win; rewrite u_small by lia; lia
                                                   | unfold V10ReadLoop.in_data; rewrite u_small by lia; lia]));
      clear EQM.
    - (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_L tl_rvld Rx Mx Hp0 eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tl_rvld rvl18 app edenot]; unfold calls; rewrite (proj2 (Z.eqb_eq cfg 0) Hc0); reflexivity
        | reflexivity | reflexivity
        | cbn [nth tl_rvld rvl18 app edenot]; unfold calls; rewrite (proj2 (Z.eqb_eq cfg 0) Hc0); reflexivity
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tl_rvld)) with (xenv (ENV vals) tl_rvld (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tl_rvld idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tl_rvld)) with (xenv (ENV vals) tl_rvld (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tl_rvld idb _ _ kn kn_TL (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_L tl_rvlb Rx Mx Hp0 eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tl_rvlb rvl18 app]; apply (calls_x_val vals P11 Hc0)
        | reflexivity | reflexivity
        | cbn [nth tl_rvlb rvl18 app]; apply (calls_x_val vals P11 Hc0)
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tl_rvlb)) with (xenv (ENV vals) tl_rvlb (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tl_rvlb idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tl_rvlb)) with (xenv (ENV vals) tl_rvlb (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tl_rvlb idb _ _ kn kn_TL (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_M tm_rvlc Rx Mx ltac:(lia) eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tm_rvlc rvl13 app edenot]; unfold calls; rewrite (proj2 (Z.eqb_eq cfg 0) Hc0); reflexivity
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tm_rvlc)) with (xenv (ENV vals) tm_rvlc (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tm_rvlc idb _ (fun k => eq_refl) srb sr_TM _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tm_rvlc)) with (xenv (ENV vals) tm_rvlc (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tm_rvlc idb _ _ kn kn_T (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
    - (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO_M tm_rvla Rx Mx ltac:(lia) eq_refl) end;
        [ intros i Hi; do 13 (destruct i as [|i]; [reflexivity|]); lia
        | cbn [nth tm_rvla rvl13 app]; apply (calls_x_val vals P11 Hc0)
        | | | exact HS1 | exact HB1 ].
      + change (ENV (map (edenot (ENV vals)) tm_rvla)) with (xenv (ENV vals) tm_rvla (blobs_ev (blobs0 a0s path))).
        lazymatch type of HR with regs_ok _ ?sr _ => p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals) tm_rvla idb _ (fun k => eq_refl) srb sr_TM _ HR eq_refl eq_refl)) end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end. destruct Hi.
      + change (ENV (map (edenot (ENV vals)) tm_rvla)) with (xenv (ENV vals) tm_rvla (blobs_ev (blobs0 a0s path))).
        lazymatch type of HK with know_ok _ _ _ ?kn => apply (know_ok_xfer_entails RSEGS (ENV vals) tm_rvla idb _ _ kn kn_T (fun k => eq_refl) HK) end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
  Qed.
End TRun.
End V10TRun.


Module V10TRunE.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibWritevG.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Oom.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10Hdr_defs.
Import V10Hdr.
Import V10FuzzIface.
Import V10TRun_defs.
Import V10TRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)












Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX true.
Tactic Notation "run_blkP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSP scr NX true.

(* [comment removed for export] *)
Ltac close_exit_code HR HK P0 Hh Hlazy sp0 OFF WLO WP2 CODE :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) with (exit_code CODE) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V10Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V10Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V10Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev V10Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | right; unfold atexit_one; repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Lemma bytes_at_skipn : forall M (a : Z) (bs : list byte) (k : nat),
  bytes_at M a bs -> bytes_at M (a + Z.of_nat k)%Z (skipn k bs).
Proof.
  intros M a bs k HB i Hi. rewrite length_skipn in Hi.
  replace (a + Z.of_nat k + i)%Z with (a + (Z.of_nat k + i))%Z by lia. rewrite (HB (Z.of_nat k + i)%Z ltac:(lia)).
  rewrite nth_skipn. do 2 f_equal. lia.
Qed.

Section TRunE.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.


  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let sideW := sideW sp0 mem0 lim.
  Let calls := calls data.

  (* [comment removed for export] *)
  Definition pendingP (M : word -> option byte) (k : nat) (w : word) : Prop :=
    rdn RSEGS M (Z_to_bv 64 0x65b50) (2 * k) = Some (zero_lines k) /\ bv_unsigned w = (0x65b50 + 2 * Z.of_nat k)%Z /\ (k <= 3)%nat.

  (* [comment removed for export] *)
  Lemma pendingP_frame : forall M M' k w,
    pendingP M k w -> (forall a : word, (0x65b50 <= bv_unsigned a < bv_unsigned w)%Z -> M' a = M a) -> pendingP M' k w.
  Proof.
    intros M M' k w (HB & Hw & Hk) HF. split; [| split; [exact Hw | exact Hk]].
    rewrite <- HB. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply HF. rewrite u_small by lia. lia.
  Qed.

  Lemma zero_lines_length : forall k, length (zero_lines k) = (2 * k)%nat.
  Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.

  (* [comment removed for export] *)
  Definition at_fn1 (k : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M w,
      length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 5 = tid -> vals_ev vals 6 = buf -> vals_ev vals 7 = w ->
      regs_ok (ENV vals) sr_FN1 R -> know_ok RSEGS (ENV vals) M kn_FN1 -> sideW A vm M buf cap -> pendingP M k w ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x15400) M (seg_rom RSEGS)) (model2 vm))
               (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs0)).

  Theorem fn1_tail : forall k buf cap, at_fn1 k buf cap.
  Proof.
    intros k buf cap fxp A vm vals R M w HL P0 P5 P6 P7 HR HK HS (HPb & HPw & Hk3).
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap HS) as (Hb0 & Hb1 & Hal & Hbb).
    destruct HS as (HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0).
    unfold model2, V10ReadLoop.model2.
    run_blk_keep scr0 40%nat. cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
    destruct fn1_itin as (_ & _ & VLK1 & KNF & _ & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (F10 : getr Rc 10 = buf) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact P6);
      assert (F1 : getr Rc 1 = Z_to_bv 64 0x15408) by (regv HR (1 : reg); reflexivity);
      assert (F4 : getr Rc 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity);
      assert (F2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 128))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
            rewrite P0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (EQcfg : mkst Rc (Z_to_bv 64 0x2b208) M (seg_rom RSEGS) = mkst Rc al_free_pc M al_rom)
        by (rewrite AL_free, AL_rom; reflexivity); rewrite EQcfg; clear EQcfg end.
    rewrite <- AL_segs.
    set (md := mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (ai_free fxp A M md Rc buf (Z_to_bv 64 0x15408) sp0 [a0s; path] envv _ HI) end.
    - constructor; reflexivity.
    - apply AL_env. exact HE.
    - exact F10.
    - right. exists cap. exact Hl.
    - exact F1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite F4. symmetry. exact AL_tp.
    - rewrite F2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 128)%Z with (bv_unsigned sp0 + (-8) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, F2, u_small by lia. lia.
    - rewrite F2, u_small by lia. lia.
    - intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - intros A'' m'' vm'' regs'' HI'' Hcs'' Hlbuf'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hvlb''.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      (* [comment removed for export] *)
      assert (HP'' : pendingP m'' k w).
      { apply (pendingP_frame M m'' k w (conj HPb (conj HPw Hk3))). intros a Ha. apply Hfr''.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm _ HI Htop Ho) as [Hg|Hg]; lia.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A'' m'' vm'' _ HI'' Htop'' Ho) as [Hg|Hg]; lia.
        - intros He. apply AL_errno in He. lia.
        - rewrite F2, !u_small by lia. unfold ALLOC_STACK. lia. }
      destruct HP'' as (HPb'' & _ & _).
      set (vals2 := vals ++ junk_vals regs'').
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs'' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs'') as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_after_allocG sp0 a0s path Hvsp data AL_glob AL_grant AL_errno AL_hi A A'' vals M m'' vm vm'' regs'' kn
                      ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK1) HK HI Htop HI'' Htop'') as HK2 end.
      specialize (HK2 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                      ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
      lazymatch type of HK2 with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HK2 end.
      fold vals2 in HK2. clear HK. rename HK2 into HK.
      assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q7 : vals_ev vals2 7 = w) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      run_blk_keep scr0 72%nat.
      (* [comment removed for export] *)
      assert (HPb3 : rdn RSEGS M0 (Z_to_bv 64 0x65b50) (2 * k) = Some (zero_lines k)).
      { rewrite <- HPb''. rewrite EQM. apply rdn_agree. intros j Hj. rewrite u_small by lia.
        lazymatch goal with |- mem_denot ?E _ ?log _ = _ =>
          rewrite (mem_denot_out_win E m'' log 0); [reflexivity | vm_compute; reflexivity | cbn [ev ENV V10Open.ENV]; rewrite Q0; lia
                                                  | cbn [ev ENV V10Open.ENV]; rewrite Q0, u_small by lia; unfold WIN; lia] end. }
      clear EQM.
      assert (Hh : m_halted (mkModelC V10Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = None) by reflexivity.
      assert (Hlazy : m_vm_lazy (mkModelC V10Open.fds0 vm'' stdin0 fs0 None (Some tid) None) = []) by reflexivity.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok ?segs ?E ?Mf ?kn =>
      lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
        apply (rz_conseq segs _ (t_emit (W 1 (zero_lines k)) (t_exit (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) (m_fs model))));
        [ | cbn [m_fs]; replace (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) with (exit_code 0) by (apply bv_eq; reflexivity); apply t_eq_refl ];
        apply ref_exit_Z;
        pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl) as Ktid;
        cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
        pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 7)) in exact i) _ HK eq_refl) as Kw;
        cbn [kentry_ok edenot ev V10Open.ENV] in Kw; rewrite Q7 in Kw;
        lazymatch type of HR with regs_ok _ _ ?Rc =>
        exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)), (Z_to_bv 64 0), (Z_to_bv 64 0);
        split; [|split; [exact Hh|split; [exact Hlazy|]]]
        end end end.
      + constructor.
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV V10Open.ENV].
          rewrite Q0. first [reflexivity | f_equal; lia].
        * regv HR (4 : reg). reflexivity.
        * regv HR (10 : reg). reflexivity.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia.
          lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
          pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
                        _ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end.
          unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite Q0 in Hst.
          replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + (-192))%Z by lia. exact Hst.
        * lit_u. cbn [ev ENV V10Open.ENV] in Ktid |- *. lia.
        * lit_u. cbn [ev ENV V10Open.ENV] in Ktid |- *. lia.
        * cbn [ev ENV V10Open.ENV] in Ktid |- *. lia.
        * lit_u. change (283776 - 168)%Z with 0x453d8%Z.
          krd HK 0x453d8%Z 4%nat Htc. rewrite Htc. cbn [ev ENV V10Open.ENV] in Ktid |- *.
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK. * krd_solve HK.
        * repeat split; krd_solve HK.
        * repeat split; krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * right; unfold atexit_one; repeat split; krd_solve HK.
      + destruct k as [|k'].
        * (* [comment removed for export] *)
          left. split; [reflexivity|]. exists (Z_to_bv 64 0x65b50), (Z_to_bv 64 0).
          cbn [Z.of_nat Z.mul Z.add] in HPw.
          assert (Hw : w = Z_to_bv 64 0x65b50) by (apply bv_eq; rewrite HPw; reflexivity).
          split; [krd_solve HK|]. split.
          { krd HK (0x35230 + 40)%Z 8%nat Hwp. rewrite Hwp. cbn [ev ENV V10Open.ENV]. rewrite Q7, Hw. reflexivity. }
          split; [krd_solve HK|]. split; krd_solve HK.
        * right. exists 0x65b50%Z, (bv_unsigned w).
          krd HK (0x35230 + 88)%Z 8%nat Hbufp. krd HK (0x35230 + 96)%Z 8%nat Hbsz.
          lazymatch type of Hbufp with _ = Some (word_to_le_bytes 8 ?bp) =>
          lazymatch type of Hbsz with _ = Some (word_to_le_bytes 8 ?bs) =>
            exists bp, bs, (Z_to_bv 64 0), (canary_w a_draw) end end.
          split; [| reflexivity].
          constructor.
          -- krd_solve HK.
          -- krd HK (0x35230 + 40)%Z 8%nat Hwp. rewrite Hwp. cbn [ev ENV V10Open.ENV]. rewrite Q7, Z_to_bv_bv_unsigned. reflexivity.
          -- krd_solve HK.
          -- krd_solve HK.
          -- exact Hbufp.
          -- exact Hbsz.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- lia.
          -- rewrite zero_lines_length. lia.
          -- rewrite zero_lines_length. lia.
          -- rewrite zero_lines_length. exact HPb3.
          -- split; [krd_solve HK|].
             lazymatch type of HK with know_ok ?segs ?E ?Mf ?kn =>
               pose proof (kblob_rdn segs E Mf kn (ELit 0) 0x656e8 (ELit 8) 2%nat HK ltac:(vm_compute; reflexivity)) as Hcan end.
             cbn [eb ENV V10Open.ENV blobs_ev blobs0 nth length] in Hcan. rewrite adenot_lit0 in Hcan by lia.
             rewrite guard_bytes_w in Hcan. cbn [length word_to_le_bytes] in Hcan. exact Hcan.
  Qed.
End TRunE.
End V10TRunE.


Module V10TRunL.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibWritevG.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Oom.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10Hdr_defs.
Import V10Hdr.
Import V10FuzzIface.
Import V10TRun_defs.
Import V10TRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FPSteps.
(* [comment removed for export] *)
(* [comment removed for export] *)













Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX true.
Tactic Notation "run_blkP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSP scr NX true.

(* [comment removed for export] *)
Ltac close_exit_code HR HK P0 Hh Hlazy sp0 OFF WLO WP2 CODE :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) with (exit_code CODE) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V10Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V10Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V10Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev V10Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | right; unfold atexit_one; repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Lemma bytes_at_skipn : forall M (a : Z) (bs : list byte) (k : nat),
  bytes_at M a bs -> bytes_at M (a + Z.of_nat k)%Z (skipn k bs).
Proof.
  intros M a bs k HB i Hi. rewrite length_skipn in Hi.
  replace (a + Z.of_nat k + i)%Z with (a + (Z.of_nat k + i))%Z by lia. rewrite (HB (Z.of_nat k + i)%Z ltac:(lia)).
  rewrite nth_skipn. do 2 f_equal. lia.
Qed.

Section TRunL.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.



  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let sideW := sideW sp0 mem0 lim.
  Let sideT := sideT sp0 mem0 lim data.
  Let copyP := copyP sp0 data.
  Let slotsT := slotsT sp0 a0s path envv tid data.
  Let L := L data.
  Let cfg := cfg data.
  Let paylen := paylen data.
  Let payload := payload data.
  Let calls := calls data.

  (* [comment removed for export] *)
  Definition slotsL (vals : list word) (buf aligned owned : word) (rem : Z) : Prop := slotsT vals buf aligned owned rem.

  Lemma kimg_clearL : forall E M kn lo hi,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
  Proof.
    intros E M kn lo hi HK Hex. apply existsb_exists in Hex as (K & Hin & Hc).
    destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hn).
    intros i Hi. apply Hn. lia.
  Qed.

  Lemma sideT_block : forall A vm M buf cap owned E log,
    sideT A vm M buf cap owned -> log_wdl_b 0 DATA_RS log = true -> ev E 0 = sp0 ->
    sideT A vm (mem_denot E M log) buf cap owned
    /\ forall x : word, ~ V10ReadLoop.in_win sp0 x -> ~ in_data x -> mem_denot E M log x = M x.
  Proof.
    intros A vm M buf cap owned E log (HW & Hlo & Hln) Hlog HE0.
    destruct (sideW_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A vm M buf cap E log HW Hlog HE0) as [HW' OUT].
    split; [| exact OUT]. split; [exact HW' | split; [exact Hlo | exact Hln]].
  Qed.

  (* [comment removed for export] *)
  Lemma know_after_fcall : forall (A : AS) vals (M M' : word -> option byte) vm R' kn,
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> kn_vars_lt (length vals) kn = true -> know_ok RSEGS (ENV vals) M kn ->
    ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    (forall a : word, M a <> None -> (bv_unsigned a < al_image_hi)%Z \/ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) \/ M' a <> None) ->
    know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_fcall kn).
  Proof.
    intros A vals M M' vm R' kn HLv P0 Hlt HK HI Htop Hfr Hgr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof AL_hi as Hih.
    unfold kn_fcall. apply (know_ok_call RSEGS (ENV (vals ++ junk_vals R')) M M' LGLOB (-208 - 16384) (-208) IHI 0x34000).
    - cbn [ev ENV V10Open.ENV]. rewrite vals_ev_app_l by lia. rewrite P0. lia.
    - unfold IHI, WIN. lia.
    - unfold WIN. lia.
    - intros x Hnt. unfold touched in Hnt. cbn [ev ENV V10Open.ENV] in Hnt.
      rewrite vals_ev_app_l in Hnt by lia. rewrite P0 in Hnt. unfold IHI, WIN, LGLOB, GLOB in Hnt.
      apply Hfr.
      + intros [Hg Hlt']. destruct (AL_grant x Hg) as [Hg1 Hg2]. rewrite Htop in Hlt'.
        destruct (Z_lt_ge_dec (bv_unsigned x) 0x10000) as [Hl|Hl].
        * apply Hnt. left. split; [lia|]. exists (0x1000, 0x10000)%Z. split; [right; right; right; left; reflexivity | cbn; lia].
        * apply Hnt. right. left. lia.
      + intros Hg. apply AL_glob in Hg. apply Hnt. left. split; [lia|]. exists (0x65778, 0x65b28)%Z. split; [right; left; reflexivity | cbn; lia].
      + intros He. apply AL_errno in He. apply Hnt. left. split; [lia|]. exists (0x453dc, 0x453e0)%Z.
        split; [right; right; left; reflexivity | cbn; lia].
      + intros Hh. unfold A_LEPT_HANDLER in Hh. apply Hnt. left. split; [lia|]. exists (0x34e08, 0x34e10)%Z. split; [left; reflexivity | cbn; lia].
      + intros Hs. apply Hnt. right. right. unfold LEPT_STACK in Hs. lia.
    - intros x Hx HM. cbn [ev ENV V10Open.ENV] in Hx. rewrite vals_ev_app_l in Hx by lia.
      rewrite P0 in Hx. unfold WIN in Hx. destruct (Hgr x HM) as [H|[[Hg Hlt']|H]]; [| | exact H].
      + exfalso. lia.
      + exfalso. rewrite Htop in Hlt'. lia.
    - intros m a n H1 H2. apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2].
    - apply (env_app_know RSEGS vals (junk_vals R') _ M kn); [exact Hlt | exact HK].
  Qed.

  Lemma env_ok_fcall : forall A M M' vm,
    env_ok sp0 mem0 M -> ainv A M vm -> alloc_top vm = (bv_unsigned sp0 - 8388608)%Z ->
    (forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> M' a = M a) ->
    env_ok sp0 mem0 M'.
  Proof.
    intros A M M' vm (HEa & HEl & HEr) HI Htop Hfr. pose proof SPlo.
    assert (FR : forall a : word,
              (bv_unsigned sp0 <= bv_unsigned a)%Z \/ (0x10000 <= bv_unsigned a < 0x34000)%Z \/ (0x453b0 <= bv_unsigned a < 0x65778)%Z ->
              ~ (0x453dc <= bv_unsigned a < 0x453e0)%Z -> M' a = M a).
    { intros a Ha Hne. apply Hfr.
      - intros [Hg Hlt]. destruct (AL_grant a Hg) as [Hg1 Hg2]. rewrite Htop in Hlt. lia.
      - intros Hg. apply AL_glob in Hg. lia.
      - intros He. apply AL_errno in He. lia.
      - unfold A_LEPT_HANDLER. lia.
      - unfold LEPT_STACK. lia. }
    split; [|split].
    - intros a Ha. rewrite FR by lia. apply HEa. exact Ha.
    - intros a H1 H2. rewrite FR by lia. apply HEl; assumption.
    - intros a Ha. rewrite FR by lia. apply HEr. exact Ha.
  Qed.

  Lemma paylen_factsL : (6 + cfg <= L)%Z -> (L < 2 ^ 26)%Z ->
    (0 <= paylen < 2 ^ 26)%Z /\ Z.of_nat (length payload) = paylen /\ (0 <= cfg < 32768)%Z.
  Proof. intros. apply (paylen_facts sp0 Hvsp data); assumption. Qed.

  (* [comment removed for export] *)
  Theorem fz_call : forall (fxp : FPState) (K : TSet) A vm vals R M buf cap aligned owned (rem : Z) kn,
    frm_zero (@fp_csr fxp) ->
    length vals = 50%nat -> slotsL vals buf aligned owned rem ->
    regs_ok (ENV vals) tl_sr1 R -> know_ok RSEGS (ENV vals) M kn -> kn_vars_lt 50 kn = true ->
    existsb (is_kimg_cov A_EMPTY 16) kn = true -> existsb (is_kimg_cov A_LEPT_SEV 8) kn = true ->
    existsb (is_kimg_cov A_LEPT_PMM 16) kn = true -> existsb (is_kimg_cov A_GOT_LO (A_GOT_HI - A_GOT_LO)) kn = true ->
    existsb (is_kimg_cov A_SELNAMES SELNAMES_LEN) kn = true ->
    existsb (is_kwr_cov (EVar 0) (-8388608) 8388608) kn = true ->
    sideT A vm M buf cap owned -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
    (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
    (* [comment removed for export] *)
    (1 <= rem)%Z -> roomT A vm rem ->
    (forall (fx' : FPState) A' vm' M' R',
        frm_zero (@fp_csr fx') ->
        regs_ok (ENV (vals ++ junk_vals R')) tl_sr2i R' -> know_ok RSEGS (ENV (vals ++ junk_vals R')) M' (kn_fcall kn) ->
        sideT A' vm' M' buf cap owned -> copyP M' aligned owned -> bytes_at M' (bv_unsigned buf) data ->
        (forall a : word, (0x65b28 <= bv_unsigned a < 0x66000)%Z -> M' a = M a) ->
        roomT A' vm' (rem - 1) ->
        realizes RSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x155a8) M' (seg_rom RSEGS)) (model2 vm')) K) ->
    realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x156ac) M (seg_rom RSEGS)) (model2 vm)) K.
  Proof.
    intros fxp K A vm vals R M buf cap aligned owned rem kn FRM HL SL HR HK VLK Xe Xs Xp Xg Xselnames Xw HS HC HB HcapL Hcap26 HLc Hrem1 HRT HKONT.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    pose proof HS as HS0. destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    destruct (paylen_factsL HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    destruct HC as [HC1 HC0].
    unfold model2, V10ReadLoop.model2.
    assert (R10 : getr R 10 = aligned) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact P14).
    assert (R11 : getr R 11 = Z_to_bv 64 paylen) by (regv HR (11 : reg); cbn [edenot ev ENV V10Open.ENV]; rewrite P9; reflexivity).
    assert (R1 : getr R 1 = Z_to_bv 64 0x155a8) by (regv HR (1 : reg); reflexivity).
    assert (R3 : getr R 3 = Z_to_bv 64 0x10800) by (regv HR (3 : reg); reflexivity).
    assert (R4 : getr R 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity).
    assert (R2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    (* [comment removed for export] *)
    assert (KW : forall (d : Z) (m : nat), (-8388608 <= d)%Z -> (d + Z.of_nat m <= -8388608 + 8388608)%Z ->
                 store_ok RSEGS M (adenot (ENV vals) (SA (EVar 0) d)) m = true).
    { apply existsb_exists in Xw as (Kw & Hin & Hc). apply In_nth_error in Hin as [iw Hiw].
      destruct Kw as [| | | | | |[bw kw] nw|]; try discriminate Hc.
      cbn [is_kwr_cov] in Hc. apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hb Hk].
      apply expr_eqb_eq in Hb. apply Z.leb_le in Hk. apply Z.leb_le in Hn. subst bw.
      intros d m Hd Hm. apply (kwr_store_ok RSEGS (ENV vals) M kn iw (EVar 0) kw nw d m HK Hiw); lia. }
    assert (EQcfg : @mkst fxp R (Z_to_bv 64 0x156ac) M (seg_rom RSEGS) = @mkst fxp R (Z_to_bv 64 PC_FUZZ) M al_rom) by (rewrite AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None).
    pose proof fuzz_calls_nonneg as HFC0. pose proof (fuzz_margin_bound 0 ltac:(lia)) as HFB0.
    pose proof (fuzz_margin_bound paylen Hpl) as HFM.
    destruct (fuzz_step FUZZ_CALLS FUZZ_BMAX rem) as (EK & EB).
    destruct (fuzz_nonneg FUZZ_CALLS FUZZ_BMAX (rem - 1) HFC0 ltac:(clear -HFB0; lia) ltac:(clear -Hrem1; lia)) as (HK0 & HB0).
    eapply (FZ fxp A M md R aligned paylen payload (Z_to_bv 64 0x155a8) sp0 [a0s; path] envv K HI).
    - constructor; reflexivity.
    - apply AL_env. exact HE.
    - exact R10.
    - exact R11.
    - symmetry. exact Hplen.
    - lia.
    - intros Hp. destruct (HC1 Hp) as (-> & _). apply Hlo'. exact Hp.
    - intros i Hi. destruct (Z_lt_ge_dec 0 paylen) as [Hp|Hp]; [| exfalso; lia].
      destruct (HC1 Hp) as (_ & HBp & _). apply HBp. unfold payload in Hplen. rewrite Hplen. exact Hi.
    - intros Hp0. destruct (HC0 Hp0) as [_ ->]. split; [reflexivity|].
      intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_EMPTY (A_EMPTY + 16) HK); [| exact Ha].
      replace (A_EMPTY + 16 - A_EMPTY)%Z with 16%Z by lia. exact Xe.
    - destruct (Z.eq_dec paylen 0) as [Hp0|Hp0].
      + destruct (HC0 Hp0) as [_ ->]. reflexivity.
      + destruct (HC1 ltac:(lia)) as (_ & _ & _ & _ & Hal16). exact Hal16.
    - exact R1.
    - apply ret_ok_even. reflexivity.
    - exact R3.
    - rewrite R4. symmetry. exact AL_tp.
    - rewrite R2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, R2, u_small by lia. unfold LEPT_STACK. lia.
    - rewrite R2, u_small by lia. lia.
    - unfold sp_window_hi. lia.
    - change (m_vmmaps md) with vm. unfold init_sp_win, sp_window_lo, sp_window_hi. rewrite Hisp. lia.
    - intros a Ha. rewrite R2, u_small in Ha by lia. unfold LEPT_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_LEPT_SEV (A_LEPT_SEV + 8) HK); [| exact Ha].
      replace (A_LEPT_SEV + 8 - A_LEPT_SEV)%Z with 8%Z by lia. exact Xs.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_LEPT_PMM (A_LEPT_PMM + 16) HK); [| exact Ha].
      replace (A_LEPT_PMM + 16 - A_LEPT_PMM)%Z with 16%Z by lia. exact Xp.
    - rewrite AL_segs. apply store_ok_data; unfold A_LEPT_HANDLER; rewrite u_small by lia; cbn; lia.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_GOT_LO A_GOT_HI HK); [exact Xg | exact Ha].
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
      apply (kimg_clearL (ENV vals) M kn A_SELNAMES (A_SELNAMES + SELNAMES_LEN) HK); [| exact Ha].
      replace (A_SELNAMES + SELNAMES_LEN - A_SELNAMES)%Z with SELNAMES_LEN by lia. exact Xselnames.
    - (* [comment removed for export] *) change (m_vmmaps md) with vm. exact HRT.
    - clear -EK HK0. lia.
    - clear -EB HB0 HFM. lia.
    - (* [comment removed for export] *)
      intros A' m' vm' regs' HI' Hlive' Ha0 Hcs Hfr Hlm Hgr Hvl' Htop' Hisp' Hres' Hroom'.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Hfr, Hgr, Hvl', Htop', Hisp', Hres'.
      pose proof Htop' as Htop''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      assert (Hfr2 : forall a : word, ~ (al_grantable a /\ (bv_unsigned a < alloc_top vm)%Z) -> ~ al_globals a -> ~ al_errno_slot a ->
                      ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8)%Z ->
                      ~ (bv_unsigned sp0 - 208 - LEPT_STACK <= bv_unsigned a < bv_unsigned sp0 - 208)%Z -> m' a = M a).
      { intros a H1 H2 H3 H4 H5. apply Hfr; try assumption. rewrite R2, u_small by lia. exact H5. }
      assert (IMGFR : forall a : word, (0x33000 <= bv_unsigned a < 0x66000)%Z -> ~ (0x65778 <= bv_unsigned a < 0x65b28)%Z ->
                       ~ (0x453dc <= bv_unsigned a < 0x453e0)%Z -> ~ (0x34e08 <= bv_unsigned a < 0x34e10)%Z -> m' a = M a).
      { intros a H1 H2 H3 H4. apply Hfr2.
        - intros [Hg Hlt]. destruct (AL_grant a Hg) as [Hg1 Hg2]. lia.
        - intros Hg. apply AL_glob in Hg. lia.
        - intros He. apply AL_errno in He. lia.
        - unfold A_LEPT_HANDLER. lia.
        - unfold LEPT_STACK. lia. }
      apply (HKONT fxp A' vm' m' regs' FRM).
      + (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (regs_after_allocG a0s path vals sr Rc regs' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs) as HR2 end.
        rewrite HL in HR2.
        pose proof (regs_ok_same10 _ _ regs' (ELit 0) HR2 ltac:(cbn [edenot]; exact Ha0)) as HR3.
        lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
        exact HR3.
      + (* [comment removed for export] *)
        apply (know_after_fcall A vals M m' vm regs' kn ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK) HK HI Htop Hfr2 Hgr).
      + (* [comment removed for export] *)
        split; [| split; [intros Hp; rewrite Hlive'; exact (Hlo' Hp) | intros q Hq Hq'; rewrite Hlive'; exact (Hln q Hq Hq')]].
        split; [exact HI'|]. split; [rewrite Hlive'; exact Hl|]. split; [rewrite Hvl'; exact Hvl|]. split; [exact Htop''|].
        split; [rewrite Hisp'; exact Hisp|]. split; [rewrite Hres'; exact Hres|]. split; [| exact Hc0].
        exact (env_ok_fcall A M m' vm HE HI Htop Hfr2).
      + (* [comment removed for export] *)
        split; [| exact HC0]. intros Hp. destruct (HC1 Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
        split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
        intros i Hi. rewrite <- (HBp i Hi). pose proof (Hlm aligned paylen i ltac:(rewrite Hao; apply Hlo'; exact Hp) ltac:(rewrite <- Hplen; exact Hi)) as Hq.
        unfold at_ in Hq. exact Hq.
      + (* [comment removed for export] *)
        intros i Hi. unfold V10TRun.L in *. rewrite <- (HB i Hi). pose proof (Hlm buf cap i Hl ltac:(lia)) as Hq. unfold at_ in Hq. exact Hq.
      + intros a Ha. apply IMGFR; lia.
      + (* [comment removed for export] *)
        unfold roomT. apply (aroom_mono A' vm' _ _ _ _ Hroom'); clear -EK EB HK0 HB0 HFM; lia.
  Qed.
End TRunL.
End V10TRunL.


Module V10TRunC.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibWritevG.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Oom.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10Hdr_defs.
Import V10Hdr.
Import V10FuzzIface.
Import V10TRun_defs.
Import V10TRun.
Import V10TRunE.
Import V10TRunL.
Import V10PrintfBufBase.
Import V10PrintfBuf.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FPSteps.
(* [comment removed for export] *)
(* [comment removed for export] *)













Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX true.
Tactic Notation "run_blkP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSP scr NX true.

(* [comment removed for export] *)
Ltac close_exit_code HR HK P0 Hh Hlazy sp0 OFF WLO WP2 CODE :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) with (exit_code CODE) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V10Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V10Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V10Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev V10Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | right; unfold atexit_one; repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Lemma bytes_at_skipn : forall M (a : Z) (bs : list byte) (k : nat),
  bytes_at M a bs -> bytes_at M (a + Z.of_nat k)%Z (skipn k bs).
Proof.
  intros M a bs k HB i Hi. rewrite length_skipn in Hi.
  replace (a + Z.of_nat k + i)%Z with (a + (Z.of_nat k + i))%Z by lia. rewrite (HB (Z.of_nat k + i)%Z ltac:(lia)).
  rewrite nth_skipn. do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma addiw_dec : forall r, (1 <= r <= 4)%Z ->
  (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 r)) (low32 (Z_to_bv 64 (-1)))) : word) = Z_to_bv 64 (r - 1).
Proof.
  intros r Hr. assert (C : (r = 1 \/ r = 2 \/ r = 3 \/ r = 4)%Z) by lia.
  destruct C as [-> |[-> |[-> | ->]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Section TRunC.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.




  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let sideW := sideW sp0 mem0 lim.
  Let sideT := sideT sp0 mem0 lim data.
  Let copyP := copyP sp0 data.
  Let slotsR := slotsR sp0 a0s path envv tid data.
  Let slotsL := slotsL sp0 a0s path envv tid data.
  Let pendingP := pendingP.
  Let L := L data.
  Let cfg := cfg data.
  Let paylen := paylen data.
  Let payload := payload data.
  Let calls := calls data.
  Let counting := counting data.
  Let at_fn1 := at_fn1 sp0 a0s path tid mem0 fs0 stdin0 lim.

  Lemma calls_rngC : (1 <= calls <= 4)%Z.
  Proof. exact (calls_rng sp0 data). Qed.

  (* [comment removed for export] *)
  Lemma pendingP_snoc : forall M M' k (w w' : word),
    pendingP M k w -> (forall a : word, (0x65b50 <= bv_unsigned a < bv_unsigned w)%Z -> M' a = M a) ->
    rdn RSEGS M' (Z_to_bv 64 (bv_unsigned w)) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a] ->
    bv_unsigned w' = (bv_unsigned w + 2)%Z -> (S k <= 3)%nat ->
    pendingP M' (S k) w'.
  Proof.
    intros M M' k w w' HP HF Hrd Hw' Hk'. pose proof (pendingP_frame sp0 Hvsp data M M' k w HP HF) as (HB & Hw & Hk).
    split; [| split; [rewrite Hw'; rewrite Hw; lia | exact Hk']].
    assert (APP : zero_lines (S k) = zero_lines k ++ [Z_to_bv 8 48; Z_to_bv 8 10]).
    { clear. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines app]. rewrite <- IH. reflexivity. }
    rewrite APP. replace (2 * S k)%nat with (2 * k + 2)%nat by lia.
    apply rdn_app; [exact HB|].
    replace (Z_to_bv 64 416592 + nat_to_word (2 * k) : word) with (Z_to_bv 64 (bv_unsigned w) : word); [exact Hrd|].
    unfold nat_to_word. rewrite bv_add_Zform, !u_small by lia. f_equal. rewrite Hw. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition slotsE (vals : list word) (buf aligned owned : word) : Prop :=
    slotsR vals buf /\ vals_ev vals 14 = aligned /\ vals_ev vals 15 = owned.

  Definition at_fe (k : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M aligned owned w,
      length vals = 50%nat -> slotsE vals buf aligned owned -> vals_ev vals 18 = w ->
      regs_ok (ENV vals) sr_FE R -> know_ok RSEGS (ENV vals) M kn_FE ->
      sideT A vm M buf cap owned -> copyP M aligned owned -> pendingP M k w -> (0 <= paylen)%Z -> (L < cap)%Z ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x2b208) M (seg_rom RSEGS)) (model2 vm))
               (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs0)).

  Theorem fe_tail : forall k buf cap, at_fe k buf cap.
  Proof.
    intros k buf cap fxp A vm vals R M aligned owned w HL SL P18 HR HK HS HC HP Hpl0 HcapL. pose proof (cfg_rng sp0 data) as Hcfr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P14 & P15).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
    destruct HS as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    destruct HC as [HC1 HC0].
    unfold model2, V10ReadLoop.model2.
    assert (F10 : getr R 10 = owned) by (regv HR (10 : reg); cbn [edenot ev ENV V10Open.ENV]; exact P15).
    assert (F1 : getr R 1 = Z_to_bv 64 0x155d4) by (regv HR (1 : reg); reflexivity).
    assert (F4 : getr R 4 = Z_to_bv 64 0x45480) by (regv HR (4 : reg); reflexivity).
    assert (F2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
          rewrite P0; first [reflexivity | f_equal; lia]).
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (EQcfg : mkst R (Z_to_bv 64 0x2b208) M (seg_rom RSEGS) = mkst R al_free_pc M al_rom) by (rewrite AL_free, AL_rom; reflexivity).
    rewrite EQcfg; clear EQcfg. rewrite <- AL_segs.
    set (md := mkModelC V10Open.fds0 vm stdin0 fs0 None (Some tid) None).
    eapply (ai_free fxp A M md R owned (Z_to_bv 64 0x155d4) sp0 [a0s; path] envv _ HI).
    - constructor; reflexivity.
    - apply AL_env. exact HE.
    - exact F10.
    - destruct (Z.eq_dec paylen 0) as [Hp0|Hp0].
      + left. exact (proj1 (HC0 Hp0)).
      + right. exists paylen. apply Hlo'. unfold paylen in *. lia.
    - exact F1.
    - apply AL_ret. apply ret_ok_even. reflexivity.
    - rewrite F4. symmetry. exact AL_tp.
    - rewrite F2. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
    - change (m_vmmaps md) with vm. rewrite Htop, F2, u_small by lia. lia.
    - rewrite F2, u_small by lia. lia.
    - intros a Ha. rewrite F2, u_small in Ha by lia. unfold ALLOC_STACK in Ha. repeat split.
      + pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst.
        pose proof (store_ok_all RSEGS M 1 a ltac:(pose proof (u64_range a); cbn; lia) Hst a ltac:(cbn; lia)) as Hw.
        rewrite (mlo_wview_out (ML := LU16)) in Hw by (cbn; lia). exact Hw.
      + intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm a HI Htop Ho); lia.
      + intros Hro. apply AL_ro in Hro. lia.
      + intros Hrw. apply AL_rw in Hrw. lia.
    - intros A'' m'' vm'' regs'' HI'' Hcs'' Hlo'' Hlq'' Hfr'' Hlm'' Hgr'' Hvl'' Htop'' Hisp'' Hres'' Hvlb''.
      rewrite AL_segs, AL_rom. change (m_vmmaps md) with vm in Htop'', Hvl'', Hisp'', Hres'', Hvlb''. rewrite Htop in Htop''.
      unfold md. rewrite with_vmmaps_C.
      assert (HE'' : env_ok sp0 mem0 m'').
      { apply (env_ok_allocT sp0 mem0 Hvsp AL_glob AL_grant AL_errno A A'' M m'' vm vm'' HE HI Htop HI'' Htop'').
        intros a H1 H2 H3 H4. apply Hfr''; try assumption. rewrite F2, u_small by lia. unfold ALLOC_STACK in *. lia. }
      assert (Hlbuf'' : live A'' buf = Some cap).
      { rewrite Hlq''; [exact Hl|]. intros Heq. destruct (Z.eq_dec paylen 0) as [Hp0|Hp0].
        - rewrite (proj1 (HC0 Hp0)) in Heq. rewrite Heq in Hb0. rewrite u_small in Hb0 by lia. lia.
        - pose proof (Hlo' ltac:(unfold paylen in *; lia)) as Hlo2. rewrite <- Heq in Hlo2. rewrite Hl in Hlo2.
          injection Hlo2 as Hlo2. unfold paylen, L, cfg, V10TRun.paylen, V10TRun.L, V10TRun.cfg in *. lia. }
      assert (HW'' : sideW A'' vm'' m'' buf cap).
      { split; [exact HI''|]. split; [exact Hlbuf''|]. split; [rewrite Hvl''; exact Hvl|]. split; [exact Htop''|].
        split; [rewrite Hisp''; exact Hisp|]. split; [rewrite Hres''; exact Hres|]. split; [exact HE'' | exact Hc0]. }
      assert (HP'' : pendingP m'' k w).
      { apply (pendingP_frame sp0 Hvsp data M m'' k w HP). destruct HP as (_ & Hw & Hk3). intros a Ha. apply Hfr''.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A M vm _ HI Htop Ho) as [Hg|Hg]; lia.
        - intros Ho. destruct (ownedA_rangeT sp0 Hvsp AL_glob AL_grant A'' m'' vm'' _ HI'' Htop'' Ho) as [Hg|Hg]; lia.
        - intros He. apply AL_errno in He. lia.
        - rewrite F2, !u_small by lia. unfold ALLOC_STACK. lia. }
      set (vals2 := vals ++ junk_vals regs'').
      assert (HL2 : length vals2 = 82%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (regs_after_allocG a0s path vals sr Rc regs'' ltac:(rewrite HL; vm_compute; reflexivity) HR Hcs'') as HR2 end.
      rewrite HL in HR2. fold vals2 in HR2.
      lazymatch type of HR2 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR2 end.
      clear HR. rename HR2 into HR.
      destruct fe_itin as (_ & _ & VLK & KNA & In_ & Ic & Xn & Xc & _).
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_after_allocT sp0 a0s path Hvsp AL_glob AL_grant AL_errno AL_hi A A'' vals M m'' vm vm'' regs'' kn
                      ltac:(rewrite HL; lia) P0 ltac:(rewrite HL; exact VLK) HK HI Htop HI'' Htop'') as HK2 end.
      specialize (HK2 ltac:(intros a H1 H2 H3 H4; apply Hfr''; try assumption; rewrite F2, u_small by lia; exact H4)
                      ltac:(intros a Ha; destruct (Hgr'' a Ha) as [Ho|Hs]; [right; left; exact Ho | right; right; exact Hs])).
      rewrite KNA in HK2. fold vals2 in HK2. clear HK. rename HK2 into HK.
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = buf) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      assert (Q10 : vals_ev vals2 10 = Z_to_bv 64 (hdr_b1s data)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P10).
      assert (Q18 : vals_ev vals2 18 = w) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P18).
      clearbody vals2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
      pose proof (b1_rng sp0 data) as Hb1r. pose proof (sgn_val sp0 (hdr_b1 data) Hb1r) as SGN.
      change (bv_swrap 8 (hdr_b1 data)) with (hdr_b1s data) in SGN.
      assert (GO : forall rvl Rx Mx,
        (forall HRx : regs_ok (ENV (map (edenot (ENV vals2)) rvl)) sr_FN1 Rx, forall HKx : know_ok RSEGS (ENV (map (edenot (ENV vals2)) rvl)) Mx kn_FN1,
          length rvl = 40%nat -> nth 0 rvl (ELit 0) = EVar 0 -> nth 5 rvl (ELit 0) = EVar 5 -> nth 6 rvl (ELit 0) = EVar 6 -> nth 7 rvl (ELit 0) = EVar 18 ->
          sideW A'' vm'' Mx buf cap -> pendingP Mx k w ->
          realizes RSEGS (mkCfg (mkst Rx (Z_to_bv 64 0x15400) Mx (seg_rom RSEGS)) (mkModelC V10Open.fds0 vm'' stdin0 fs0 None (Some tid) None))
                   (t_emit (W 1 (zero_lines k)) (t_exit (exit_code 0) fs0)))).
      { intros rvl Rx Mx HRx HKx Hlen E0 E5 E6 E7 HSx HPx.
        apply (fn1_tail sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data AL_segs AL_rom AL_free AL_tp AL_glob AL_grant
                 AL_errno AL_ro AL_rw AL_hi AL_ret AL_env k buf cap fxp A'' vm'' (map (edenot (ENV vals2)) rvl) Rx Mx w).
        - rewrite length_map. exact Hlen.
        - rewrite vals_ev_map by lia. rewrite E0. exact Q0.
        - rewrite vals_ev_map by lia. rewrite E5. exact Q5.
        - rewrite vals_ev_map by lia. rewrite E6. exact Q6.
        - rewrite vals_ev_map by lia. rewrite E7. exact Q18.
        - exact HRx. - exact HKx. - exact HSx. - exact HPx. }
      destruct counting eqn:Hcnt; unfold counting, V10TRun.counting in Hcnt; rewrite Hcnt in SGN.
      + (* [comment removed for export] *)
        run_blk_keep (SCR [true] [] []) 82%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite Q10. exact SGN. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideW_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A'' vm'' m'' buf cap E log HW'' ltac:(apply log_win_wdl; vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
        rewrite <- EQM in HS3, OUT3.
        assert (HP3 : pendingP M0 k w).
        { apply (pendingP_frame sp0 Hvsp data m'' M0 k w HP''). destruct HP'' as (_ & Hw & Hk3). intros a Ha. rewrite EQM.
          lazymatch goal with |- mem_denot ?E _ ?log _ = _ =>
            apply (mem_denot_out_win E m'' log 0); [vm_compute; reflexivity | cbn [ev ENV V10Open.ENV]; rewrite Q0; lia
                                                  | cbn [ev ENV V10Open.ENV]; rewrite Q0; unfold WIN; lia] end. }
        clear EQM OUT3.
        let rv := eval vm_compute in (fn1_rvl (EVar 18) (s_regs (fst (fst fe_r2c)))) in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO rv Rx Mx); try reflexivity; [| | exact HS3 | exact HP3] end.
        * lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) rvl idb _ (fun k => eq_refl) srb sr_FN1 _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals2) rvl idb _ _ kn kn_FN1 (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
      + (* [comment removed for export] *)
        run_blk_keep (SCR [false] [] []) 82%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite Q10. exact SGN. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideW_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A'' vm'' m'' buf cap E log HW'' ltac:(apply log_win_wdl; vm_compute; reflexivity) Q0) as [HS3 OUT3] end.
        rewrite <- EQM in HS3, OUT3.
        assert (HP3 : pendingP M0 k w).
        { apply (pendingP_frame sp0 Hvsp data m'' M0 k w HP''). destruct HP'' as (_ & Hw & Hk3). intros a Ha. rewrite EQM.
          lazymatch goal with |- mem_denot ?E _ ?log _ = _ =>
            apply (mem_denot_out_win E m'' log 0); [vm_compute; reflexivity | cbn [ev ENV V10Open.ENV]; rewrite Q0; lia
                                                  | cbn [ev ENV V10Open.ENV]; rewrite Q0; unfold WIN; lia] end. }
        clear EQM OUT3.
        let rv := eval vm_compute in (fn1_rvl (EVar 18) (s_regs (fst (fst fe_r2n)))) in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => apply (GO rv Rx Mx); try reflexivity; [| | exact HS3 | exact HP3] end.
        * lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals2) rvl idb _ (fun k => eq_refl) srb sr_FN1 _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
            change (ENV (map (edenot (ENV vals2)) rvl)) with (xenv (ENV vals2) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals2) rvl idb _ _ kn kn_FN1 (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end. constructor.
  Qed.
  Definition PFU : list (Z * Z) := [(0x35230, 0x35234); (0x35258, 0x35260); (0x65b50, 0x65f50)]%Z.

  Definition at_tl1 (rem k : nat) (buf : word) (cap : Z) : Prop :=
    forall (fxp : FPState) A vm vals R M aligned owned w,
      frm_zero (@fp_csr fxp) ->
      length vals = 50%nat -> slotsL vals buf aligned owned (Z.of_nat rem) -> vals_ev vals 18 = w ->
      regs_ok (ENV vals) sr_TL R -> know_ok RSEGS (ENV vals) M kn_TL1 ->
      sideT A vm M buf cap owned -> roomT A vm (Z.of_nat rem) -> copyP M aligned owned -> bytes_at M (bv_unsigned buf) data ->
      pendingP M k w -> (1 <= rem)%nat -> (rem + k <= 3)%nat ->
      (L < cap)%Z -> (cap <= 67108864)%Z -> (6 + cfg <= L)%Z ->
      realizes RSEGS (mkCfg (@mkst fxp R (Z_to_bv 64 0x15594) M (seg_rom RSEGS)) (model2 vm))
               (t_emit (W 1 (zero_lines (k + rem))) (t_exit (exit_code 0) fs0)).

  Theorem tl1_loop : forall rem k buf cap, at_tl1 rem k buf cap.
  Proof.
    induction rem as [|rem IH]; intros k buf cap fxp A vm vals R M aligned owned w FRM HL SL P18 HR HK HS HRT HC HB HP Hrem Hrk HcapL Hcap26 HLc; [lia|].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    destruct (paylen_facts sp0 Hvsp data HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcr).
    unfold model2, V10ReadLoop.model2.
    (* [comment removed for export] *)
    run_blk_keep scr0 50%nat.

    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap owned E log HS ltac:(vm_compute; reflexivity) P0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x45384%Z -> Mq x = M x).
    { intros x Hx. rewrite EQM. cbn [mem_denot]. apply MemSplit.wbytes_outside;
        rewrite length_N_to_le_bytes; unfold adenot, v_addi; cbn [a_base a_off edenot];
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    assert (HCb : copyP Mq aligned owned).
    { pose proof HS as ((HIq & _ & _ & Htopq & _) & Hloq & _).
      destruct HC as [HCa HCc]. split; [| exact HCc]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A M vm owned paylen HIq (Hloq Hp) Hp Htopq) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTb. rewrite u_small by lia. lia. }
    assert (HBb : bytes_at Mq (bv_unsigned buf) data).
    { pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
      intros i Hi. unfold V10TRun.L in *. rewrite <- (HB i Hi). apply OUTb. rewrite u_small by lia. lia. }
    assert (HPx : pendingP Mq k w) by (apply (pendingP_frame sp0 Hvsp data M Mq k w HP); intros a Ha; apply OUTb; lia).
    clear HP. rename HPx into HP.
    clear EQM OUTb HS HC HB. clear M. rename Mq into M. rename HSb into HS. rename HCb into HC. rename HBb into HB.
    destruct tl1_itin as (_ & _ & _ & VLK1 & VLS1 & KF & _ & S2 & VLS2 & VLK2 & I3l & I3e & KA3 & S3e & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) ?K =>
      apply (fz_call sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data AL_segs AL_rom AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
               AL_hi AL_env FZ fxp K A vm vals Rc M buf cap aligned owned (Z.of_nat (S rem)) tl1_kn1 FRM HL SL0 HR HK VLK1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (* [comment removed for export] *) ltac:(vm_compute; reflexivity) HS HC HB HcapL Hcap26 HLc ltac:(lia) HRT) end.
    clear HR HK. intros fx2 A' vm' M' R' FRM2 HR HK HS' HC' HB' HFR HRT'. clear FRM. clear fxp.
    assert (HP' : pendingP M' k w).
    { apply (pendingP_frame sp0 Hvsp data M M' k w HP). destruct HP as (_ & Hw & Hk3). intros a Ha. apply HFR. lia. }
    rewrite KF in HK. clear HS HC HB HP HFR M.
    set (vals2 := vals ++ junk_vals R') in *.
    assert (HL2 : length vals2 = 82%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q16 : vals_ev vals2 16 = Z_to_bv 64 (Z.of_nat (S rem))) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P16).
    assert (Q18 : vals_ev vals2 18 = w) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P18).
    assert (SL2 : slotsL vals2 buf aligned owned (Z.of_nat (S rem))).
    { subst vals2. split; [repeat split|]; rewrite ?vals_ev_app_l by (rewrite HL; lia); try assumption.
      all: repeat split; rewrite ?vals_ev_app_l by (rewrite HL; lia); assumption. }
    clearbody vals2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
    clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P18 SL0.
    destruct SL2 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    destruct HP' as (HPb & HPw & HPk).
    (* [comment removed for export] *)
    run_blk_keep scr0 82%nat.
    (* [comment removed for export] *)
    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M' buf cap owned E log HS' ltac:(vm_compute; reflexivity) Q0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x45384%Z -> Mq x = M' x).
    { intros x Hx. rewrite EQM. cbn [mem_denot]. apply MemSplit.wbytes_outside;
        rewrite length_N_to_le_bytes; unfold adenot, v_addi; cbn [a_base a_off edenot];
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    assert (HCb : copyP Mq aligned owned).
    { pose proof HS' as ((HIq & _ & _ & Htopq & _) & Hloq & _).
      destruct HC' as [HCa HCc]. split; [| exact HCc]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HIq (Hloq Hp) Hp Htopq) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTb. rewrite u_small by lia. lia. }
    assert (HBb : bytes_at Mq (bv_unsigned buf) data).
    { pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS')) as (Hb0 & Hb1 & Hal & Hbb).
      intros i Hi. unfold V10TRun.L in *. rewrite <- (HB' i Hi). apply OUTb. rewrite u_small by lia. lia. }
    assert (HPbb : rdn RSEGS Mq (Z_to_bv 64 0x65b50) (2 * k) = Some (zero_lines k)).
    { rewrite <- HPb. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply OUTb. rewrite u_small by lia. lia. }
    clear HPb. rename HPbb into HPb.
    clear EQM OUTb HS' HC' HB'. clear M'. rename Mq into M'. rename HSb into HS'. rename HCb into HC'. rename HBb into HB'.
    pose proof HS' as HS0. destruct HS' as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS0)) as (Hb0 & Hb1 & Hal & Hbb).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (G1 : getr Rc 1 = Z_to_bv 64 0x155b8) by (regv HR (1 : reg); reflexivity);
      assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11 : reg); reflexivity);
      assert (G2 : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp0 - 208))
        by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV V10Open.ENV];
            rewrite Q0; first [reflexivity | f_equal; lia])
    end.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (fun d m Hd Hm => kwr_store_ok RSEGS (ENV vals2) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                      _ _ _ d m HK eq_refl Hd Hm) as KW end.
    assert (PFH : pfH M' (Z_to_bv 64 (bv_unsigned sp0 - 208)) (bv_unsigned w) (bv_unsigned (canary_w a_draw))).
    { constructor.
      - rewrite u_small by lia. replace (bv_unsigned sp0 - 208)%Z with (bv_unsigned sp0 + (-13) * 16)%Z by lia. rewrite Z_mod_plus_full. exact SPal.
      - rewrite u_small by lia. lia.
      - rewrite u_small by lia. lia.
      - intros a n Ha1 Ha2. rewrite u_small in Ha1, Ha2 by lia. unfold PF_FR in Ha1.
        pose proof (KW (bv_unsigned a - bv_unsigned sp0)%Z n ltac:(lia) ltac:(lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV V10Open.ENV] in Hst. rewrite Q0 in Hst.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in Hst by lia.
        rewrite Z_to_bv_bv_unsigned in Hst. exact Hst.
      - lazymatch type of HK with know_ok _ _ _ ?kn =>
          exact (kimg_clearL sp0 Hvsp data (ENV vals2) M' kn 0x10000 0x34000 HK ltac:(vm_compute; reflexivity)) end.
      - krd_solve HK.
      - krd_solve HK.
      - krd HK 0x35258%Z 8%nat Hwp. rewrite Hwp. cbn [ev ENV V10Open.ENV]. rewrite Q18, Z_to_bv_bv_unsigned. reflexivity.
      - rewrite HPw. lia.
      - krd_solve HK.
      - krd_solve HK.
      - krd_solve HK.
      - lazymatch type of HK with know_ok ?segs ?E ?Mf ?kn =>
          pose proof (kblob_rdn segs E Mf kn (ELit 0) 0x656e8 (ELit 8) 2%nat HK ltac:(vm_compute; reflexivity)) as Hcan end.
        cbn [eb ENV V10Open.ENV blobs_ev blobs0 nth length] in Hcan. rewrite SymDriveX.adenot_lit0 in Hcan.
        rewrite guard_bytes_w in Hcan. cbn [length word_to_le_bytes] in Hcan. rewrite Z_to_bv_bv_unsigned. exact Hcan.
      - apply u64_range. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      destruct (printf0_buffered Rc M' (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (bv_unsigned w) (bv_unsigned (canary_w a_draw))
                  PFH G1 G2 G11) as (Rm & Mm & Hms & Hkeep & [Hagree Hgrows] & Hrd2 & Hwpos & Hflags) end.
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms PFH KW G1 G2 G11.
    (* [comment removed for export] *)
    assert (OUTP : forall x : word,
              ~ (bv_unsigned sp0 - 208 - 1056 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
              ~ (0x35230 <= bv_unsigned x < 0x35234)%Z -> ~ (0x35258 <= bv_unsigned x < 0x35260)%Z ->
              ~ (bv_unsigned w <= bv_unsigned x < bv_unsigned w + 2)%Z -> Mm x = M' x).
    { intros x H1 H2 H3 H4. apply Hagree. cbn [outside]. unfold in_rng.
      rewrite (u_small (bv_unsigned sp0 - 208)) by lia. rewrite !u_small by lia. repeat split; lia. }
    assert (HS2 : sideT A' vm' Mm buf cap owned).
    { split; [| split; [exact Hlo' | exact Hln]].
      apply (sideW_frame sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A' vm' M' Mm buf cap (proj1 HS0)); [| exact Hgrows].
      intros x Hne.
      destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 208 - 1056)) as [Y1|Y1];
        [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 208)) as [Y2|Y2]; [left; unfold V10ReadLoop.in_win; lia|]];
        (destruct (Z_lt_ge_dec (bv_unsigned x) 0x35230) as [Y3|Y3];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) 0x35260) as [Y4|Y4]; [right; left; unfold in_data; lia|]]);
        (destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned w)) as [Y5|Y5];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned w + 2)) as [Y6|Y6]; [right; left; unfold in_data; lia|]]);
        exfalso; apply Hne; apply OUTP; lia. }
    assert (HC2 : copyP Mm aligned owned).
    { destruct HC' as [HC1 HC0]. split; [| exact HC0]. intros Hp. destruct (HC1 Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTP; rewrite u_small by lia; lia. }
    assert (HB2 : bytes_at Mm (bv_unsigned buf) data).
    { intros i Hi. unfold V10TRun.L in *. rewrite <- (HB' i Hi). apply OUTP; rewrite u_small by lia; lia. }
    assert (HP2 : pendingP Mm (S k) (Z_to_bv 64 (bv_unsigned w + 2))).
    { apply (pendingP_snoc M' Mm k w _ (conj HPb (conj HPw HPk))); [| exact Hrd2 | rewrite u_small by lia; reflexivity | lia].
      intros a Ha. apply OUTP; lia. }
    clear HS0 HC' HB' HPb Hrd2.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path)) sr Rc Rm RefMemcpyLib.callee_saved ltac:(rewrite HL2; exact VLS2) HR Hkeep callee_saved_no0) as HR3 end.
    rewrite HL2 in HR3. lazymatch type of HR3 with regs_ok ?E ?sr ?Rx => let sr' := eval vm_compute in sr in change (regs_ok E sr' Rx) in HR3 end.
    clear HR Hkeep. rename HR3 into HR.
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (know_ok_call RSEGS (ENV vals2) M' Mm PFU (-208 - 1056) (-208) IHI 0x34000) as KC;
      specialize (KC ltac:(cbn [ev ENV V10Open.ENV]; rewrite Q0; lia) ltac:(unfold IHI, WIN; lia) ltac:(unfold WIN; lia));
      specialize (fun OUT WINNN SEGWR => KC OUT WINNN SEGWR kn HK) as HKc; clear KC
    end.
    specialize (HKc ltac:(intros x Hnt; apply OUTP; unfold touched, IHI, WIN, PFU in Hnt; cbn [ev ENV V10Open.ENV] in Hnt; rewrite Q0 in Hnt;
                            [ intros Hx; apply Hnt; right; right; lia
                            | intros Hx; apply Hnt; left; split; [lia|]; exists (0x35230, 0x35234)%Z; split; [left; reflexivity | cbn; lia]
                            | intros Hx; apply Hnt; left; split; [lia|]; exists (0x35258, 0x35260)%Z; split; [right; left; reflexivity | cbn; lia]
                            | intros Hx; apply Hnt; left; split; [lia|]; exists (0x65b50, 0x65f50)%Z; split; [right; right; left; reflexivity | cbn; lia] ])
                    ltac:(intros x _ Hx; apply Hgrows; exact Hx)
                    ltac:(intros m a n H1 H2; apply store_ok_data; [exact H1 | unfold IHI in H2; exact H2])).
    lazymatch type of HKc with know_ok ?sg ?E ?Mx ?kn => let kn' := eval vm_compute in kn in change (know_ok sg E Mx kn') in HKc end. clear HK.
    assert (HK : know_ok RSEGS (ENV vals2) Mm tl1_kn3i).
    { unfold know_ok, tl1_kn3i. apply Forall_cons; [| apply Forall_cons; [| exact HKc]].
      - apply (kword_intro RSEGS (ENV vals2) Mm (ELit 0) (Z_to_bv 64 0) 0x35258 8 _ (Z_to_bv 64 (bv_unsigned w + 2)));
          [reflexivity | cbn [edenot ev ENV V10Open.ENV]; rewrite Q18; rewrite alu_add_wZ; reflexivity | lia | lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; exact Hwpos].
      - apply (kword_intro RSEGS (ENV vals2) Mm (ELit 0) (Z_to_bv 64 0) 0x35230 4 _ (Z_to_bv 64 5));
          [reflexivity | reflexivity | lia | lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
          | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; exact Hflags]. }
    clear HKc.
    pose proof (env_app_know RSEGS vals2 (junk_vals Rm) (blobs_ev (blobs0 a0s path)) Mm tl1_kn3i ltac:(rewrite HL2; vm_compute; reflexivity) HK) as HK3.
    clear HK. rename HK3 into HK.
    set (vals3 := vals2 ++ junk_vals Rm) in *.
    assert (HL3 : length vals3 = 114%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
    assert (T0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q0).
    assert (T16 : vals_ev vals3 16 = Z_to_bv 64 (Z.of_nat (S rem))) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q16).
    assert (T18 : vals_ev vals3 18 = w) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q18).
    assert (SL3 : slotsL vals3 buf aligned owned (Z.of_nat (S rem))).
    { subst vals3. split; [repeat split|]; rewrite ?vals_ev_app_l by (rewrite HL2; lia); try assumption.
      all: repeat split; rewrite ?vals_ev_app_l by (rewrite HL2; lia); assumption. }
    clearbody vals3. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
    clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 Q0 Q16 Q18.
    destruct SL3 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    assert (ADD16 : (sext 64 (alu32 ALU_ADD (low32 (vals_ev vals3 16)) (low32 (Z_to_bv 64 (-1)))) : word) = Z_to_bv 64 (Z.of_nat rem)).
    { rewrite T16, addiw_dec by lia. f_equal. lia. }
    assert (W2 : (0x65b50 <= bv_unsigned w + 2 <= 0x65b50 + 6)%Z) by lia.
    (* [comment removed for export] *)
    destruct rem as [|rem'].
    - (* [comment removed for export] *)
      run_blk_keep (SCR [false] [] []) 114%nat.
      { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite ADD16. reflexivity. }
      cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      replace (k + 1)%nat with (S k) by lia.
      let rv := eval vm_compute in fe_rvlt in
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (fe_tail (S k) buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 (bv_unsigned w + 2))) end.
      + rewrite length_map. reflexivity.
      + unfold slotsE, V10Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V10Open.ENV]; assumption.
      + rewrite vals_ev_map by (cbn; lia). cbn [nth edenot ev ENV V10Open.ENV]. rewrite T18, alu_add_wZ. reflexivity.
      + lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_FE _ HR eq_refl eq_refl)) end end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[Hi|[]]]; [exfalso; lia|]. subst i. cbn [nth emap edenot ev ENV V10Open.ENV idb]. rewrite ADD16. reflexivity.
      + lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_FE (fun k => eq_refl) HK) end end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
        apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot ev ENV V10Open.ENV]. rewrite T18, alu_add_wZ, u_small by lia. lia.
      + exact HS2.
      + exact HC2.
      + exact HP2.
      + lia.
      + exact HcapL.
    - (* [comment removed for export] *)
      run_blk_keep (SCR [true] [] []) 114%nat.
      { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite ADD16. unfold bv_eqb. rewrite !u_small by lia.
        replace (Z.of_nat (S rem') =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      cbn [mem_denot] in EQM. lazymatch type of EQM with ?Mx = _ => subst Mx end.
      replace (k + S (S rem'))%nat with (S k + S rem')%nat by lia.
      let rv := eval vm_compute in tl1_rvl in
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
        apply (IH (S k) buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 (bv_unsigned w + 2)) FRM2) end.
      + rewrite length_map. reflexivity.
      + unfold slotsL, V10TRunL.slotsL, slotsT, V10Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V10Open.ENV];
          first [assumption | rewrite ADD16; reflexivity].
      + rewrite vals_ev_map by (cbn; lia). cbn [nth edenot ev ENV V10Open.ENV]. rewrite T18, alu_add_wZ. reflexivity.
      + lazymatch goal with |- regs_ok (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HR with regs_ok _ ?sr _ =>
            p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end end.
        intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
        destruct Hi as [Hi|[]]. exfalso; lia.
      + lazymatch goal with |- know_ok _ (ENV (map _ ?rvl)) _ _ =>
          change (ENV (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
          lazymatch type of HK with know_ok _ _ _ ?kn =>
            apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_TL1 (fun k => eq_refl) HK) end end.
        lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
        apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot ev ENV V10Open.ENV]. rewrite T18, alu_add_wZ, u_small by lia. lia.
      + exact HS2.
      + (* [comment removed for export] *)
        replace (Z.of_nat (S rem')) with (Z.of_nat (S (S rem')) - 1)%Z by lia. exact HRT'.
      + exact HC2.
      + exact HB2.
      + exact HP2.
      + lia.
      + lia.
      + exact HcapL.
      + exact Hcap26.
      + exact HLc.
  Qed.
End TRunC.
End V10TRunC.


Module V10TRunB.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowXfer.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.RefPrintfLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibWritevG.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Room.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10Oom.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10Hdr_defs.
Import V10Hdr.
Import V10FuzzIface.
Import V10TRun_defs.
Import V10TRun.
Import V10TRunE.
Import V10TRunL.
Import V10PrintfBufBase.
Import V10PrintfBuf.
Import V10TRunC.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FPSteps.
(* [comment removed for export] *)
(* [comment removed for export] *)













Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10StdioDefs. Import V10ExitR23.V10Exit. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds. Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPST scr NX true.
Tactic Notation "run_blkP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPSP scr NX true.

(* [comment removed for export] *)
Ltac close_exit_code HR HK P0 Hh Hlazy sp0 OFF WLO WP2 CODE :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 CODE) (Z_to_bv 64 255)) with (exit_code CODE) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev V10Open.ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x45480), (bv_unsigned (ev E 5)),
           WP2, (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev V10Open.ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); first [reflexivity | cbn [edenot ev V10Open.ENV]; assumption]
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev V10Open.ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; cbn [ev V10Open.ENV] in Ktid |- *; lia
      | cbn [ev V10Open.ENV] in Ktid |- *; lia
      | lit_u; change (283776 - 168)%Z with 0x453d8%Z;
        let Htc := fresh "Htc" in
        krd HK 0x453d8%Z 4%nat Htc; rewrite Htc; cbn [ev V10Open.ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | right; unfold atexit_one; repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Lemma bytes_at_skipn : forall M (a : Z) (bs : list byte) (k : nat),
  bytes_at M a bs -> bytes_at M (a + Z.of_nat k)%Z (skipn k bs).
Proof.
  intros M a bs k HB i Hi. rewrite length_skipn in Hi.
  replace (a + Z.of_nat k + i)%Z with (a + (Z.of_nat k + i))%Z by lia. rewrite (HB (Z.of_nat k + i)%Z ltac:(lia)).
  rewrite nth_skipn. do 2 f_equal. lia.
Qed.

Section TRunB.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  Hypothesis AL_thr : (al_mmap_threshold <= 131072)%Z.
  Hypothesis FZ : fuzz_call_contract.





  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let ENV := V10Open.ENV a0s path.
  Let model2 := model2 tid fs0 stdin0.
  Let sideW := sideW sp0 mem0 lim.
  Let sideT := sideT sp0 mem0 lim data.
  Let copyP := copyP sp0 data.
  Let slotsL := slotsL sp0 a0s path envv tid data.
  Let L := L data.
  Let cfg := cfg data.
  Let paylen := paylen data.
  Let payload := payload data.
  Let calls := calls data.
  Let at_tl0 := at_tl0 sp0 a0s path envv tid mem0 fs0 stdin0 lim data.

  (* [comment removed for export] *)
  Lemma kimg_rdn_n : forall E M kn (a : Z) (n : nat) bs,
    know_ok RSEGS E M kn -> existsb (is_kimg_cov a (Z.of_nat n)) kn = true ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
    rdn RSEGS M (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros E M kn a n bs HK Hex Himg Ha0 Ha1. apply existsb_exists in Hex as (K & Hin & Hc).
    destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hn).
    rewrite <- Himg. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply Hn. lia.
  Qed.

  Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1074a) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_lines_S : forall n, zero_lines (S n) = [Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines n.
  Proof. reflexivity. Qed.

  Theorem tl0_run : forall j buf cap,
    at_tl0 (t_emit (W 1 (zero_lines (Z.to_nat calls))) (t_exit (exit_code 0) fs0)) j buf cap.
  Proof.
    intros j buf cap fxp A vm vals R M aligned owned FRM HL SL HR HK HS HRT HC HB HcapL Hcap26 HLc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SL as SL0. pose proof (calls_rng sp0 data) as Hcr4. fold calls in Hcr4.
    destruct SL as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    destruct (paylen_facts sp0 Hvsp data HLc ltac:(unfold L in *; lia)) as (Hpl & Hplen & Hcfr).
    unfold model2, V10ReadLoop.model2.
    (* [comment removed for export] *)
    replace (Z.to_nat calls) with (S (Z.to_nat calls - 1)) by lia. set (n1 := (Z.to_nat calls - 1)%nat).
    rewrite zero_lines_S. unfold W. rewrite map_app.
    lazymatch goal with |- realizes _ ?c (t_emit (?a ++ ?b) ?X) =>
      apply (rz_conseq RSEGS _ (t_emit a (t_emit b X))); [| apply t_eq_sym; apply t_emit_app] end.
    (* [comment removed for export] *)
    run_blk_keep scr0 50%nat.

    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A vm M buf cap owned E log HS ltac:(vm_compute; reflexivity) P0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x45384%Z -> Mq x = M x).
    { intros x Hx. rewrite EQM. cbn [mem_denot]. apply MemSplit.wbytes_outside;
        rewrite length_N_to_le_bytes; unfold adenot, v_addi; cbn [a_base a_off edenot];
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    assert (HCb : copyP Mq aligned owned).
    { pose proof HS as ((HIq & _ & _ & Htopq & _) & Hloq & _).
      destruct HC as [HCa HCc]. split; [| exact HCc]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A M vm owned paylen HIq (Hloq Hp) Hp Htopq) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTb. rewrite u_small by lia. lia. }
    assert (HBb : bytes_at Mq (bv_unsigned buf) data).
    { pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A vm M buf cap (proj1 HS)) as (Hb0 & Hb1 & Hal & Hbb).
      intros i Hi. unfold V10TRun.L in *. rewrite <- (HB i Hi). apply OUTb. rewrite u_small by lia. lia. }
    clear EQM OUTb HS HC HB. clear M. rename Mq into M. rename HSb into HS. rename HCb into HC. rename HBb into HB.
    destruct tl_itin as (_ & _ & VLK1 & VLS1 & KF & _ & IP1 & SP1 & IP2 & SC & SCF & IP3l & IP3e & KA3 & SP3).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) ?K =>
      apply (fz_call sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp data AL_segs AL_rom AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
               AL_hi AL_env FZ fxp K A vm vals Rc M buf cap aligned owned calls tl_kn1 FRM HL SL0 HR HK VLK1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (* [comment removed for export] *) ltac:(vm_compute; reflexivity) HS HC HB HcapL Hcap26 HLc ltac:(clear -Hcr4; lia) HRT) end.
    clear HR HK. intros fx2 A' vm' M' R' FRM2 HR HK HS' HC' HB' HFR HRT'. clear FRM. clear fxp.
    rewrite KF in HK. clear HS HC HB HFR HRT.
    set (vals2 := vals ++ junk_vals R') in *.
    assert (HL2 : length vals2 = 82%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q16 : vals_ev vals2 16 = Z_to_bv 64 calls) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P16).
    assert (SL2 : slotsL vals2 buf aligned owned calls).
    { subst vals2. unfold slotsL, V10TRunL.slotsL, slotsT, V10Hdr.slotsR; repeat split; rewrite ?vals_ev_app_l by (rewrite HL; lia); assumption. }
    clearbody vals2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR, HK.
    clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 SL0.
    destruct SL2 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
    (* [comment removed for export] *)
    run_blk_keep scr0 82%nat.

    lazymatch type of EQM with ?Mn = mem_denot _ _ _ => rename Mn into Mq end.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M' buf cap owned E log HS' ltac:(vm_compute; reflexivity) Q0) as [HSb _] end.
    rewrite <- EQM in HSb.
    assert (OUTb : forall x : word, bv_unsigned x <> 0x45384%Z -> Mq x = M' x).
    { intros x Hx. rewrite EQM. cbn [mem_denot]. apply MemSplit.wbytes_outside;
        rewrite length_N_to_le_bytes; unfold adenot, v_addi; cbn [a_base a_off edenot];
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    assert (HCb : copyP Mq aligned owned).
    { pose proof HS' as ((HIq & _ & _ & Htopq & _) & Hloq & _).
      destruct HC' as [HCa HCc]. split; [| exact HCc]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HIq (Hloq Hp) Hp Htopq) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply OUTb. rewrite u_small by lia. lia. }
    assert (HBb : bytes_at Mq (bv_unsigned buf) data).
    { pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS')) as (Hb0 & Hb1 & Hal & Hbb).
      intros i Hi. unfold V10TRun.L in *. rewrite <- (HB' i Hi). apply OUTb. rewrite u_small by lia. lia. }
    clear EQM OUTb HS' HC' HB'. clear M'. rename Mq into M'. rename HSb into HS'. rename HCb into HC'. rename HBb into HB'.
    (* [comment removed for export] *)
    run_blkP_keep scr0 82%nat.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M' buf cap owned E log HS' ltac:(vm_compute; reflexivity) Q0) as [HS1 OUT1] end.
    rewrite <- EQM in HS1, OUT1.
    pose proof (bufW_facts sp0 mem0 lim Hvsp AL_grant A' vm' M' buf cap (proj1 HS')) as (Hb0 & Hb1 & Hal & Hbb).
    pose proof HS' as HS'0. destruct HS' as ((HI & Hl & Hvl & Htop & Hisp & Hres & HE & Hc0) & Hlo' & Hln).
    assert (HC1 : copyP M0 aligned owned).
    { destruct HC' as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
      apply OUT1; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    assert (HB1 : bytes_at M0 (bv_unsigned buf) data).
    { intros i Hi. unfold V10TRun.L in *. rewrite <- (HB' i Hi). apply OUT1; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    clear EQM OUT1 HC' HB' HS'0.
    (* [comment removed for export] *)
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x2d7a0) = Some ECALLW) by (vm_compute; reflexivity).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A17 : bv_unsigned (getr Rc 17) = 29%Z) by (regv HR (17 : reg); reflexivity);
      assert (A10 : getr Rc 10 = Z_to_bv 64 1) by (regv HR (10 : reg); reflexivity);
      assert (A11 : bv_unsigned (getr Rc 11) = 0x5413%Z) by (regv HR (11 : reg); reflexivity);
      apply (rz_ioctl_winsz_at RSEGS Rc _ _ (seg_rom RSEGS) _ ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)) _
               (model2_pure tid fs0 stdin0 vm') HF is_ecall_ECALLW A17 A10 ltac:(rewrite u_small by lia; lia) eq_refl eq_refl A11);
      clear A17 A10 A11 HF
    end.
    rewrite v_addi_pc4 by lia. change (0x2d7a0 + 4)%Z with 0x2d7a4%Z.
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_set_a0 E sr Rc (errno_ret ENOTTY) (ELit (2 ^ 64 - 25)) HR ltac:(apply bv_eq; vm_compute; reflexivity)) as HR2 end.
    clear HR. rename HR2 into HR.
    (* [comment removed for export] *)
    run_blkP_keep scr0 82%nat.
    lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
      destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M0 buf cap owned E log HS1 ltac:(vm_compute; reflexivity) Q0) as [HS2 OUT2] end.
    rewrite <- EQM in HS2, OUT2.
    assert (HC2 : copyP M1 aligned owned).
    { destruct HC1 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
      split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
      pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
      intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
      apply OUT2; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    assert (HB2 : bytes_at M1 (bv_unsigned buf) data).
    { intros i Hi. unfold V10TRun.L in *. rewrite <- (HB1 i Hi). apply OUT2; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
    clear EQM OUT2 HC1 HB1 HS1.
    (* [comment removed for export] *)
    assert (Hnl : rdn RSEGS M1 (Z_to_bv 64 0x1074a) 1 = Some [Z_to_bv 8 10]).
    { lazymatch type of HK with know_ok _ _ _ ?kn =>
        apply (kimg_rdn_n (ENV vals2) M1 kn 0x1074a 1 _ HK ltac:(vm_compute; reflexivity) nl_img); lia end. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?md) (t_emit _ ?K) =>
    apply (stdio_call_sound_fr vals2 (blobs_ev (blobs0 a0s path)) p_sr2 p_kn2 Rc Mc md p_sc [Z_to_bv 8 48] [Z_to_bv 8 10] K
             HR HK (eq_trans (f_equal (fun n => stdio_call n p_sr2 p_kn2) HL2) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn p_sc length Z.of_nat] end.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. reflexivity.
    - cbn. lia.
    - cbn. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V10Open.ENV]; rewrite ?Q0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV V10Open.ENV]; rewrite ?Q0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - cbn [edenot]. unorm. krd_solve HK.
    - cbn [edenot]. exact Hnl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply t_emit_has_nil.
    - clear HR HK. intros Rw M2 HR HK HPOST.
      destruct HPOST as [Pagree Pgrows _ _ _]. cbn [edenot ev ENV V10Open.ENV] in Pagree. rewrite Q0 in Pagree.
      rewrite alu_add_wZ, u_small in Pagree by lia.
      assert (HS3 : sideT A' vm' M2 buf cap owned).
      { destruct HS2 as (HW2 & HSl & HSn). split; [| split; [exact HSl | exact HSn]].
        apply (sideW_frame sp0 tid mem0 fs0 stdin0 lim Hvsp Htid AL_glob AL_grant A' vm' M1 M2 buf cap HW2); [| exact Pgrows].
        intros x Hne.
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 1296 - 112)) as [Y1|Y1];
          [| destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp0 - 1296)) as [Y2|Y2]; [left; unfold V10ReadLoop.in_win; lia|]];
          (destruct (Z_lt_ge_dec (bv_unsigned x) (0x35230 + 32)) as [Y3|Y3];
            [| destruct (Z_lt_ge_dec (bv_unsigned x) (0x35230 + 64)) as [Y4|Y4]; [right; left; unfold in_data; lia|]]);
          exfalso; apply Hne; apply Pagree; lia. }
      assert (HC3 : copyP M2 aligned owned).
      { destruct HC2 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
        split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
        pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
        intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi. apply Pagree; rewrite u_small by lia; lia. }
      assert (HB3 : bytes_at M2 (bv_unsigned buf) data).
      { intros i Hi. unfold V10TRun.L in *. rewrite <- (HB2 i Hi). apply Pagree; rewrite u_small by lia; lia. }
      clear HS2 HC2 HB2 Pagree Pgrows Hnl M0 M1.
      set (vals3 := vals2 ++ junk_vals Rw) in *.
      assert (HL3 : length vals3 = 114%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (T0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q0).
      assert (T16 : vals_ev vals3 16 = Z_to_bv 64 calls) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Q16).
      assert (SL3 : slotsL vals3 buf aligned owned calls).
      { subst vals3. unfold slotsL, V10TRunL.slotsL, slotsT, V10Hdr.slotsR; repeat split; rewrite ?vals_ev_app_l by (rewrite HL2; lia); assumption. }
      clearbody vals3. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path))) with (ENV vals3) in HR, HK.
      clear P0 P1 P2 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 Q0 Q16.
      destruct SL3 as ((P0 & P1 & P2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) & P13 & P14 & P15 & P16).
      assert (ADD16 : (sext 64 (alu32 ALU_ADD (low32 (vals_ev vals3 16)) (low32 (Z_to_bv 64 (-1)))) : word) = Z_to_bv 64 (calls - 1)).
      { rewrite T16, addiw_dec by lia. reflexivity. }
      (* [comment removed for export] *)
      destruct (Z.eq_dec calls 1) as [Hc1|Hc1].
      + (* [comment removed for export] *)
        run_blkP_keep (SCR [false] [] []) 114%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite ADD16, Hc1. reflexivity. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M2 buf cap owned E log HS3 ltac:(vm_compute; reflexivity) T0) as [HS4 OUT4] end.
        rewrite <- EQM in HS4, OUT4.
        assert (HC4 : copyP M0 aligned owned).
        { destruct HC3 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
          split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
          pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
          intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
          apply OUT4; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
        clear EQM OUT4.
        subst n1. rewrite Hc1. change (Z.to_nat 1 - 1)%nat with 0%nat.
        let rv := eval vm_compute in fe_rvlp in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (fe_tail sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
                   AL_hi AL_ret AL_env 0%nat buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 0x65b50)) end.
        * rewrite length_map. reflexivity.
        * unfold slotsE, V10Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V10Open.ENV]; assumption.
        * rewrite vals_ev_map by (cbn; lia). reflexivity.
        * lazymatch goal with |- regs_ok (_ (map _ ?rvl)) _ _ =>
            change (V10Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_FE _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[Hi|[]]]; [exfalso; lia|]. subst i. cbn [nth emap edenot ev ENV V10Open.ENV idb]. rewrite ADD16, Hc1. reflexivity.
        * lazymatch goal with |- know_ok _ (_ (map _ ?rvl)) _ _ =>
            change (V10Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_FE (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot]. unorm. lia.
        * exact HS4.
        * exact HC4.
        * split; [reflexivity | split; [unorm; reflexivity | lia]].
        * lia.
        * exact HcapL.
      + (* [comment removed for export] *)
        run_blkP_keep (SCR [true] [] []) 114%nat.
        { cbn [sc_denot branch_taken edenot ev ENV V10Open.ENV]. rewrite ADD16. unfold bv_eqb. rewrite !u_small by lia.
          replace (calls - 1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        lazymatch type of EQM with _ = mem_denot ?E _ ?log =>
          destruct (sideT_block sp0 tid mem0 fs0 stdin0 lim Hvsp Htid data AL_glob AL_grant A' vm' M2 buf cap owned E log HS3 ltac:(vm_compute; reflexivity) T0) as [HS4 OUT4] end.
        rewrite <- EQM in HS4, OUT4.
        assert (HC4 : copyP M0 aligned owned).
        { destruct HC3 as [HCa HCb]. split; [| exact HCb]. intros Hp. destruct (HCa Hp) as (Hao & HBp & Hx1 & Hx2 & Hx3).
          split; [exact Hao|]. split; [| split; [exact Hx1 | split; [exact Hx2 | exact Hx3]]].
          pose proof (live_where sp0 Hvsp AL_grant A' M' vm' owned paylen HI (Hlo' Hp) Hp Htop) as HW. rewrite <- Hao in HW.
          intros i Hi. rewrite <- (HBp i Hi). rewrite Hplen in Hi.
          apply OUT4; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
        assert (HB4 : bytes_at M0 (bv_unsigned buf) data).
        { intros i Hi. unfold V10TRun.L in *. rewrite <- (HB3 i Hi). apply OUT4; [unfold V10ReadLoop.in_win | unfold in_data]; rewrite u_small by lia; lia. }
        clear EQM OUT4.
        replace n1 with (0 + n1)%nat by lia.
        let rv := eval vm_compute in tl1_rvl0 in
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ =>
          apply (tl1_loop sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw
                   AL_hi AL_ret AL_env FZ n1 0%nat buf cap fx2 A' vm' (map (edenot (ENV vals3)) rv) Rx Mx aligned owned (Z_to_bv 64 0x65b50) FRM2) end.
        * rewrite length_map. reflexivity.
        * unfold V10TRunL.slotsL, slotsT, V10Hdr.slotsR; repeat split; rewrite vals_ev_map by (cbn; lia); cbn [nth edenot ev ENV V10Open.ENV];
            first [assumption | rewrite ADD16; f_equal; lia].
        * rewrite vals_ev_map by (cbn; lia). reflexivity.
        * lazymatch goal with |- regs_ok (_ (map _ ?rvl)) _ _ =>
            change (V10Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HR with regs_ok _ ?sr _ =>
              p6_sr_body sr ltac:(fun srb => apply (regs_ok_xfer (ENV vals3) rvl idb _ (fun k => eq_refl) srb sr_TL _ HR eq_refl eq_refl)) end end.
          intros i Hi Hne. lazymatch type of Hi with In i ?t => let t' := eval vm_compute in t in change (In i t') in Hi end.
          destruct Hi as [Hi|[]]. exfalso; lia.
        * lazymatch goal with |- know_ok _ (_ (map _ ?rvl)) _ _ =>
            change (V10Open.ENV a0s path (map (edenot (ENV vals3)) rvl)) with (xenv (ENV vals3) rvl (blobs_ev (blobs0 a0s path)));
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              apply (know_ok_xfer_entails RSEGS (ENV vals3) rvl idb _ _ kn kn_TL1 (fun k => eq_refl) HK) end end.
          lazymatch goal with |- Forall ?P ?t => let t' := eval vm_compute in t in change (Forall P t') end.
          apply Forall_cons; [| constructor]. apply krange_intro. cbn [edenot]. unorm. lia.
        * exact HS4.
        * (* [comment removed for export] *)
          replace (Z.of_nat n1) with (calls - 1)%Z by (subst n1; clear -Hcr4; lia). exact HRT'.
        * exact HC4.
        * exact HB4.
        * split; [reflexivity | split; [unorm; reflexivity | lia]].
        * lia.
        * lia.
        * exact HcapL.
        * exact Hcap26.
        * exact HLc.
  Qed.
End TRunB.
End V10TRunB.

Module V10MainFile.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveH4.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibTail.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymCall.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeLaws.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.FileSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.LibWritev.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.ShapeLawsV2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10MainEntry.
Import V10OpenFail_defs.
Import V10OpenFail_tail2.
Import V10Open_defs.
Import V10Open.
Import V10Oom_defs.
Import V10ReadErr.
Import V10Malloc65536.
Import V10DirRead_defs.
Import V10DirRead.
Import V10OpenFailBranch.
Import V10ReadLoop_defs.
Import V10ReadLoop.
Import V10Grow.
Import V10ReadPhase.
Import V10Hdr_defs.
Import V10Hdr.
Import V10FuzzIface.
Import V10TRun_defs.
Import V10TRun.
Import V10TRunB.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesFS.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)











Import V10Kit.V10MallocLayout. Import V10Kit.V10ExitBase. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts. Import V10Kit.V10LibStdioCall. Import V10Kit.V10MemPreds.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section MainFile.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hlim : (2 ^ 34 <= lim)%Z.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall M, V10Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  (* [comment removed for export] *)
  Hypothesis FZ : fuzz_call_contract.

  Let model0 := V10Open.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.

  Lemma AL_retL : forall z, In z [0x15260; 0x1528c; 0x15308; 0x15408; 0x15538]%Z -> al_ret_ok (Z_to_bv 64 z).
  Proof.
    intros z Hz. apply AL_ret. apply ret_ok_even.
    destruct Hz as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
  Qed.

  Variable data : list byte.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.

  (* [comment removed for export] *)
  Definition SUCC : TSet := t_emit (W 1 (zero_lines (Z.to_nat (calls data)))) (t_exit (exit_code 0) fs0).
  (* [comment removed for export] *)
  Definition HDRK : TSet := hdr_shape fs0 data (tr_shape SUCC).

  (* [comment removed for export] *)
  Lemma body_shape :
    (if (2 ^ 26 <=? Z.of_nat (length data))%Z then t_die msg_refused fs0 else HDRK) = t_body data fs0.
  Proof.
    unfold HDRK, hdr_shape, tr_shape, SUCC, t_body, V10TRun.paylen, V10TRun.counting, V10TRun.calls, V10TRun.cfg, V10TRun.L,
      hdr_cfg, hdr_b0, hdr_b1, hdr_b2, MAX_INPUT.
    set (len := length data). set (b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0))). set (b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0))).
    set (b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0))).
    pose proof (bv_unsigned_in_range _ (nth 0 data (Z_to_bv 8 0))) as R0. pose proof (bv_unsigned_in_range _ (nth 1 data (Z_to_bv 8 0))) as R1.
    pose proof (bv_unsigned_in_range _ (nth 2 data (Z_to_bv 8 0))) as R2. change (bv_modulus 8) with 256%Z in R0, R1, R2.
    fold b0 in R0. fold b1 in R1. fold b2 in R2.
    pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)) as Rc. pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as Rb2.
    change (2 ^ 26)%Z with 67108864%Z.
    destruct (Z.leb_spec 67108864 (Z.of_nat len)) as [Hbig|Hsmall]; [reflexivity|].
    destruct (Z.ltb_spec (Z.of_nat len) 6) as [H6|H6].
    { replace (len <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    replace (len <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    destruct (Z.ltb_spec (Z.of_nat len) (6 + (b0 + 256 * b1) mod 32768)) as [Ho|Ho].
    { replace (len <? 6 + Z.to_nat ((b0 + 256 * b1) mod 32768))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    replace (len <? 6 + Z.to_nat ((b0 + 256 * b1) mod 32768))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    assert (CALLS : Z.to_nat (if ((b0 + 256 * b1) mod 32768 =? 0)%Z then 1 else 1 + b2 mod 4)
                    = match Z.to_nat ((b0 + 256 * b1) mod 32768) with O => 1%nat | S _ => S (Z.to_nat (b2 mod 4)) end).
    { destruct (Z.eqb_spec ((b0 + 256 * b1) mod 32768) 0) as [E|E].
      - rewrite E. reflexivity.
      - destruct (Z.to_nat ((b0 + 256 * b1) mod 32768)) as [|m] eqn:Hm; [exfalso; lia|]. rewrite Z2Nat.inj_add by lia. reflexivity. }
    rewrite CALLS. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_file_path :
    path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x1520c) mem0 (seg_rom RSEGS)) model0)
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
  Proof.
    intros Hpne Hpnd Hplen.
    assert (HDR : forall j buf cap, at_header sp0 a0s path envv tid mem0 fs0 stdin0 lim data HDRK j buf cap).
    { unfold HDRK. apply (header_cases sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_free AL_tp
                           AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret AL_env).
      intros j buf cap. apply (trun_entry sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_malloc AL_tp
                                 AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret AL_env).
      apply (tl0_run sp0 a0s path envv tid mem0 fs0 stdin0 lim Hvsp Htid data AL_segs AL_rom AL_free AL_tp
               AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret AL_env FZ). }
    apply (rz_conseq RSEGS _ (t_alt2 (t_die (msg_cannot_open path) fs0) (rshape fs0 data HDRK 11 0))).
    - apply (V10Open.open_file_pipeline sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Htid ME data _ _ Hfile Hpne Hpnd Hplen).
      + apply (open_err_branch_cannot_open sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp ME Hfits).
      + intros vals R M HL P0 P1 P2 P5 HR HK HOW.
        apply (V10Malloc65536.malloc65536_node sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hvsp Htid ME Hbrk Hlim
                 AL_segs AL_rom AL_malloc AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_retL AL_env (FdFile path (Z_to_bv 64 0)) _
                 (read_phase sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim Hvsp Htid Hlim data Hfile AL_segs AL_rom AL_malloc AL_free AL_tp
                    AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret AL_env HDRK HDR)
                 vals R M HL P0 P1 P2 P5 HR HK HOW).
    - apply t_alt2_congr; [apply t_eq_refl|]. unfold t_opened. rewrite <- body_shape.
      rewrite (rshape_collapse fs0 lim Hlim data HDRK 10 0 eq_refl). apply t_eq_refl.
  Qed.
End MainFile.
End V10MainFile.
