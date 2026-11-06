(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto RtCells MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require I_read I_memcpy AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StrwF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module DrvKitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto RtCells MonadF. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require I_read I_memcpy AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import MonadG GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac zsteps_to A :=
  repeat (lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              let b := eval vm_compute in (Z.eqb pc A) in
              lazymatch b with true => fail | false => zstep end
          end).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {St : Type}.
  #[using="Type"] Lemma implMG_msys_of_enode : forall {A B} RNG n (dec : resp -> option A) (k : A -> Monad.M St B) s Q
      (P : A -> footprint -> machine_state -> Prop) ms,
    implA asegs ASHM RNG (enode n dec) (epostF P) ms ->
    (forall a RNG' ms', P a RNG' ms' -> implMG RNG' (k a) s Q ms') ->
    implMG RNG (mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B RNG n dec k s Q P ms H HK. unfold implMG, mbind, msys.
    eapply implF_ebind with (Q1 := fun (p : A * St) RNG' ms' => snd p = s /\ P (fst p) RNG' ms').
    - apply implA_implS. unfold enode in *. cbn [implF] in *.
      eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(fpk & Hfpk & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. specialize (Hk rsp RNG' HF). destruct (dec rsp) as [a|]; cbn in *.
        * eapply evtS_mono; [exact Hk|]. cbn. intros ms2 HP. split; [reflexivity| exact HP].
        * exact Hk.
      + right. exists fpk. split; [exact Hfpk|]. intros RNG' HF. specialize (Hk RNG' HF). destruct (dec (fpk ms1)) as [a|]; cbn in *.
        * eapply evtS_mono; [exact Hk|]. cbn. intros ms2 HP. split; [reflexivity| exact HP].
        * exact Hk.
    - intros [a s'] RNG' ms' [E HP]. cbn [fst snd] in *. subst s'. apply HK. exact HP.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_bind_assoc : forall {A B C} RNG (m : Monad.M St A) (g : A -> Monad.M St B) (f : B -> Monad.M St C) s Q ms,
    implMG RNG (mbind m (fun a => mbind (g a) f)) s Q ms -> implMG RNG (mbind (mbind m g) f) s Q ms.
  Proof.
    intros A B C RNG m g f s Q ms H. unfold implMG, mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.
  #[using="Type"] Lemma implMG_ret_bind : forall {A B} RNG (a : A) (f : A -> Monad.M St B) (s : St) Q ms,
    implMG RNG (f a) s Q ms -> implMG RNG (mbind (mret a) f) s Q ms.
  Proof. intros A B RNG a f s Q ms H. exact H. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_get_bind : forall {B} RNG (k : St -> Monad.M St B) s Q ms,
    implMG RNG (k s) s Q ms -> implMG RNG (mbind mget k) s Q ms.
  Proof. intros B RNG k s Q ms H. exact H. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_loop_S : forall {X R} RNG fuel (body : X -> Monad.M St (X + R)) x s (Q : R -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG (body x) s (fun r s' RNG' ms' => match r with
                                               | inl x' => implMG RNG' (mloop fuel body x') s' Q ms'
                                               | inr v => evtF asegs RNG' (Q v s' RNG') ms'
                                               end) ms ->
    implMG RNG (mloop (S fuel) body x) s Q ms.
  Proof.
    intros X R RNG fuel body x s Q ms H. cbn [mloop]. eapply implMG_bind; [exact H|].
    intros [x'|v] s' RNG' ms' H'; cbn in H'; [exact H'| apply implMG_ret; exact H'].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_sys : forall {A} RNG n (dec : resp -> option A) s (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF asegs RNG (fun ms1 => at_nodeA asegs n RNG ms1 /\
                            forall rsp a, dec rsp = Some a -> evtF asegs RNG (Q a s RNG) (nret ms1 rsp)) ms ->
    implMG RNG (msys n dec) s Q ms.
  Proof.
    intros A RNG n dec s Q ms Hn H. unfold implMG, msys. apply implF_enode.
    eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' [a s'] HF E. cbn.
    assert (ER : RNG' = RNG).
    { destruct HF as [HF _]. destruct n; try destruct Hn; cbn in HF; exact HF. }
    subst RNG'. specialize (Hk rsp). destruct (dec rsp) as [a'|]; [|discriminate E]. injection E as <- <-. apply Hk. reflexivity.
  Qed.
End Glue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma memcpy_i_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo Dst Src n : Z) (src junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 Src -> a2 = Z_to_bv 64 n ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2240 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m ->
  bytes_at asegs m Src src -> length src = Z.to_nat n -> 0 <= n <= 2^40 ->
  rw_cells asegs m Dst [CB (Z.to_nat n) junk] ->
  (Src + n <= Dst \/ Dst + n <= Src) ->
  mobjA RNG m Src n -> mobjA RNG m Dst n -> Src + n <= ATOP -> Dst + n <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (Dst, Dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Dst [CB (Z.to_nat n) src] /\ bytes_at asegs m' Src src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54960) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> -> -> MI ST BU LO RT SRC LEN Hn DST SEP OS OD TS TD RIMG RSTK.
  (nd_pre OS 6%nat; intros S0 S47 SUNP SRNG (RLO1 & RHI1 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18) SAPP; nd_post).
  (nd_pre OD 6%nat; intros D0 D47 DUNP DRNG (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) DAPP; nd_post).
  (nd_pre RT 9%nat; intros _ GOT GRIC RMEM SHB _ INI LAY _; nd_post).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  zstep.
  eapply evtF_mono.
  - eapply (memcpy_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo src junk RLO1 RHI1 RLO2 RHI2); rewrite ?E0, ?E1, ?E2;
      first [ assumption | unfold KHIGH, KEND in *; lia ].
  - cbv beta. intros ms' PO. unfold memcpy_i_post in PO. rewrite ?E0, ?E1, ?E2 in PO. exact PO.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma read_i_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo fd B count : Z) (junk : list byte) (errv : word),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 count ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2208 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m -> bv_unsigned tp = ATP ->
  rw_cells asegs m B [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (ATP + -164) [C4 errv] ->
  3 <= fd < 2^32 -> 1 <= count <= 16777216 ->
  (0x603000 <= B \/ (0x5d0c50 <= B /\ B + count <= 0x603000)) -> B + count <= ATOP -> tclr B count ->
  mobjA RNG m B count ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng_atls RNG ->
  implA asegs ASHM RNG (enode (NRead fd B count) (dec_read B count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x44488) fc None m (seg_rom asegs)).
Proof.
  intros until errv. intros -> EA1 -> MI ST BU LO RT ETP DST ERR FD CNT BHI BTOP BT OB RIMG RSTK RTLS.
  (nd_pre OB 6%nat; intros B0 B47 BUNP BRNG (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) BAPP; nd_post).
  (nd_pre RT 17%nat; intros _ GOT _ _ SHB _ INI LAY _ _ _ _ _ _ _ RRD _; nd_post).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  (pose proof atp_lin as ndP__; nd_pre ndP__ 3%nat; intros (TL & (KI & KS) & _) (TI1 & TI2) (TS1 & TS2); nd_post). pose proof atp_below_atop as TBA. unfold ATP in *.
  assert (EB : bv_unsigned a1 = B) by (subst a1; apply unsigned_lit; lia).
  assert (KB : exists kb, 0 <= kb <= 1 /\ B + count <= ATPv + -164 + kb * 18446744073709551616 /\ ATPv + -164 + 4 <= B + (1 - kb) * 18446744073709551616).
  { unfold tclr in BT. destruct BT as [BT|BT]; [exists 0 | exists 1]; lia. }
  (nd_pre KB 4%nat; intros kb KB0 KB1 KB2; nd_post).
  iprefix. zstep. apply evtF_done.
  rewrite <- EB in *.
  eapply (read_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 (Z_to_bv 64 count) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m lo fd count junk errv RLO2 RHI2 kt_img kt_sh kb); rewrite ?ETP;
    first [ assumption | reflexivity | unfold KHIGH, KEND in *; lia
          | eapply rng_sub; [exact RTLS| lia| lia] ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac zsteps_to A :=
  repeat (lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              let b := eval vm_compute in (Z.eqb pc A) in
              lazymatch b with true => fail | false => zstep end
          end).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {St : Type}.
  #[using="Type"] Lemma implMG_msys_of_enode : forall {A B} RNG n (dec : resp -> option A) (k : A -> Monad.M St B) s Q
      (P : A -> footprint -> machine_state -> Prop) ms,
    implA asegs ASHM RNG (enode n dec) (epostF P) ms ->
    (forall a RNG' ms', P a RNG' ms' -> implMG RNG' (k a) s Q ms') ->
    implMG RNG (mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B RNG n dec k s Q P ms H HK. unfold implMG, mbind, msys.
    eapply implF_ebind with (Q1 := fun (p : A * St) RNG' ms' => snd p = s /\ P (fst p) RNG' ms').
    - apply implA_implS. unfold enode in *. cbn [implF] in *.
      eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(fpk & Hfpk & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. specialize (Hk rsp RNG' HF). destruct (dec rsp) as [a|]; cbn in *.
        * eapply evtS_mono; [exact Hk|]. cbn. intros ms2 HP. split; [reflexivity| exact HP].
        * exact Hk.
      + right. exists fpk. split; [exact Hfpk|]. intros RNG' HF. specialize (Hk RNG' HF). destruct (dec (fpk ms1)) as [a|]; cbn in *.
        * eapply evtS_mono; [exact Hk|]. cbn. intros ms2 HP. split; [reflexivity| exact HP].
        * exact Hk.
    - intros [a s'] RNG' ms' [E HP]. cbn [fst snd] in *. subst s'. apply HK. exact HP.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_bind_assoc : forall {A B C} RNG (m : Monad.M St A) (g : A -> Monad.M St B) (f : B -> Monad.M St C) s Q ms,
    implMG RNG (mbind m (fun a => mbind (g a) f)) s Q ms -> implMG RNG (mbind (mbind m g) f) s Q ms.
  Proof.
    intros A B C RNG m g f s Q ms H. unfold implMG, mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.
  #[using="Type"] Lemma implMG_ret_bind : forall {A B} RNG (a : A) (f : A -> Monad.M St B) (s : St) Q ms,
    implMG RNG (f a) s Q ms -> implMG RNG (mbind (mret a) f) s Q ms.
  Proof. intros A B RNG a f s Q ms H. exact H. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_get_bind : forall {B} RNG (k : St -> Monad.M St B) s Q ms,
    implMG RNG (k s) s Q ms -> implMG RNG (mbind mget k) s Q ms.
  Proof. intros B RNG k s Q ms H. exact H. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_loop_S : forall {X R} RNG fuel (body : X -> Monad.M St (X + R)) x s (Q : R -> St -> footprint -> machine_state -> Prop) ms,
    implMG RNG (body x) s (fun r s' RNG' ms' => match r with
                                               | inl x' => implMG RNG' (mloop fuel body x') s' Q ms'
                                               | inr v => evtF asegs RNG' (Q v s' RNG') ms'
                                               end) ms ->
    implMG RNG (mloop (S fuel) body x) s Q ms.
  Proof.
    intros X R RNG fuel body x s Q ms H. cbn [mloop]. eapply implMG_bind; [exact H|].
    intros [x'|v] s' RNG' ms' H'; cbn in H'; [exact H'| apply implMG_ret; exact H'].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_sys : forall {A} RNG n (dec : resp -> option A) s (Q : A -> St -> footprint -> machine_state -> Prop) ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF asegs RNG (fun ms1 => at_nodeA asegs n RNG ms1 /\
                            forall rsp a, dec rsp = Some a -> evtF asegs RNG (Q a s RNG) (nret ms1 rsp)) ms ->
    implMG RNG (msys n dec) s Q ms.
  Proof.
    intros A RNG n dec s Q ms Hn H. unfold implMG, msys. apply implF_enode.
    eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' [a s'] HF E. cbn.
    assert (ER : RNG' = RNG).
    { destruct HF as [HF _]. destruct n; try destruct Hn; cbn in HF; exact HF. }
    subst RNG'. specialize (Hk rsp). destruct (dec rsp) as [a'|]; [|discriminate E]. injection E as <- <-. apply Hk. reflexivity.
  Qed.
End Glue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma memcpy_i_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo Dst Src n : Z) (src junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 Src -> a2 = Z_to_bv 64 n ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2240 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m ->
  bytes_at asegs m Src src -> length src = Z.to_nat n -> 0 <= n <= 2^40 ->
  rw_cells asegs m Dst [CB (Z.to_nat n) junk] ->
  (Src + n <= Dst \/ Dst + n <= Src) ->
  mobjA RNG m Src n -> mobjA RNG m Dst n -> Src + n <= ATOP -> Dst + n <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (Dst, Dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Dst [CB (Z.to_nat n) src] /\ bytes_at asegs m' Src src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x549c8) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> -> -> MI ST BU LO RT SRC LEN Hn DST SEP OS OD TS TD RIMG RSTK.
  (nd_pre OS 6%nat; intros S0 S47 SUNP SRNG (RLO1 & RHI1 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18) SAPP; nd_post).
  (nd_pre OD 6%nat; intros D0 D47 DUNP DRNG (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) DAPP; nd_post).
  (nd_pre RT 9%nat; intros _ GOT GRIC RMEM SHB _ INI LAY _; nd_post).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  zstep.
  eapply evtF_mono.
  - eapply (memcpy_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo src junk RLO1 RHI1 RLO2 RHI2); rewrite ?E0, ?E1, ?E2;
      first [ assumption | unfold KHIGH, KEND in *; lia ].
  - cbv beta. intros ms' PO. unfold memcpy_i_post in PO. rewrite ?E0, ?E1, ?E2 in PO. exact PO.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma read_i_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo fd B count : Z) (junk : list byte) (errv : word),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 count ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2208 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m -> bv_unsigned tp = ATP ->
  rw_cells asegs m B [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (ATP + -164) [C4 errv] ->
  3 <= fd < 2^32 -> 1 <= count <= 16777216 ->
  (0x604000 <= B \/ (0x5d1050 <= B /\ B + count <= 0x604000)) -> B + count <= ATOP -> tclr B count ->
  mobjA RNG m B count ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng_atls RNG ->
  implA asegs ASHM RNG (enode (NRead fd B count) (dec_read B count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x444f0) fc None m (seg_rom asegs)).
Proof.
  intros until errv. intros -> EA1 -> MI ST BU LO RT ETP DST ERR FD CNT BHI BTOP BT OB RIMG RSTK RTLS.
  (nd_pre OB 6%nat; intros B0 B47 BUNP BRNG (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) BAPP; nd_post).
  (nd_pre RT 17%nat; intros _ GOT _ _ SHB _ INI LAY _ _ _ _ _ _ _ RRD _; nd_post).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  (pose proof atp_lin as ndP__; nd_pre ndP__ 3%nat; intros (TL & (KI & KS) & _) (TI1 & TI2) (TS1 & TS2); nd_post). pose proof atp_below_atop as TBA. unfold ATP in *.
  assert (EB : bv_unsigned a1 = B) by (subst a1; apply unsigned_lit; lia).
  assert (KB : exists kb, 0 <= kb <= 1 /\ B + count <= ATPv + -164 + kb * 18446744073709551616 /\ ATPv + -164 + 4 <= B + (1 - kb) * 18446744073709551616).
  { unfold tclr in BT. destruct BT as [BT|BT]; [exists 0 | exists 1]; lia. }
  (nd_pre KB 4%nat; intros kb KB0 KB1 KB2; nd_post).
  iprefix. zstep. apply evtF_done.
  rewrite <- EB in *.
  eapply (read_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 (Z_to_bv 64 count) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m lo fd count junk errv RLO2 RHI2 kt_img kt_sh kb); rewrite ?ETP;
    first [ assumption | reflexivity | unfold KHIGH, KEND in *; lia
          | eapply rng_sub; [exact RTLS| lia| lia] ].
Qed.
End CANSEC1.
End TwB.
End DrvKitA.

(* [comment removed for export] *)
Module ExitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.      (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 779776).      (* [comment removed for export] *)
Definition EXIT_A : Z := 0x947c4.
Definition STDIO_EXIT_A : Z := 0x9a5b4.
Definition STDIO_EXIT_RET_A : Z := 0x94830.
Definition MDTOR_DEPTH : Z := 4096.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iv_clear (KEEP : list (Z * Z)) (iv : Z * Z) : Prop :=
  Forall (fun k => snd iv <= fst k \/ snd k <= fst iv) KEEP.
Lemma keep_disjoint : forall (KEEP W : list (Z * Z)) k A n,
  Forall (iv_clear KEEP) W -> In k KEEP -> fst k <= A -> A + n <= snd k -> disjoint_from W A n.
Proof.
  intros KEEP W k A n HW Hk H1 H2. induction HW as [|[lo hi] W H HW IH]; cbn [disjoint_from]; [exact I|].
  split; [| exact IH]. unfold iv_clear in H. pose proof (proj1 (Forall_forall _ _) H k Hk) as C. cbn [fst snd] in C. lia.
Qed.
Lemma iv_clear_app : forall K1 K2 iv, iv_clear (K1 ++ K2) iv <-> iv_clear K1 iv /\ iv_clear K2 iv.
Proof. intros. unfold iv_clear. apply Forall_app. Qed.
(* [comment removed for export] *)
Ltac keep_in := cbn [In]; repeat first [left; reflexivity | right].

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition module_dtor_post (MW : list (Z * Z)) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((bv_unsigned sp - MDTOR_DEPTH, bv_unsigned sp) :: MW) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition module_dtor_stmt (PRE : mem -> Prop) (MW : list (Z * Z)) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (ATOP + 4096 <= lo) ->
    mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    evtF asegs RNG (module_dtor_post MW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x84c10) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exit_cells (t : Z) (reg : bool) (m : mem) : Prop :=
     rw_cells asegs m (ATPv + -168) [C4 (Z_to_bv 64 t)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601828 [C4 z64]                                                (* [comment removed for export] *)
  /\ atx_cells reg 0 m                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1404a0 [C1 (Z_to_bv 8 0)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6190 [C8 (Z_to_bv 64 0xa4f40); C8 (Z_to_bv 64 0xa4f30)]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa4f30 [C8 (Z_to_bv 64 0x84c10); C8 (Z_to_bv 64 0x32a80)]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaaf90 [C1 (Z_to_bv 8 0)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5480 [C8 (Z_to_bv 64 0x946a8); C8 z64]                        (* [comment removed for export] *)
  /\ (exists dso : word, rw_cells asegs m 0xa71d0 [C8 dso])                            (* [comment removed for export] *)
  /\ (0 < t < 4194304).

(* [comment removed for export] *)
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
  [(sp - 48 - MDTOR_DEPTH, sp); (0x601828, 0x60182c); (0x601608, 0x601609); (0x601610, 0x601614); (0x601618, 0x601620); (0xaaf90, 0xaaf91)].

(* [comment removed for export] *)
Definition aexit_prefix_post (MW : list (Z * Z)) (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET_A) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 STDIO_EXIT_A) fc None m' (seg_rom asegs)
    /\ munch (AEXIT_W1 (bv_unsigned sp) ++ MW) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra].

#[using="Type"] Lemma outside_app : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto.
Qed.
#[using="Type"] Lemma disjoint_from_low : forall (W : list (Z * Z)) A n, Forall (fun iv => snd iv <= ATOP) W -> ATOP <= A -> 0 <= n -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n HW HA Hn; cbn [disjoint_from]; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn [snd] in H1. split; [right; lia| apply IH; assumption].
Qed.

Section Prefix.
  Variable PRE : mem -> Prop.
  Variable MW : list (Z * Z).
  Hypothesis MDTOR : module_dtor_stmt PRE MW.
  (* [comment removed for export] *)
  Hypothesis MW_low : Forall (fun iv => snd iv <= ATOP) MW.      (* [comment removed for export] *)
  Hypothesis PRE_frame : forall sp m m', PRE m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.

  #[using="MDTOR MW_low PRE_frame"] Lemma aexit_prefix_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (reg : bool),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    exit_cells t reg m ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 code ->
    (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (ATOP + 4096 <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    evtF asegs RNG (aexit_prefix_post MW sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_A) fc None m (seg_rom asegs)).
  Proof.
    intros until reg.
    intros HPRE ST EC MI -> -> LO KH RSTK RIMG RISH RTLS.
    destruct EC as (TID & EXL & ATXC & COV & GF & FA & FINZ & GCX & (dso & DSO) & Ht).
    destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. atop_facts.
    pose proof atp_lin as ((TL & _) & _). pose proof atp_below_atop as TBA. unfold ATP, EXIT_A in *.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    (* [comment removed for export] *)
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    astep. sort_lits. amo_step. astep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. astep.
    hstep. hstep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    steps_to 0x9f074%Z.
    (* [comment removed for export] *)
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
    (* [comment removed for export] *)
    destruct reg; cbn [Z.b2z] in SLOT; [change (1 + 1)%Z with 2%Z in SLOT | change (1 + 0)%Z with 1%Z in SLOT].
    1: {
    (* [comment removed for export] *)
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x32a80%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0x946a8%Z. hstep.
    steps_to 0x32b0c%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH; lia) MU WM) as HPRE1 end.
    eapply evtF_cut.
    { eapply (MDTOR RNG); [exact HPRE1 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; unfold MDTOR_DEPTH; lia | exact KH
                          | eassumption | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH]. }
    cbv beta. intros ms' PO. unfold module_dtor_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MUd WMd MId STd; nd_post).
    rewrite unsigned_lit in MUd, STd by lia. unfold MDTOR_DEPTH in MUd.
    (* [comment removed for export] *)
    assert (DJ : forall A n, bv_unsigned sp + -48 <= A -> 0 <= n -> disjoint_from ((bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48) :: MW) A n).
    { intros A n HA Hn. cbn [disjoint_from]. split; [right; lia| apply disjoint_from_low; [exact MW_low| lia| exact Hn]]. }
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR'. clear FR. rename FR' into FR.
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR0 MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR0'. clear FR0. rename FR0' into FR0.
    assert (MU2 : munch (AEXIT_W1 (bv_unsigned sp) ++ MW) m ltac:(lazymatch type of MId with mem_inv _ ?mm => exact mm end)).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU]. intros xq Hx. apply outside_app in Hx as [Hx _]. unfold AEXIT_W1, MDTOR_DEPTH in Hx. exact Hx.
      - eapply munch_weaken; [| exact MUd]. intros xq Hx. apply outside_app in Hx as [Hx1 Hx2]. unfold AEXIT_W1, MDTOR_DEPTH in Hx1. cbn [outside] in Hx1 |- *.
        split; [lia| exact Hx2]. }
    pose proof (wmono_trans asegs _ _ _ WM WMd) as WM2.
    clear MU WM MUd WMd MI ST. rename MId into MI. rename STd into ST.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x947a8)) with (Z_to_bv 64 0x947a8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    astep. astep. hstep. hstep. hstep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    hstep. hstep.
    hstep.
    apply evtF_done. unfold aexit_prefix_post, STDIO_EXIT_RET_A, STDIO_EXIT_A, ATP.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI|]. split; [exact ST| exact FR].
    }
    (* [comment removed for export] *)
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x32a80%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0x946a8%Z. hstep.
    steps_to 0x32b0c%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH; lia) MU WM) as HPRE1 end.
    eapply evtF_cut.
    { eapply (MDTOR RNG); [exact HPRE1 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; unfold MDTOR_DEPTH; lia | exact KH
                          | eassumption | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH]. }
    cbv beta. intros ms' PO. unfold module_dtor_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MUd WMd MId STd; nd_post).
    rewrite unsigned_lit in MUd, STd by lia. unfold MDTOR_DEPTH in MUd.
    (* [comment removed for export] *)
    assert (DJ : forall A n, bv_unsigned sp + -48 <= A -> 0 <= n -> disjoint_from ((bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48) :: MW) A n).
    { intros A n HA Hn. cbn [disjoint_from]. split; [right; lia| apply disjoint_from_low; [exact MW_low| lia| exact Hn]]. }
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR'. clear FR. rename FR' into FR.
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR0 MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR0'. clear FR0. rename FR0' into FR0.
    assert (MU2 : munch (AEXIT_W1 (bv_unsigned sp) ++ MW) m ltac:(lazymatch type of MId with mem_inv _ ?mm => exact mm end)).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU]. intros xq Hx. apply outside_app in Hx as [Hx _]. unfold AEXIT_W1, MDTOR_DEPTH in Hx. exact Hx.
      - eapply munch_weaken; [| exact MUd]. intros xq Hx. apply outside_app in Hx as [Hx1 Hx2]. unfold AEXIT_W1, MDTOR_DEPTH in Hx1. cbn [outside] in Hx1 |- *.
        split; [lia| exact Hx2]. }
    pose proof (wmono_trans asegs _ _ _ WM WMd) as WM2.
    clear MU WM MUd WMd MI ST. rename MId into MI. rename STd into ST.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x947a8)) with (Z_to_bv 64 0x947a8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    astep. astep. hstep. hstep. hstep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    hstep. hstep.
    hstep.
    apply evtF_done. unfold aexit_prefix_post, STDIO_EXIT_RET_A, STDIO_EXIT_A, ATP.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI|]. split; [exact ST| exact FR].
  Qed.
End Prefix.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (stdio_exit_model : Monad.M St unit).
  Variable PRE : mem -> Prop.
  Variable MW : list (Z * Z).
  Hypothesis MDTOR : module_dtor_stmt PRE MW.
  Hypothesis MW_low : Forall (fun iv => snd iv <= ATOP) MW.
  Hypothesis PRE_frame : forall sp m m', PRE m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.
  (* [comment removed for export] *)
  Variable SX : St -> footprint -> mem -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  (* [comment removed for export] *)
  Hypothesis SX_frame : forall s RNG sp m m', SX s RNG m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MW) m m' -> wmono asegs m m' -> SX s RNG m'.

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      : unit -> St -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ rng_aimg RNG'.

  (* [comment removed for export] *)
  Definition stdio_exit_stmtA : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (s : St),
      stk asegs m lo (bv_unsigned sp) ->
      SX s RNG m ->
      mem_inv asegs m ->
      lo <= bv_unsigned sp - stdio_exit_frame -> ATOP + 4096 <= lo -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      tp = Z_to_bv 64 ATP ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
      implMG RNG stdio_exit_model s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 STDIO_EXIT_A) fc None m (seg_rom asegs)).

  Hypothesis stdio_exit_spec : stdio_exit_stmtA.

  (* [comment removed for export] *)
  Definition at_exitA (code : Z) (s : St) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (reg : bool),
      ms = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 EXIT_A) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp) /\ exit_cells t reg m /\ PRE m /\ SX s RNG m /\ mem_inv asegs m
      /\ lo <= bv_unsigned sp - 48 - MDTOR_DEPTH - stdio_exit_frame /\ ATOP + 4096 <= lo /\ bv_unsigned sp <= 2^47 /\ bv_unsigned sp mod 16 = 0
      /\ (rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG).

  Definition exit_specA__stmt : Prop := forall (code : Z) (s : St) (RNG : footprint) (Q : Empty_set -> St -> footprint -> machine_state -> Prop) ms,
    at_exitA code s RNG ms -> implMG RNG (exit_model stdio_exit_model code) s Q ms.
  Section Zd2.   (* [comment removed for export] *)
  Variable code : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 0).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 1).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 2).
  Variable Q : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 3).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 4).
  #[using="MW MDTOR MW_low PRE_frame stdio_exit_frame_nonneg SX_frame stdio_exit_spec"] Lemma exit_specA__body : ltac:(let T := type of (fun (h : exit_specA__stmt) => h code s RNG Q ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (code, (s, (RNG, (Q, ms))))) as _.
    intros AE.
    (nd_pre AE 36%nat; intros ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo t reg ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into AE).
    (nd_pre AE 13%nat; intros ST EC HPRE HSX MI LO LOLO SP47 ALN RSTK RIMG RISH RTLS; nd_post).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. atop_facts.
    unfold exit_model.
    eapply implMG_bind with (Q1 := fun _ _ RNG' ms' => rng_aimg RNG' /\
                 exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F' fc' m',
                 ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET_A) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F' (Z_to_bv 64 STDIO_EXIT_RET_A) fc' None m' (seg_rom asegs)).
    - (* [comment removed for export] *)
      apply implMG_from_evtF.
      eapply evtF_cut.
      { eapply (aexit_prefix_spec PRE MW MDTOR MW_low PRE_frame RNG) with (lo := lo) (code := code) (t := t) (reg := reg);
          [exact HPRE | exact ST | exact EC | exact MI | reflexivity | reflexivity | unfold MDTOR_DEPTH; lia | exact LOLO | exact RSTK | exact RIMG | exact RISH | exact RTLS]. }
      cbv beta. intros ms' PO. unfold aexit_prefix_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MU WM MI' ST' FR; nd_post).
      apply evtF_done. eapply implMG_mono.
      { eapply stdio_exit_spec with (lo := lo);
          [ rewrite unsigned_lit by lia; exact ST'
          | eapply SX_frame; [exact HSX | | exact MU | exact WM]; unfold MDTOR_DEPTH; lia
          | exact MI' | rewrite unsigned_lit by lia; lia | exact LOLO | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; clear - ALN; Z.div_mod_to_equations; lia | reflexivity
          | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH | exact RTLS ]. }
      cbv beta. intros [] s' RNG' ms' PO. unfold stdio_exit_post in PO. destruct_exs PO. destruct PO as (-> & RI').
      split; [exact RI'|].
      replace (ret_pc (Z_to_bv 64 STDIO_EXIT_RET_A)) with (Z_to_bv 64 STDIO_EXIT_RET_A) by (symmetry; apply ret_pc_even; [unfold STDIO_EXIT_RET_A; lia|reflexivity]).
      repeat eexists; cbv delta [mkR]; reflexivity.
    - (* [comment removed for export] *)
      intros [] s' RNG' ms' (RI' & PO). destruct_exs PO. subst ms'. unfold STDIO_EXIT_RET_A.
      apply implMG_sys; [exact I|]. do 4 zstep. step_ecall.
      split; [ at_nodeA_solve | intros rsp a HH; cbn in HH; discriminate HH ].
  Qed.
  End Zd2.
  #[using="MW MDTOR MW_low PRE_frame stdio_exit_frame_nonneg SX_frame stdio_exit_spec"] Lemma exit_specA : ltac:(let t := eval cbv delta [exit_specA__stmt] in exit_specA__stmt in exact t).
  Proof. exact exit_specA__body. Qed.
End ExitProof.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.      (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 780288).      (* [comment removed for export] *)
Definition EXIT_A : Z := 0x94ba8.
Definition STDIO_EXIT_A : Z := 0x9a998.
Definition STDIO_EXIT_RET_A : Z := 0x94c14.
Definition MDTOR_DEPTH : Z := 4096.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iv_clear (KEEP : list (Z * Z)) (iv : Z * Z) : Prop :=
  Forall (fun k => snd iv <= fst k \/ snd k <= fst iv) KEEP.
Lemma keep_disjoint : forall (KEEP W : list (Z * Z)) k A n,
  Forall (iv_clear KEEP) W -> In k KEEP -> fst k <= A -> A + n <= snd k -> disjoint_from W A n.
Proof.
  intros KEEP W k A n HW Hk H1 H2. induction HW as [|[lo hi] W H HW IH]; cbn [disjoint_from]; [exact I|].
  split; [| exact IH]. unfold iv_clear in H. pose proof (proj1 (Forall_forall _ _) H k Hk) as C. cbn [fst snd] in C. lia.
Qed.
Lemma iv_clear_app : forall K1 K2 iv, iv_clear (K1 ++ K2) iv <-> iv_clear K1 iv /\ iv_clear K2 iv.
Proof. intros. unfold iv_clear. apply Forall_app. Qed.
(* [comment removed for export] *)
Ltac keep_in := cbn [In]; repeat first [left; reflexivity | right].

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition module_dtor_post (MW : list (Z * Z)) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((bv_unsigned sp - MDTOR_DEPTH, bv_unsigned sp) :: MW) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition module_dtor_stmt (PRE : mem -> Prop) (MW : list (Z * Z)) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (ATOP + 4096 <= lo) ->
    mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    evtF asegs RNG (module_dtor_post MW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x84c9c) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exit_cells (t : Z) (reg : bool) (m : mem) : Prop :=
     rw_cells asegs m (ATPv + -168) [C4 (Z_to_bv 64 t)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601c28 [C4 z64]                                                (* [comment removed for export] *)
  /\ atx_cells reg 0 m                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1408a0 [C1 (Z_to_bv 8 0)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6570 [C8 (Z_to_bv 64 0xa5320); C8 (Z_to_bv 64 0xa5310)]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5310 [C8 (Z_to_bv 64 0x84c9c); C8 (Z_to_bv 64 0x32ae8)]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab390 [C1 (Z_to_bv 8 0)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5860 [C8 (Z_to_bv 64 0x94a8c); C8 z64]                        (* [comment removed for export] *)
  /\ (exists dso : word, rw_cells asegs m 0xa75b0 [C8 dso])                            (* [comment removed for export] *)
  /\ (0 < t < 4194304).

(* [comment removed for export] *)
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
  [(sp - 48 - MDTOR_DEPTH, sp); (0x601c28, 0x601c2c); (0x601a08, 0x601a09); (0x601a10, 0x601a14); (0x601a18, 0x601a20); (0xab390, 0xab391)].

(* [comment removed for export] *)
Definition aexit_prefix_post (MW : list (Z * Z)) (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET_A) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 STDIO_EXIT_A) fc None m' (seg_rom asegs)
    /\ munch (AEXIT_W1 (bv_unsigned sp) ++ MW) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra].

#[using="Type"] Lemma outside_app : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto.
Qed.
#[using="Type"] Lemma disjoint_from_low : forall (W : list (Z * Z)) A n, Forall (fun iv => snd iv <= ATOP) W -> ATOP <= A -> 0 <= n -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n HW HA Hn; cbn [disjoint_from]; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn [snd] in H1. split; [right; lia| apply IH; assumption].
Qed.

Section Prefix.
  Variable PRE : mem -> Prop.
  Variable MW : list (Z * Z).
  Hypothesis MDTOR : module_dtor_stmt PRE MW.
  (* [comment removed for export] *)
  Hypothesis MW_low : Forall (fun iv => snd iv <= ATOP) MW.      (* [comment removed for export] *)
  Hypothesis PRE_frame : forall sp m m', PRE m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.

  #[using="MDTOR MW_low PRE_frame"] Lemma aexit_prefix_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (reg : bool),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    exit_cells t reg m ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 code ->
    (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (ATOP + 4096 <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    evtF asegs RNG (aexit_prefix_post MW sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_A) fc None m (seg_rom asegs)).
  Proof.
    intros until reg.
    intros HPRE ST EC MI -> -> LO KH RSTK RIMG RISH RTLS.
    destruct EC as (TID & EXL & ATXC & COV & GF & FA & FINZ & GCX & (dso & DSO) & Ht).
    destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. atop_facts.
    pose proof atp_lin as ((TL & _) & _). pose proof atp_below_atop as TBA. unfold ATP, EXIT_A in *.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    (* [comment removed for export] *)
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    astep. sort_lits. amo_step. astep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. astep.
    hstep. hstep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    steps_to 0x9f458%Z.
    (* [comment removed for export] *)
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
    (* [comment removed for export] *)
    destruct reg; cbn [Z.b2z] in SLOT; [change (1 + 1)%Z with 2%Z in SLOT | change (1 + 0)%Z with 1%Z in SLOT].
    1: {
    (* [comment removed for export] *)
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x32ae8%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0x94a8c%Z. hstep.
    steps_to 0x32b74%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH; lia) MU WM) as HPRE1 end.
    eapply evtF_cut.
    { eapply (MDTOR RNG); [exact HPRE1 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; unfold MDTOR_DEPTH; lia | exact KH
                          | eassumption | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH]. }
    cbv beta. intros ms' PO. unfold module_dtor_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MUd WMd MId STd; nd_post).
    rewrite unsigned_lit in MUd, STd by lia. unfold MDTOR_DEPTH in MUd.
    (* [comment removed for export] *)
    assert (DJ : forall A n, bv_unsigned sp + -48 <= A -> 0 <= n -> disjoint_from ((bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48) :: MW) A n).
    { intros A n HA Hn. cbn [disjoint_from]. split; [right; lia| apply disjoint_from_low; [exact MW_low| lia| exact Hn]]. }
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR'. clear FR. rename FR' into FR.
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR0 MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR0'. clear FR0. rename FR0' into FR0.
    assert (MU2 : munch (AEXIT_W1 (bv_unsigned sp) ++ MW) m ltac:(lazymatch type of MId with mem_inv _ ?mm => exact mm end)).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU]. intros xq Hx. apply outside_app in Hx as [Hx _]. unfold AEXIT_W1, MDTOR_DEPTH in Hx. exact Hx.
      - eapply munch_weaken; [| exact MUd]. intros xq Hx. apply outside_app in Hx as [Hx1 Hx2]. unfold AEXIT_W1, MDTOR_DEPTH in Hx1. cbn [outside] in Hx1 |- *.
        split; [lia| exact Hx2]. }
    pose proof (wmono_trans asegs _ _ _ WM WMd) as WM2.
    clear MU WM MUd WMd MI ST. rename MId into MI. rename STd into ST.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x94b8c)) with (Z_to_bv 64 0x94b8c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    astep. astep. hstep. hstep. hstep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    hstep. hstep.
    hstep.
    apply evtF_done. unfold aexit_prefix_post, STDIO_EXIT_RET_A, STDIO_EXIT_A, ATP.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI|]. split; [exact ST| exact FR].
    }
    (* [comment removed for export] *)
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x32ae8%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0x94a8c%Z. hstep.
    steps_to 0x32b74%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH; lia) MU WM) as HPRE1 end.
    eapply evtF_cut.
    { eapply (MDTOR RNG); [exact HPRE1 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; unfold MDTOR_DEPTH; lia | exact KH
                          | eassumption | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH]. }
    cbv beta. intros ms' PO. unfold module_dtor_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MUd WMd MId STd; nd_post).
    rewrite unsigned_lit in MUd, STd by lia. unfold MDTOR_DEPTH in MUd.
    (* [comment removed for export] *)
    assert (DJ : forall A n, bv_unsigned sp + -48 <= A -> 0 <= n -> disjoint_from ((bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48) :: MW) A n).
    { intros A n HA Hn. cbn [disjoint_from]. split; [right; lia| apply disjoint_from_low; [exact MW_low| lia| exact Hn]]. }
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR'. clear FR. rename FR' into FR.
    pose proof (rw_cells_transport asegs _ _ _ _ _ FR0 MUd WMd ltac:(apply DJ; [lia| cbn; lia])) as FR0'. clear FR0. rename FR0' into FR0.
    assert (MU2 : munch (AEXIT_W1 (bv_unsigned sp) ++ MW) m ltac:(lazymatch type of MId with mem_inv _ ?mm => exact mm end)).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU]. intros xq Hx. apply outside_app in Hx as [Hx _]. unfold AEXIT_W1, MDTOR_DEPTH in Hx. exact Hx.
      - eapply munch_weaken; [| exact MUd]. intros xq Hx. apply outside_app in Hx as [Hx1 Hx2]. unfold AEXIT_W1, MDTOR_DEPTH in Hx1. cbn [outside] in Hx1 |- *.
        split; [lia| exact Hx2]. }
    pose proof (wmono_trans asegs _ _ _ WM WMd) as WM2.
    clear MU WM MUd WMd MI ST. rename MId into MI. rename STd into ST.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x94b8c)) with (Z_to_bv 64 0x94b8c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    astep. astep. hstep. hstep. hstep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    hstep. hstep.
    hstep.
    apply evtF_done. unfold aexit_prefix_post, STDIO_EXIT_RET_A, STDIO_EXIT_A, ATP.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI|]. split; [exact ST| exact FR].
  Qed.
End Prefix.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (stdio_exit_model : Monad.M St unit).
  Variable PRE : mem -> Prop.
  Variable MW : list (Z * Z).
  Hypothesis MDTOR : module_dtor_stmt PRE MW.
  Hypothesis MW_low : Forall (fun iv => snd iv <= ATOP) MW.
  Hypothesis PRE_frame : forall sp m m', PRE m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.
  (* [comment removed for export] *)
  Variable SX : St -> footprint -> mem -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  (* [comment removed for export] *)
  Hypothesis SX_frame : forall s RNG sp m m', SX s RNG m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MW) m m' -> wmono asegs m m' -> SX s RNG m'.

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      : unit -> St -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ rng_aimg RNG'.

  (* [comment removed for export] *)
  Definition stdio_exit_stmtA : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (s : St),
      stk asegs m lo (bv_unsigned sp) ->
      SX s RNG m ->
      mem_inv asegs m ->
      lo <= bv_unsigned sp - stdio_exit_frame -> ATOP + 4096 <= lo -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      tp = Z_to_bv 64 ATP ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
      implMG RNG stdio_exit_model s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 STDIO_EXIT_A) fc None m (seg_rom asegs)).

  Hypothesis stdio_exit_spec : stdio_exit_stmtA.

  (* [comment removed for export] *)
  Definition at_exitA (code : Z) (s : St) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (reg : bool),
      ms = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 EXIT_A) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp) /\ exit_cells t reg m /\ PRE m /\ SX s RNG m /\ mem_inv asegs m
      /\ lo <= bv_unsigned sp - 48 - MDTOR_DEPTH - stdio_exit_frame /\ ATOP + 4096 <= lo /\ bv_unsigned sp <= 2^47 /\ bv_unsigned sp mod 16 = 0
      /\ (rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG).

  Definition exit_specA__stmt : Prop := forall (code : Z) (s : St) (RNG : footprint) (Q : Empty_set -> St -> footprint -> machine_state -> Prop) ms,
    at_exitA code s RNG ms -> implMG RNG (exit_model stdio_exit_model code) s Q ms.
  Section Zd2.   (* [comment removed for export] *)
  Variable code : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 0).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 1).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 2).
  Variable Q : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 3).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'exit_specA__stmt 4).
  #[using="MW MDTOR MW_low PRE_frame stdio_exit_frame_nonneg SX_frame stdio_exit_spec"] Lemma exit_specA__body : ltac:(let T := type of (fun (h : exit_specA__stmt) => h code s RNG Q ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (code, (s, (RNG, (Q, ms))))) as _.
    intros AE.
    (nd_pre AE 36%nat; intros ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo t reg ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into AE).
    (nd_pre AE 13%nat; intros ST EC HPRE HSX MI LO LOLO SP47 ALN RSTK RIMG RISH RTLS; nd_post).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. atop_facts.
    unfold exit_model.
    eapply implMG_bind with (Q1 := fun _ _ RNG' ms' => rng_aimg RNG' /\
                 exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F' fc' m',
                 ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET_A) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F' (Z_to_bv 64 STDIO_EXIT_RET_A) fc' None m' (seg_rom asegs)).
    - (* [comment removed for export] *)
      apply implMG_from_evtF.
      eapply evtF_cut.
      { eapply (aexit_prefix_spec PRE MW MDTOR MW_low PRE_frame RNG) with (lo := lo) (code := code) (t := t) (reg := reg);
          [exact HPRE | exact ST | exact EC | exact MI | reflexivity | reflexivity | unfold MDTOR_DEPTH; lia | exact LOLO | exact RSTK | exact RIMG | exact RISH | exact RTLS]. }
      cbv beta. intros ms' PO. unfold aexit_prefix_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MU WM MI' ST' FR; nd_post).
      apply evtF_done. eapply implMG_mono.
      { eapply stdio_exit_spec with (lo := lo);
          [ rewrite unsigned_lit by lia; exact ST'
          | eapply SX_frame; [exact HSX | | exact MU | exact WM]; unfold MDTOR_DEPTH; lia
          | exact MI' | rewrite unsigned_lit by lia; lia | exact LOLO | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; clear - ALN; Z.div_mod_to_equations; lia | reflexivity
          | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH | exact RTLS ]. }
      cbv beta. intros [] s' RNG' ms' PO. unfold stdio_exit_post in PO. destruct_exs PO. destruct PO as (-> & RI').
      split; [exact RI'|].
      replace (ret_pc (Z_to_bv 64 STDIO_EXIT_RET_A)) with (Z_to_bv 64 STDIO_EXIT_RET_A) by (symmetry; apply ret_pc_even; [unfold STDIO_EXIT_RET_A; lia|reflexivity]).
      repeat eexists; cbv delta [mkR]; reflexivity.
    - (* [comment removed for export] *)
      intros [] s' RNG' ms' (RI' & PO). destruct_exs PO. subst ms'. unfold STDIO_EXIT_RET_A.
      apply implMG_sys; [exact I|]. do 4 zstep. step_ecall.
      split; [ at_nodeA_solve | intros rsp a HH; cbn in HH; discriminate HH ].
  Qed.
  End Zd2.
  #[using="MW MDTOR MW_low PRE_frame stdio_exit_frame_nonneg SX_frame stdio_exit_spec"] Lemma exit_specA : ltac:(let t := eval cbv delta [exit_specA__stmt] in exit_specA__stmt in exact t).
  Proof. exact exit_specA__body. Qed.
End ExitProof.
End CANSEC1.
End TwB.
End ExitA.

(* [comment removed for export] *)
Module DrvFactsA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section DrvFacts.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Variables (USP : Z) (SB : list byte).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SB.
  #[local] Abbreviation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA USP SB GL GD"] Lemma drv_lit_mobjA : forall L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> rng_aimg RNG -> rng_aimg_sh RNG ->
    0x10040 <= A -> A + n <= DRV_RODATA_HI -> 0 <= n -> mobjA RNG m A n.
  Proof.
    intros L RNG s CL FB FL m A n G RI RS HA HB Hn. destruct (gd_unp _ _ _ GD _ _ _ _ _ _ _ G) as [U _].
    destruct (gl_globals _ _ _ GL _ _ _ _ _ _ _ G) as [W _]. unfold DRV_RODATA_LO, DRV_RODATA_HI in *.
    apply static_mobjA; [lia | lia | lia | eapply unpoisoned_sub; [exact U| lia| lia] | exact W | exact RI | exact RS].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma drv_stack_writes : forall L RNG s CL FB m m' W SP, GIOA L RNG s CL FB [] m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
    GIOA L RNG s CL FB [] m' /\ agrees_on (client_keeps [] CL SP) m m'.
  Proof.
    intros L RNG s CL FB m m' W SP G MU WM HW HSP. split.
    - eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM |].
      eapply Forall_impl; [| exact HW]. intros iv [A _]. left. exact A.
    - rewrite <- (app_nil_r CL) in G.
      eapply (gl_keeps _ _ _ GL L RNG s CL [] FB [] [] m m' W SP); [exact G | exact MU | exact WM | | exact HSP].
      eapply Forall_impl; [| exact HW]. intros iv A. left. exact A.
  Qed.

  (* [comment removed for export] *)
  Definition drv_w (CLo : list cblk) (SP : Z) (iv : Z * Z) : Prop :=
    (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block CLo iv \/ rs_iv iv
    \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160)
    \/ ((DRV_INIT_FLAG <= fst iv /\ snd iv <= DRV_INIT_FLAG + 8) \/ (ATX <= fst iv /\ snd iv <= ATX + 544)).   (* [comment removed for export] *)

  #[using="Type"] Lemma outside_Forall : forall (W : list (Z * Z)) a, Forall (fun iv => ~ (fst iv <= a < snd iv)) W -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a HF; [exact I|]. apply Forall_cons_iff in HF as [H1 H2]. cbn [outside fst snd] in *. split; [exact H1| apply IH; exact H2].
  Qed.

  #[using="FO fflagA GL"] Lemma drv_keeps : forall L RNG s (CLo CL FB : list cblk) m m' W SP,
    GIOA L RNG s (CLo ++ CL) FB [] m -> munch W m m' -> wmono asegs m m' ->
    Forall (drv_w CLo SP) W -> ATOP + 4096 <= SP ->
    agrees_on (client_keeps [] CL SP) m m'.
  Proof.
    intros L RNG s CLo CL FB m m' W SP G MU WM HW HSP.
    eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha HK. apply outside_Forall.
    eapply Forall_impl; [| exact HW]. intros iv HIV. cbv beta. intros Hin.
    pose proof atp_below_atop as TBA. atop_facts. unfold drv_w, rs_iv in HIV. unfold ATP in *.
    assert (BLK : forall b, In b (CLo ++ CL) -> AIMG_HI <= cb_addr b /\ cb_addr b + cb_size b <= ATOP).
    { intros b Hb. destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((BAND & _ & TOP & _) & _).
      apply ablk_lin in BAND. lia. }
    unfold client_keeps in HK. destruct HK as [HK|[HK|[HK|HK]]].
    - (* [comment removed for export] *)
      destruct HIV as [[A1 A2]|[HIV|[[A1 A2]|[[A1 A2]|[[A1 A2]|[A1 A2]]]]]]; unfold READ_STAGE, DRV_INIT_FLAG, ATX in *; try lia.
      unfold iv_in_block in HIV. apply Exists_exists in HIV as (b & Hb & B1 & B2).
      destruct (BLK b ltac:(apply in_or_app; left; exact Hb)) as [_ T]. lia.
    - (* [comment removed for export] *)
      apply in_block_In in HK as (c & Hc & C1).
      destruct (BLK c ltac:(apply in_or_app; right; exact Hc)) as [CI CT]. unfold AIMG_HI in CI.
      destruct HIV as [[A1 A2]|[HIV|[[A1 A2]|[[A1 A2]|[[A1 A2]|[A1 A2]]]]]]; unfold READ_STAGE, DRV_INIT_FLAG, ATX in *; try lia.
      + unfold iv_in_block in HIV. apply Exists_exists in HIV as (b & Hb & B1 & B2).
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as AP. apply blocks_apart_app_inv in AP as (AP & _ & _).
        apply blocks_apart_app_inv in AP as (_ & _ & AP2). specialize (AP2 b c Hb Hc). unfold apart in AP2. lia.
      + apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G); [left; apply in_block_app; left; apply in_block_app; right; apply in_block_In; exists c; split; [exact Hc| lia] | unfold ATP; lia].
    - unfold in_frames in HK. inversion HK.
    - unfold in_frame_sh in HK. inversion HK.
  Qed.

  (* [comment removed for export] *)
  Definition data_loc (CL : list cblk) (D : Z) (data : list byte) : Prop :=
    (data = [] /\ 0x10040 <= D /\ D <= 0x602fc0) \/ exists b, In b CL /\ (cb_addr b <= D /\ D + Z.of_nat (length data) <= cb_addr b + cb_size b).   (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma data_loc_cobjA : forall L RNG s CL FB m D data, GIOA L RNG s CL FB [] m -> data_loc CL D data ->
    (data = [] /\ 0x10040 <= D /\ D <= 0x602fc0) \/ cobjA RNG m [] CL D (Z.of_nat (length data)).
  Proof.
    intros L RNG s CL FB m D data G [E|(b & Hb & H1 & H2)]; [left; exact E| right].
    split; [left; exists b; split; [exact Hb| lia]|].
    eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G| apply in_or_app; left; exact Hb] | lia | lia | lia].
  Qed.
  #[using="Type"] Lemma data_loc_keeps : forall (CL : list cblk) D data a, data_loc CL D data -> D <= a < D + Z.of_nat (length data) -> in_block CL a.
  Proof.
    intros CL D data a [(-> & _)|(b & Hb & H1 & H2)] Ha; [cbn in Ha; lia|].
    apply in_block_In. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma block_mobjA : forall L RNG s CL FB m A n, GIOA L RNG s CL FB [] m ->
    (exists b, In b CL /\ cb_addr b <= A /\ A + n <= cb_addr b + cb_size b) -> 0 <= n -> mobjA RNG m A n /\ A + n <= ATOP /\ AIMG_HI <= A.
  Proof.
    intros L RNG s CL FB m A n G (b & Hb & H1 & H2) Hn.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as BA.
    pose proof BA as ((BAND & _ & TOP & _) & _). apply ablk_lin in BAND.
    split; [apply aobjA_mobjA; [eapply blockA_aobj; [exact BA| lia| lia| lia]| lia]| lia].
  Qed.
End DrvFacts.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section DrvFacts.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Variables (USP : Z) (SB : list byte).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SB.
  #[local] Abbreviation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA USP SB GL GD"] Lemma drv_lit_mobjA : forall L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> rng_aimg RNG -> rng_aimg_sh RNG ->
    0x10040 <= A -> A + n <= DRV_RODATA_HI -> 0 <= n -> mobjA RNG m A n.
  Proof.
    intros L RNG s CL FB FL m A n G RI RS HA HB Hn. destruct (gd_unp _ _ _ GD _ _ _ _ _ _ _ G) as [U _].
    destruct (gl_globals _ _ _ GL _ _ _ _ _ _ _ G) as [W _]. unfold DRV_RODATA_LO, DRV_RODATA_HI in *.
    apply static_mobjA; [lia | lia | lia | eapply unpoisoned_sub; [exact U| lia| lia] | exact W | exact RI | exact RS].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma drv_stack_writes : forall L RNG s CL FB m m' W SP, GIOA L RNG s CL FB [] m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
    GIOA L RNG s CL FB [] m' /\ agrees_on (client_keeps [] CL SP) m m'.
  Proof.
    intros L RNG s CL FB m m' W SP G MU WM HW HSP. split.
    - eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM |].
      eapply Forall_impl; [| exact HW]. intros iv [A _]. left. exact A.
    - rewrite <- (app_nil_r CL) in G.
      eapply (gl_keeps _ _ _ GL L RNG s CL [] FB [] [] m m' W SP); [exact G | exact MU | exact WM | | exact HSP].
      eapply Forall_impl; [| exact HW]. intros iv A. left. exact A.
  Qed.

  (* [comment removed for export] *)
  Definition drv_w (CLo : list cblk) (SP : Z) (iv : Z * Z) : Prop :=
    (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block CLo iv \/ rs_iv iv
    \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160)
    \/ ((DRV_INIT_FLAG <= fst iv /\ snd iv <= DRV_INIT_FLAG + 8) \/ (ATX <= fst iv /\ snd iv <= ATX + 544)).   (* [comment removed for export] *)

  #[using="Type"] Lemma outside_Forall : forall (W : list (Z * Z)) a, Forall (fun iv => ~ (fst iv <= a < snd iv)) W -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a HF; [exact I|]. apply Forall_cons_iff in HF as [H1 H2]. cbn [outside fst snd] in *. split; [exact H1| apply IH; exact H2].
  Qed.

  #[using="FO fflagA GL"] Lemma drv_keeps : forall L RNG s (CLo CL FB : list cblk) m m' W SP,
    GIOA L RNG s (CLo ++ CL) FB [] m -> munch W m m' -> wmono asegs m m' ->
    Forall (drv_w CLo SP) W -> ATOP + 4096 <= SP ->
    agrees_on (client_keeps [] CL SP) m m'.
  Proof.
    intros L RNG s CLo CL FB m m' W SP G MU WM HW HSP.
    eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha HK. apply outside_Forall.
    eapply Forall_impl; [| exact HW]. intros iv HIV. cbv beta. intros Hin.
    pose proof atp_below_atop as TBA. atop_facts. unfold drv_w, rs_iv in HIV. unfold ATP in *.
    assert (BLK : forall b, In b (CLo ++ CL) -> AIMG_HI <= cb_addr b /\ cb_addr b + cb_size b <= ATOP).
    { intros b Hb. destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((BAND & _ & TOP & _) & _).
      apply ablk_lin in BAND. lia. }
    unfold client_keeps in HK. destruct HK as [HK|[HK|[HK|HK]]].
    - (* [comment removed for export] *)
      destruct HIV as [[A1 A2]|[HIV|[[A1 A2]|[[A1 A2]|[[A1 A2]|[A1 A2]]]]]]; unfold READ_STAGE, DRV_INIT_FLAG, ATX in *; try lia.
      unfold iv_in_block in HIV. apply Exists_exists in HIV as (b & Hb & B1 & B2).
      destruct (BLK b ltac:(apply in_or_app; left; exact Hb)) as [_ T]. lia.
    - (* [comment removed for export] *)
      apply in_block_In in HK as (c & Hc & C1).
      destruct (BLK c ltac:(apply in_or_app; right; exact Hc)) as [CI CT]. unfold AIMG_HI in CI.
      destruct HIV as [[A1 A2]|[HIV|[[A1 A2]|[[A1 A2]|[[A1 A2]|[A1 A2]]]]]]; unfold READ_STAGE, DRV_INIT_FLAG, ATX in *; try lia.
      + unfold iv_in_block in HIV. apply Exists_exists in HIV as (b & Hb & B1 & B2).
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as AP. apply blocks_apart_app_inv in AP as (AP & _ & _).
        apply blocks_apart_app_inv in AP as (_ & _ & AP2). specialize (AP2 b c Hb Hc). unfold apart in AP2. lia.
      + apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G); [left; apply in_block_app; left; apply in_block_app; right; apply in_block_In; exists c; split; [exact Hc| lia] | unfold ATP; lia].
    - unfold in_frames in HK. inversion HK.
    - unfold in_frame_sh in HK. inversion HK.
  Qed.

  (* [comment removed for export] *)
  Definition data_loc (CL : list cblk) (D : Z) (data : list byte) : Prop :=
    (data = [] /\ 0x10040 <= D /\ D <= 0x603fc0) \/ exists b, In b CL /\ (cb_addr b <= D /\ D + Z.of_nat (length data) <= cb_addr b + cb_size b).   (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma data_loc_cobjA : forall L RNG s CL FB m D data, GIOA L RNG s CL FB [] m -> data_loc CL D data ->
    (data = [] /\ 0x10040 <= D /\ D <= 0x603fc0) \/ cobjA RNG m [] CL D (Z.of_nat (length data)).
  Proof.
    intros L RNG s CL FB m D data G [E|(b & Hb & H1 & H2)]; [left; exact E| right].
    split; [left; exists b; split; [exact Hb| lia]|].
    eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G| apply in_or_app; left; exact Hb] | lia | lia | lia].
  Qed.
  #[using="Type"] Lemma data_loc_keeps : forall (CL : list cblk) D data a, data_loc CL D data -> D <= a < D + Z.of_nat (length data) -> in_block CL a.
  Proof.
    intros CL D data a [(-> & _)|(b & Hb & H1 & H2)] Ha; [cbn in Ha; lia|].
    apply in_block_In. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma block_mobjA : forall L RNG s CL FB m A n, GIOA L RNG s CL FB [] m ->
    (exists b, In b CL /\ cb_addr b <= A /\ A + n <= cb_addr b + cb_size b) -> 0 <= n -> mobjA RNG m A n /\ A + n <= ATOP /\ AIMG_HI <= A.
  Proof.
    intros L RNG s CL FB m A n G (b & Hb & H1 & H2) Hn.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as BA.
    pose proof BA as ((BAND & _ & TOP & _) & _). apply ablk_lin in BAND.
    split; [apply aobjA_mobjA; [eapply blockA_aobj; [exact BA| lia| lia| lia]| lia]| lia].
  Qed.
End DrvFacts.
End CANSEC1.
End TwB.
End DrvFactsA.
