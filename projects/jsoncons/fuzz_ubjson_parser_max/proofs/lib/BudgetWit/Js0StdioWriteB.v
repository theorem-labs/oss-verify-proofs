(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Js0StdioWrite.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: added a channel-reader hypothesis Hrdr passed to the write-step tactics, and unfolded the Section SE blocks for RI_but, finish_b and ref_stdio_write into plain lemmas with #[using] attributes, dropping the TCodec import; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/Src0StdioWriteB.v, lines 66, 496, 550-554. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes LibWritev LibWritevX Frame RefMemcpyLib Js0StdioDefs Js0StdioWrite_run1 Js0StdioWrite_run2.
Import ListNotations.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RdnPeelKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0StdioWrite.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import LibWritevXB SpinAlgB.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
| |- _ => rdn_hyp
end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Section FPX_1.
Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Lemma rz_emit_nil_b : (forall (c : (@LinuxProcessSemantics.LinuxProcessSem.Run.config)), (forall (K : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.TSet)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg c K)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg c (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event)) K))))).
Proof.
intros c K H. eapply SpinAlgB.rzb_conseq; [exact H|].
apply t_eq_sym. apply t_emit_nil_eq. exact (SpinAlgB.rzb_nonempty _ _ _ _ H).
Qed.
#[using="Type"] Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
(k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.
#[using="Type"] Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
(length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.
#[using="Type"] Lemma u_at_le : (forall (b : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (k : (@Corelib.Numbers.BinNums.Z)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le Z0 k)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b) k) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 64%positive)))), (@Corelib.Init.Logic.or (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare.at_ b k)) (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b) k)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare.at_ b k)) Z0) (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b) k) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 64%positive))))))))).
Proof.
intros b k Hk Hle. unfold at_. pose proof (u64_range b).
destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
- right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
- left. u_norm. reflexivity.
Qed.
Section Loop.
Variables (su f fd : Z) (l bufp bufsz can ret : word).
Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
Variable mem1 : word -> option byte.
Variable model : Model.
Variable K : TSet.
Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
Hypothesis SUhi : (su <= 0x800000000000)%Z.
Hypothesis Flo : (0xb5000 <= f)%Z.
Hypothesis Fhi : (f + 232 <= 0xe7ed0)%Z.
Hypothesis FD : (0 < fd < 2147483648)%Z.
Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Hypothesis Hrdr : m_channel_reader model = true.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hret : ret_ok ret.
Hypothesis HKnil : K [].
Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
Hypothesis M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xe7ed0) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
Hypothesis HK_b : forall regs' m,
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = e8 -> getr regs' 9 = e9 ->
getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
(Js0StdioWrite.LM su mem1) m ->
SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.
#[using="Type"] Lemma RI_but : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (regs' : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (_ : ((Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run2.sw_regs_but regs regs')), ((Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs'))))).
Proof.
intros regs regs'.
intros (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
(P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
unfold Js0StdioWrite.RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
Qed.
#[using="Type"] Lemma LM_rdn : (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (a : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (bs : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem1 a n) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) bs))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) a) (@Stdlib.ZArith.BinInt.Z.of_nat n)) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 64%positive)))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) a) (@Stdlib.ZArith.BinInt.Z.of_nat n)) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 104%positive))) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 72%positive)) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) a)))), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m a n) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) bs)))))))))).
Proof.
intros m a n bs [E G] H Hnw D.
rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
intros x Hx. apply E. lia.
Qed.
#[using="Type"] Lemma LM_store_ok : (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (a : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem1 a n) (@Corelib.Init.Datatypes.true))), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m a n) (@Corelib.Init.Datatypes.true))))))).
Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.
#[using="SUlo SUhi"] Lemma LM_wbytes8 : (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (a : (@Corelib.Numbers.BinNums.Z)), (forall (v : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 104%positive)) a)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add a (Zpos 8%positive)) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 72%positive)))), ((Js0StdioWrite.LM su mem1) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec.wbytes m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) a) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat v))))))))).
Proof.
intros m a v [E G] Hlo Hhi. split.
- intros x Hx. rewrite wbytes_outside.
+ apply E, Hx.
+ unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+ rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK_b"] Lemma finish_b : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (_ : ((Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs)), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646348%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) m (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) K))))).
Proof.
intros regs m.
intros RIr LMm.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
try assumption.
all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
apply HK_b; try assumption.
- rewrite Q23; exact R23.
- rewrite Q24; exact R24.
- rewrite Q25; exact R25.
- rewrite Q26; exact R26.
- rewrite Q27; exact R27.
- rewrite Q3; exact R3.
- rewrite Q4; exact R4.
Qed.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK_b"] Lemma finish_nil_b : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (_ : ((Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs)), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646348%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) m (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event)) K)))))).
Proof. intros. apply rz_emit_nil_b. apply finish_b; assumption. Qed.
#[using="Type"] Lemma pc_9dcfc : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.v_addi ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646472%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) (Zpos 4%positive)) ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646476%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive)))).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK_b"] Lemma loop1_b : (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (k : (@Corelib.Init.Datatypes.nat)), (forall (b : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bs : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (_ : (@Corelib.Init.Peano.le (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs) n)), (forall (_ : ((Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs)), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 10%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.of_nat k)))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 22%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 18%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 1%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 19%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 88%positive))))), (forall (_ : (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat k) (@Corelib.Init.Peano.lt k (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 88%positive))) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 80%positive))) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs))))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem1 b (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) bs))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs))) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs))) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs)) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 30%positive)))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646488%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) m (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv (Npos 8%positive)) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) fd)) (@Corelib.Lists.ListDef.skipn (@stdpp.bitvector.definitions.bv (Npos 8%positive)) k bs)) K)))))))))))))))))))))).
Proof.
induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b) as Hb.
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
(Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : (Js0StdioWrite.LM su mem1) m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : (Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs1) by (eapply RI_but; [exact RIr' | exact QB]).
eapply (LibWritevXB.rz_writev1_wallX_b RSEGS scfg regs1 (0x9dd48 : word) m' model (ltac:(oW' 0x9dd48%Z)) fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
[ exact (ltac:(oF' 0x9dd48%Z)) | exact (ltac:(oE' 0x9dd48%Z)) | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
- subst m'. rdn_solve.
- subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
- rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
- unfold TASK_SIZE. u_norm. lia.
- unfold TASK_SIZE. u_norm. lia.
- u_norm. lia.
- u_norm. lia.
-
intros k' K1 K2. rewrite pc_9dcfc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
+
destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
apply finish_nil_b; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
* rewrite length_skipn. lia.
* eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* exact LMm'.
* exact P10.
* rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
* rewrite P18. gres. exact Q18.
* rewrite P19. gres. exact Q20.
* rewrite length_skipn. lia.
* subst m'. unfold at_. rdn_solve.
* subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
* rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
* unfold at_. rewrite length_skipn. u_norm. lia.
* unfold at_. rewrite length_skipn. u_norm. lia.
* rewrite length_skipn. lia.
Qed.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK_b"] Lemma loop2_b : (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (k : (@Corelib.Init.Datatypes.nat)), (forall (b0 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bs0 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (b1 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bs1 : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (_ : (@Corelib.Init.Peano.le (@Corelib.Init.Nat.add (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0) (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1)) n)), (forall (_ : ((Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs)), (forall (_ : ((Js0StdioWrite.LM su mem1) m)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 10%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.of_nat k)))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 22%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.add (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0)) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1)))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 18%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 2%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 19%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 104%positive))))), (forall (_ : (@Corelib.Init.Logic.and (@Corelib.Init.Peano.le 1%nat k) (@Corelib.Init.Peano.lt k (@Corelib.Init.Nat.add (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0) (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 104%positive))) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b0)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 96%positive))) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0))))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 88%positive))) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat b1)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) m (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 80%positive))) 8%nat) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes 8%nat (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1))))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem1 b0 (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) bs0))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem1 b1 (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) bs1))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b0) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0))) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b0)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b0) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0))) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b1) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1))) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b1)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) b1) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1))) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0)) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs1))) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 30%positive)))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646488%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) m (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv (Npos 8%positive)) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) fd)) (@Corelib.Lists.ListDef.skipn (@stdpp.bitvector.definitions.bv (Npos 8%positive)) k (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv (Npos 8%positive)) bs0 bs1))) K))))))))))))))))))))))))))))).
Proof.
induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
-
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : (Js0StdioWrite.LM su mem1) m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : (Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_le k bs0 bs1 LE).
eapply (LibWritevXB.rz_writev2_wallX_b RSEGS scfg regs1 (0x9dd48 : word) m' model (ltac:(oW' 0x9dd48%Z)) fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
[ exact (ltac:(oF' 0x9dd48%Z)) | exact (ltac:(oE' 0x9dd48%Z)) | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
+ subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
{ replace (length bs0 - k)%nat with 0%nat by lia.
rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
+ rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
subst m'. repeat rdn_peel1.
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' K1 K2. rewrite pc_9dcfc. rewrite length_app, length_skipn in K2.
destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
apply finish_nil_b; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
-- subst m'. repeat rdn_peel1. exact Mb1.
-- subst m'. repeat rdn_peel1. exact Mn1.
-- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
-- exact Bbs1.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- exact DISJ1.
-- exact NW1.
-- rewrite length_skipn. lia.
-
destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs1))
(Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
{ replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : (Js0StdioWrite.LM su mem1) m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : (Js0StdioWrite.RI su f l g3 g4 g23 g24 g25 g26 g27) regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_ge k bs0 bs1) by lia.
eapply (LibWritevXB.rz_writev1_wallX_b RSEGS scfg regs1 (0x9dd48 : word) m' model (ltac:(oW' 0x9dd48%Z)) fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
(Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
(skipn (k - length bs0) bs1) K);
[ exact (ltac:(oF' 0x9dd48%Z)) | exact (ltac:(oE' 0x9dd48%Z)) | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' K1 K2. rewrite pc_9dcfc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
apply finish_nil_b; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (loop1_b (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
rdn_solve.
-- rewrite length_skipn.
apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- rewrite length_skipn. lia.
Qed.
End Loop.
End FPX_1.
Section FPX_2.
Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Lemma sw_post_of_LM : (forall (mem : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (m : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (su : (@Corelib.Numbers.BinNums.Z)), (forall (f : (@Corelib.Numbers.BinNums.Z)), (forall (ra : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s0 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s1 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s2 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s3 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s4 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s5 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (s6 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (can : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (wb : (@Corelib.Numbers.BinNums.Z)), (forall (n : (@Corelib.Numbers.BinNums.Z)), (forall (s : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (l : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bufp : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bufsz : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (Zpos 4294967296%positive) (Zpos 112%positive)) su)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le su (Zpos 140737488355328%positive))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (Zpos 741376%positive) f)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add f (Zpos 232%positive)) (Zpos 949968%positive))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite.LM su (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run1.mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.sw_post mem su f bufp bufsz (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run2.mem_sw2 m f bufp bufsz)))))))))))))))))))))))))).
Proof.
intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
constructor.
- intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
unfold mem_sw2. do 3 wout1.
rewrite (E x) by lia.
unfold mem_sw1. do 13 wout1. reflexivity.
- unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
eapply mem_grows_trans; [|exact G].
unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
apply mem_grows_refl.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
Qed.
#[using="Type"] Lemma pc_9dc74 : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.v_addi ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646336%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) (Zpos 4%positive)) ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646340%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive)))).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
#[using="Type"] Theorem ref_stdio_write_b : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (mem : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model)), (forall (su : (@Corelib.Numbers.BinNums.Z)), (forall (f : (@Corelib.Numbers.BinNums.Z)), (forall (wb : (@Corelib.Numbers.BinNums.Z)), (forall (wp : (@Corelib.Numbers.BinNums.Z)), (forall (fd : (@Corelib.Numbers.BinNums.Z)), (forall (s : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (l : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bufp : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (bufsz : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (can : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (ret : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (pending : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (extra : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (K : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.TSet)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 2%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) su))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 10%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) f))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 11%positive) (@Corelib.Init.Logic.I))) s)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 12%positive) (@Corelib.Init.Logic.I))) l)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 1%positive) (@Corelib.Init.Logic.I))) ret)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (Zpos 4294967296%positive) (Zpos 112%positive)) su)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le su (Zpos 140737488355328%positive))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) 112%nat) (@Corelib.Init.Datatypes.true))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (Zpos 741376%positive) f)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add f (Zpos 232%positive)) (Zpos 949968%positive))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.sw_file mem f wb wp fd bufp bufsz)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.ssp_cells mem can)), (forall (_ : (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt Z0 fd) (@Stdlib.ZArith.BinInt.Z.lt fd (Zpos 2147483648%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds model) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) fd)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) fd))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader model) (@Corelib.Init.Datatypes.true))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 64%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_halted model) (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv (Npos 64%positive))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy model) (@Corelib.Init.Datatypes.nil (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))))), (forall (_ : (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le Z0 wb) (@Stdlib.ZArith.BinInt.Z.le wb wp))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le wp (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.sub wp wb) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) l) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) extra)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending)) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) extra))) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 30%positive)))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le wp (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su wb))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) s) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) l)) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) s)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) s) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) l)) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) wb) (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) pending))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) mem s (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) extra)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) extra))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare.ret_ok ret)), (forall (_ : (K (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event)))), (forall (_ : (forall (regs' : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (mem' : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 10%positive) (@Corelib.Init.Logic.I))) l)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 2%positive) (@Corelib.Init.Logic.I))) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) su))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 1%positive) (@Corelib.Init.Logic.I))) ret)), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 8%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 8%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 9%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 9%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 18%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 18%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 19%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 19%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 20%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 20%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 21%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 21%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 22%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 22%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 23%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 23%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 24%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 24%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 25%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 25%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 26%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 26%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 27%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 27%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 3%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 3%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs' (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 4%positive) (@Corelib.Init.Logic.I))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.getr regs (@stdpp.bitvector.definitions.BV (Npos 5%positive) (Zpos 4%positive) (@Corelib.Init.Logic.I))))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.sw_post mem su f bufp bufsz mem')), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs' ret mem' (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) K)))))))))))))))))))))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 646200%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) mem (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv (Npos 8%positive)) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) fd)) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending extra)) K))))))))))))))))))))))))))))))))))))))))))))))))).
Proof.
intros regs mem model su f wb wp fd s l bufp bufsz can ret.
intros pending extra K
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hrdr Hh Hlazy WBP WPhi
LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK_b.
pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
pose proof SWF as SWF'. pose proof SSP as SSP'.
destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
{ rewrite <- LENE. symmetry. apply u64_roundtrip'. }
set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
{ subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xe7ed0) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
assert (HK' : forall regs' m,
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
Js0StdioWrite.LM su mem1 m ->
SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
{ intros. apply HK_b. all: try assumption.
eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
match goal with H : Js0StdioWrite.LM _ _ _ |- _ => exact H end. }
pose proof (finish_nil_b scfg su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
pose proof (loop1_b scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
pose proof (loop2_b scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
pose proof (Js0StdioWrite.LM_refl su mem1) as LM1.
destruct (Z.eq_dec wb wp) as [EQ|NEQ].
-
destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
subst wb.
destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
lazymatch goal with |- SpinAlgB.rzb _ _ (mkCfg (mkst _ _ ?M _) _) _ =>
replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
rewrite Z.sub_diag in M96.
assert (RI1 : Js0StdioWrite.RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold Js0StdioWrite.RI. repeat split; assumption. }
destruct extra as [|x0 extra'].
+
cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
eapply (LibWritevXB.rz_writev1_zeroX_b RSEGS scfg regs1 (0x9dcc0 : word) mem1 model (ltac:(oW' 0x9dcc0%Z)) fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
[ exact (ltac:(oF' 0x9dcc0%Z)) | exact (ltac:(oE' 0x9dcc0%Z)) | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; u_norm; lia | ].
{ u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
rewrite pc_9dc74.
destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. exact HlZ. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
eapply (LibWritevXB.rz_writev1_wallX_b RSEGS scfg regs1 (0x9dcc0 : word) mem1 model (ltac:(oW' 0x9dcc0%Z)) fd
(Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
[ exact (ltac:(oF' 0x9dcc0%Z)) | exact (ltac:(oE' 0x9dcc0%Z)) | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
* u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
* unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
* unfold TASK_SIZE. u_norm. lia.
* unfold TASK_SIZE. u_norm. lia.
* cbn [length] in LENE. lia.
* lia.
* intros k K1 K2. rewrite pc_9dc74.
destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
-- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. f_equal. lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(Z.of_nat (length (x0 :: extra'))))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. reflexivity. }
{ lia. }
{ lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
++ exact LM1.
++ exact P10.
++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
++ rewrite P18. gres. exact R18.
++ rewrite P19. gres. exact R19.
++ exact M88.
++ rewrite <- HlZ. exact M80.
++ exact Be.
-
destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
assert (RI1 : Js0StdioWrite.RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold Js0StdioWrite.RI. repeat split; assumption. }
eapply (LibWritevXB.rz_writev2_wallX_b RSEGS scfg regs1 (0x9dcc0 : word) mem1 model (ltac:(oW' 0x9dcc0%Z)) fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
[ exact (ltac:(oF' 0x9dcc0%Z)) | exact (ltac:(oE' 0x9dcc0%Z)) | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
+ u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
+ u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
+ u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
+ rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
+ unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k K1 K2. rewrite pc_9dc74. rewrite length_app in K2.
destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
* destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. f_equal. lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(wp - wb + bv_unsigned l))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact R22. }
{ lia. }
{ lia. }
{ lia. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LM1.
-- exact P10.
-- rewrite P22. gres. rewrite R22. f_equal. lia.
-- rewrite P18. gres. exact R18.
-- rewrite P19. gres. exact R19.
-- exact M104.
-- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
-- exact M88.
-- rewrite <- HlZ. exact M80.
-- exact Bp.
-- exact Be.
-- u_norm. lia.
-- u_norm. lia.
Qed.
End FPX_2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
