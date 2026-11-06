(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q3bI QU0c.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QWTC QgpE Q3bI QU0c.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

Lemma at_0 : forall base, at_ base 0 = base.
Proof.
intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
intros base d e. unfold at_, v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.

Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
forall x, ~ W x -> m' x = m x.

Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

Lemma regs_agree_trans : forall C regs1 regs2 regs3,
regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma regs_agree_mono : forall (C C' : regset) regs regs',
(forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
intros C regs regs' r v Hin H s Hs.
rewrite getr_other by (intro Heq; subst; contradiction).
apply H, Hs.
Qed.

Definition triple (segs : list Segment)
(C : regset) (W : memset)
(P : assn) (a b : word) (Q : assn) : Prop :=
forall regs mem rom, P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
/\ Q regs' mem' rom
/\ regs_agree C regs regs'
/\ mem_agree W mem mem'.

Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
forall regs mem rom regs' mem',
regs_agree C regs regs' -> mem_agree W mem mem' ->
R regs mem rom -> R regs' mem' rom.

Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
intros z Hz.
assert (Hl : Z.land z 1 = 0%Z).
{ replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
replace (-2)%Z with (Z.lnot 1) by reflexivity.
rewrite <- Z.ldiff_land.
rewrite <- (Z.lor_ldiff_and z 1) at 2.
rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
rewrite Z.add_0_r, land_m2_even by exact Hk.
apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Definition proc (segs : list Segment) (C : regset) (W : memset)
(P : assn) (entry : word) (Q : assn) : Prop :=
forall k : word, ret_ok k ->
triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

Definition ra_indep (P : assn) : Prop :=
forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

End WithFP1.

End Mq0.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQny QWTC Q3bI QgpE QU0c.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

End WithFP1.
End Mq1.
From LinuxProcessSemantics.EquivalenceDefinition Require OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.
Import QWXq.Mq2 QQny Q3bI QWTC QU0c QgpE.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.

Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k) ->
to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
(1 <= length rest)%nat ->
to_wall ms rest k ->
to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wall_tail ms' rest k ->
to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

Lemma msteps_to_wall_tail : forall ms ms' rest k,
msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
intros ms ms' rest k H; induction H; [auto|].
intro Hw. eapply twt_step; eauto.
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
(ms : machine_state) : Prop :=
match bufs with
| [] => to_wexit segs ms [] code
| buf :: rest =>
(1 <= length buf)%nat /\
to_wall_tail ms buf (to_wallexit rest code)
end.

Lemma twe_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hsvc Hstep Hw.
destruct bufs as [|buf rest].
- eapply tw_step; eauto.
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply twt_step; eauto.
Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
- exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply msteps_to_wall_tail; eauto.
Qed.

End WithSegsCh.

Abbreviation wexit1 segs ms bufs code :=
(to_wallexit segs (Z_to_bv 64 1) bufs code ms).

End WithFP1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Definition mkstR (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word)
: machine_state :=
{| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := rv; ms_fcsr := Z_to_bv 32 0;
ms_mem := mem; ms_rom := rom |}.

Definition resv_inval_w (rv : option word) (a : word) : option word :=
match rv with
| Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else rv
| None => None
end.

Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
match sz with
| SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
| SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
| SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
| SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
end.

Definition eff_sx (sz : msize) (sx : bool) : bool :=
match sz with SZ8 => false | _ => sx end.

Definition msize_bytes (sz : msize) : nat :=
match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

Definition amo_msize (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_nbytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.

Definition amo_store_bytes (op : amoop) (wd : awidth) (bs : list byte) (src : word) : list byte :=
match wd with
| AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
| AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))
end.

Ltac stepR_pipeline Hfetch Hecall Hdecode :=
unfold mkstR;
step_pipeline Hfetch Hecall Hdecode;
cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
rewrite ?bv_eqb0_is_x0.

Lemma stepR_opimm_gen : forall segs regs pc mem rom rv w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_opimm32_gen : forall segs regs pc mem rom rv w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd rs imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm32_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_lui : forall segs regs pc mem rom rv w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lui rd imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepR_auipc : forall segs regs pc mem rom rv w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Auipc rd imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepR_jal_link : forall segs regs pc mem rom rv w rd (imm : bv 21),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jal rd imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(btgt pc (bv_signed imm)) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_addsext;
reflexivity.
Qed.

Lemma stepR_jalr : forall segs regs pc mem rom rv w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv).
Proof.
intros segs regs pc mem rom rv w rd rs1 imm Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_jalr; reflexivity.
Qed.

Lemma stepR_branch_tk_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = true ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR regs (btgt pc (bv_signed imm)) mem rom rv).
Proof.
intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.

Lemma stepR_branch_ft_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = false ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fence : forall segs regs pc mem rom rv w a b c d e,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fence a b c d e, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w a b c d e Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma stepR_fencei : forall segs regs pc mem rom rv w a b c,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (FenceI a b c, 4%Z) ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w a b c Hfetch Hecall Hdecode.
stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma stepR_load : forall segs regs pc mem rom rv w sz sx rd rs (imm : bv 12) bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
(v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma stepR_store : forall segs regs pc mem rom rv w sz (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = true ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom
(resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))).
Proof.
intros segs regs pc mem rom rv w sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
assert (Hsb : forall u : word,
Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
{ intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_wrap. lia. }
stepR_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite !b_addsext.
destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
rewrite Hok; cbv beta iota;
rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc4;
(destruct rv as [r|]; cbv beta iota; [|reflexivity]);
unfold resv_inval_w;
match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

Lemma stepR_lr : forall segs regs pc mem rom rv w wd aq rl rd rs bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
(bv_unsigned (getr regs rs) mod amo_bytes wd = 0)%Z ->
rdn segs mem (getr regs rs) (amo_nbytes wd) = Some bs ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
(v_addi pc 4) mem rom (Some (getr regs rs))).
Proof.
intros segs regs pc mem rom rv w wd aq rl rd rs bs Hfetch Hecall Hdecode Hal Hread.
stepR_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
unfold amo_bytes in Hal.
destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
rewrite b_npc4; unfold regupd;
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma stepR_sc_ok : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
r = getr regs rs1 ->
RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
RiscvSemantics.step segs (mkstR regs pc mem rom (Some r)) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
(wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom None).
Proof.
intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
stepR_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
unfold amo_bytes in Hal.
destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
subst r; rewrite Z.eqb_refl; cbv beta iota;
cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
unfold regupd, word_to_le_bytes;
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma stepR_amo : forall segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
rdn segs mem (getr regs rs1) (amo_nbytes wd) = Some bs ->
RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
(v_addi pc 4)
(wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
rom (resv_inval_w rv (getr regs rs1))).
Proof.
intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
stepR_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
unfold amo_bytes in Hal.
destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
rewrite Hok; cbv beta iota;
rewrite write_to_mem_wbytes, b_npc4; unfold regupd, amo_store_bytes;
(destruct rv as [r|]; cbv beta iota);
unfold resv_inval_w;
try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
