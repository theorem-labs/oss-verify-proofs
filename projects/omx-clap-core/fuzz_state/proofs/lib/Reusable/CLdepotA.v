(* copied from proofs/cgif/cgif_file_fuzzer/lib/CLdepotA.v @ 86aa4177b94 (a working branch: F1 / F2 + NMAX-PARAM + EV_MAX value-independence; installs in c5 ~18:30Z), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* CLdepot's depot field over an abstract trace admissibility [adm], image-free.

   CLdepot.depot_field_ok derives the interfaces' depot field (CLdepot.depot_field: AGif0n.if_depot / if_depot_miss,
   AGif4.ifs_depot, DGif0.di_depot) from the released machine-level depot contract.  CLdepot fixes that contract's trace
   premise to cgif_file's [In tr (as_universe B)] (CLdepot.depot_spec_x, CLdepot.v:98) and the sub-interface's
   [ds_univ] to give it (CLdepot.v:76).  An instance whose released contract admits a trace by another fact cannot use
   CLdepot: fuzz_state's AFl0.tfib_depot_spec takes [areq_ok S (KDepot tr)] (the trace length, YG01.v:35), and its
   trace premise tr_admit gives that by YG01.tr_admit_len, not [In tr (as_universe B)].

   This file states the same contract, sub-interface and theorem over a Variable [adm : astate -> list Z -> Prop] in
   place of [fun _ tr => In tr (as_universe B)], and concludes CLdepot.depot_field itself, so the field an instance
   gets is the field the interfaces state.  CLdepot.v is unchanged.  cgif_file's instance is
   [adm := fun _ tr => In tr (as_universe B)] ([depot_sub_a_of], [depot_spec_xa_of]); fuzz_state's is
   [adm := fun S tr => areq_ok S (KDepot tr)], where AFl0.tfib_depot_spec is [depot_spec_xa] by conversion. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import CLdepot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section b.
(* The image, the relation, the trace premise and the zones: CLdepot's section variables. *)
Variable segs : list Segment.
Variable A_DEP : Z.
Variable TPv : Z.
Variable IMGC : alayout -> Prop.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable U : list Z -> astate -> Prop.
Variable DZ : alayout -> Z -> Prop.
Variable KEEP : alayout -> Z -> Prop.
(* The released contract's trace admissibility at the call's state. *)
Variable adm : astate -> list Z -> Prop.

(* CLdepot.DepotSub with [ds_univ] giving [adm S tr]. *)
Record DepotSubA : Prop := {
  dsa_view : forall inst ly S W mem md, ARX inst ly S W mem md -> layout_ok ly /\ IMGC ly /\ Wf (as_universe B) S;
  (* the trace premise of the consumer gives the released contract's admissibility *)
  dsa_adm : forall inst ly S W mem md tr, ARX inst ly S W mem md -> U tr S -> adm S tr;
  dsa_keep : forall inst ly S W mem0 md0 (mem : word -> option byte),
    ARX inst ly S W mem0 md0 -> (forall x : word, KEEP ly (bv_unsigned x) -> mem x = mem0 x) ->
    Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly) /\
    depot_mem_ok B ly S (aview segs (w_H W) mem);
  dsa_fp : forall inst ly S W mem md a, ARX inst ly S W mem md -> depot_footprint B ly a -> DZ ly a
}.

(* CLdepot.depot_spec_x with [adm S tr] in place of [In tr (as_universe B)]. *)
Definition depot_spec_xa : Prop :=
forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (buf : Z) (tr : list Z),
let H := w_H W in let rd := aview segs H mem in let sp := bv_unsigned (getr regs 2) in
layout_ok ly -> IMGC ly -> Wf (as_universe B) S -> adm S tr ->
Forall (cell_holds B ly rd) (as_const B ly) -> depot_mem_ok B ly S rd ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TPv -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict H mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
SRr segs W (mkCfg (mkst regs (Z_to_bv 64 A_DEP) mem (seg_rom segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
aok S (KDepot tr) z /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
depot_mem_ok B ly (depot_after z tr S) (aview segs H mem') /\
Forall (cell_holds B ly (aview segs H mem')) (as_const B ly)).

(* CLdepot.depot_field_ok's script, with [dsa_adm] in place of [ds_univ]. *)
Theorem depot_field_ok_a : DepotSubA -> depot_spec_xa -> depot_field segs A_DEP TPv B ARX U DZ KEEP.
Proof.
intros SUB HD1 inst ly S W mem0 md0 tr regs mem md buf HARX HU MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
destruct (dsa_view SUB inst ly S W mem0 md0 HARX) as (LY & IMG & WF).
pose proof (dsa_adm SUB inst ly S W mem0 md0 tr HARX HU) as Htr.
destruct (dsa_keep SUB inst ly S W mem0 md0 mem HARX MEQ) as [CST DEP].
eapply SRr_mono.
{ exact (HD1 W ly S regs mem md buf tr LY IMG WF Htr CST DEP R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES). }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [reflexivity|]. split; [exact RP|].
split; [|split; [exact PR' | exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [exact N1|].
intros FP. apply N2. exact (dsa_fp SUB inst ly S W mem0 md0 (bv_unsigned x) HARX FP).
Qed.
End b.

(* cgif_file's admissibility: CLdepot's sub-interface and contract are the [In tr (as_universe B)] instance. *)
Lemma depot_sub_a_of : forall segs IMGC B ARX U DZ KEEP,
  DepotSub segs IMGC B ARX U DZ KEEP ->
  DepotSubA segs IMGC B ARX U DZ KEEP (fun _ tr => In tr (as_universe B)).
Proof.
intros segs IMGC B ARX U DZ KEEP [V UN K F]. exact (Build_DepotSubA segs IMGC B ARX U DZ KEEP _ V UN K F).
Qed.
Lemma depot_spec_xa_of : forall segs A_DEP TPv IMGC B,
  depot_spec_x segs A_DEP TPv IMGC B -> depot_spec_xa segs A_DEP TPv IMGC B (fun _ tr => In tr (as_universe B)).
Proof. intros segs A_DEP TPv IMGC B H. exact H. Qed.
End a.
