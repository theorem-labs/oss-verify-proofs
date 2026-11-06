(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command
   (image B, entry 0x8ce4c), put together: tverbs_receive_spec (lib/B/Prog/verbs_receive_c.v) from the 32 segment
   statements of lib/B/Prog/verbs_receive_iface.v and the record facts RECC and ROIN, which give the entry state's
   vr_ent. Each boundary state of the interface is followed to the return: a state P is done when every run from it
   ends in the statement's post (`vr_K P`); the segments are chained backwards from the epilogue S32 to the prologue
   S01 with SRr_bind (cgif lib/Reusable/YA0n.v), the shape of cgif's cgif_close walk (A/ACh5.v) and of the A twin
   lib/A/Prog/verbs_receive.v.

   B's join graph is not A's. B merges three of A's nine `sup_resp` refusal tails, so there are six refusal stubs
   (0x8d4c4, 0x8d64c, 0x8d68c, 0x8d870, 0x8d884, 0x8d88c) where A has nine, and four reply call sites behind six
   join entries (J1 0x8d3b0 -> the epilogue; JB 0x8d4cc / 0x8d4d0 -> the call after the reply; JA 0x8d55c /
   0x8d6a0 / 0x8d6a4 -> either, by the `ntok = 1` test at 0x8d6b4). The chaining below follows that graph.

   A callee that reaches the printf wrappers returns at some other FP state (apost_baseF), so a boundary predicate
   is used at every FP state (vrP) and the FP relation is PaFx's fxrel: vr_K_segF moves the walk from the FP state
   a segment started at to the one its call returned at, and vr_final_fxr carries the post back. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* cmd_ro_ok holds the four GOT words of cmd_got_ok (CmdRo.v RO_ptr_a6bc8 .. RO_ptr_a6be0, B's slots for A's
   0xa7068 .. 0xa7080) *)
Lemma vri_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. decompose [and] Hb. clear Hb.
unfold cmd_got_ok, aval_mem.
split; [|split; [|split]]; intros k Hk;
[ match goal with H : abytes_atR rd _ RO_ptr_a6bc8 |- _ => rewrite (H k) end
| match goal with H : abytes_atR rd _ RO_ptr_a6bd0 |- _ => rewrite (H k) end
| match goal with H : abytes_atR rd _ RO_ptr_a6bd8 |- _ => rewrite (H k) end
| match goal with H : abytes_atR rd _ RO_ptr_a6be0 |- _ => rewrite (H k) end ];
try (cbn; lia); do 8 (destruct k as [|k]; [reflexivity|]); lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* each segment lemma at every FP state: the walk runs a segment at the FP state it has reached *)
Hypothesis VR01 : forall fx : YK11.FPState, vr_s01_stmt (fx := fx) B MT.
Hypothesis VR02 : forall fx : YK11.FPState, vr_s02_stmt (fx := fx) B MT.
Hypothesis VR03 : forall fx : YK11.FPState, vr_s03_stmt (fx := fx) B MT.
Hypothesis VR04 : forall fx : YK11.FPState, vr_s04_stmt (fx := fx) B MT.
Hypothesis VR05 : forall fx : YK11.FPState, vr_s05_stmt (fx := fx) B MT.
Hypothesis VR06 : forall fx : YK11.FPState, vr_s06_stmt (fx := fx) B MT.
Hypothesis VR07 : forall fx : YK11.FPState, vr_s07_stmt (fx := fx) B MT.
Hypothesis VR08 : forall fx : YK11.FPState, vr_s08_stmt (fx := fx) B MT.
Hypothesis VR09 : forall fx : YK11.FPState, vr_s09_stmt (fx := fx) B MT.
Hypothesis VR10 : forall fx : YK11.FPState, vr_s10_stmt (fx := fx) B MT.
Hypothesis VR11 : forall fx : YK11.FPState, vr_s11_stmt (fx := fx) B MT.
Hypothesis VR12 : forall fx : YK11.FPState, vr_s12_stmt (fx := fx) B MT.
Hypothesis VR13 : forall fx : YK11.FPState, vr_s13_stmt (fx := fx) B MT.
Hypothesis VR14 : forall fx : YK11.FPState, vr_s14_stmt (fx := fx) B MT.
Hypothesis VR15 : forall fx : YK11.FPState, vr_s15_stmt (fx := fx) B MT.
Hypothesis VR16 : forall fx : YK11.FPState, vr_s16_stmt (fx := fx) B MT.
Hypothesis VR17 : forall fx : YK11.FPState, vr_s17_stmt (fx := fx) B MT.
Hypothesis VR18 : forall fx : YK11.FPState, vr_s18_stmt (fx := fx) B MT.
Hypothesis VR19 : forall fx : YK11.FPState, vr_s19_stmt (fx := fx) B MT.
Hypothesis VR20 : forall fx : YK11.FPState, vr_s20_stmt (fx := fx) B MT.
Hypothesis VR21 : forall fx : YK11.FPState, vr_s21_stmt (fx := fx) B MT.
Hypothesis VR22 : forall fx : YK11.FPState, vr_s22_stmt (fx := fx) B MT.
Hypothesis VR23 : forall fx : YK11.FPState, vr_s23_stmt (fx := fx) B MT.
Hypothesis VR24 : forall fx : YK11.FPState, vr_s24_stmt (fx := fx) B MT.
Hypothesis VR25 : forall fx : YK11.FPState, vr_s25_stmt (fx := fx) B MT.
Hypothesis VR26 : forall fx : YK11.FPState, vr_s26_stmt (fx := fx) B MT.
Hypothesis VR27 : forall fx : YK11.FPState, vr_s27_stmt (fx := fx) B MT.
Hypothesis VR28 : forall fx : YK11.FPState, vr_s28_stmt (fx := fx) B MT.
Hypothesis VR29 : forall fx : YK11.FPState, vr_s29_stmt (fx := fx) B MT.
Hypothesis VR30 : forall fx : YK11.FPState, vr_s30_stmt (fx := fx) B MT.
Hypothesis VR31 : forall fx : YK11.FPState, vr_s31_stmt (fx := fx) B MT.
Hypothesis VR32 : forall fx : YK11.FPState, vr_s32_stmt (fx := fx) B MT.

(* a boundary predicate at every FP state *)
Definition vrP : Type := YK11.FPState -> vrE -> world SEGS -> config -> Prop.
Definition vrP_or (P Q : vrP) : vrP := fun fq => vr_or (P fq) (Q fq).

(* the entry facts at a later FP state: only rounding mode 0 names the FP state, and fxrel keeps it *)
Lemma vr_ent_fxr : forall f0 f1 e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hr. revert He. unfold vr_ent. cbv zeta. intros He.
repeat lazymatch type of He with
| _ /\ _ => let H1 := fresh "H" in destruct He as [H1 He]; split; [exact H1|]
end.
exact (fxrel_frm0 f0 f1 He Hr).
Qed.
(* the statement's post at a later FP state gives it at an earlier one: fxrel is transitive *)
Lemma vr_final_fxr : forall f0 f1 e W cf, fxrel f0 f1 ->
vr_final (fx := f1) B MT e W cf -> vr_final (fx := f0) B MT e W cf.
Proof.
intros f0 f1 e W cf (Rr & Cr). unfold vr_final, apost_baseF. cbv zeta.
intros (fx' & ly' & S' & regs' & mem' & md' & Hc & HR & HC & HJ & HP & HQ).
exists fx', ly', S', regs', mem', md'. split; [exact Hc|]. split.
{ intros k Hk. rewrite (HR k Hk). exact (Rr k Hk). }
split; [|exact (conj HJ (conj HP HQ))].
destruct HC as [HC|HC]; [|right; exact HC]. rewrite HC.
destruct Cr as [Cr|Cr]; [left; exact Cr | right; exact Cr].
Qed.

(* a boundary state from which every run, at whatever FP state the walk has reached, ends in the statement's post *)
Definition vr_K (P : vrP) : Prop :=
forall fq e W cf, vr_ent (fx := fq) B MT e -> P fq e W cf -> SRr SEGS W cf (vr_final (fx := fq) B MT e).

Lemma vr_K_seg : forall P Q : vrP, (forall fq, vr_seg (fx := fq) B MT (P fq) (Q fq)) -> vr_K Q -> vr_K P.
Proof.
intros P Q HS HK fq e W cf He HP. eapply SRr_bind; [exact (HS fq e W cf He HP)|].
intros W' cf' _ HQ. exact (HK fq e W' cf' He HQ).
Qed.
Lemma vr_K_segF : forall (P Q : vrP), (forall fq, vr_segF (fx := fq) B MT (P fq) Q) -> vr_K Q -> vr_K P.
Proof.
intros P Q HS HK fq e W cf He HP. eapply SRr_bind; [exact (HS fq e W cf He HP)|].
intros W' cf' _ (fq' & Hr & HQ). eapply SRr_mono; [exact (HK fq' e W' cf' (vr_ent_fxr fq fq' e He Hr) HQ)|].
intros W'' cf'' _ Hf. exact (vr_final_fxr fq fq' e W'' cf'' Hr Hf).
Qed.
Lemma vr_K_or : forall P Q, vr_K P -> vr_K Q -> vr_K (vrP_or P Q).
Proof. intros P Q HP HQ fq e W cf He [H|H]; [exact (HP fq e W cf He H) | exact (HQ fq e W cf He H)]. Qed.

(* the boundary predicates at every FP state *)
Let Pb1 : vrP := fun fq => vr_b1 (fx := fq) B MT.
Let Pb2 : vrP := fun fq => vr_b2 (fx := fq) B MT.
Let Pb3 : vrP := fun fq => vr_b3 (fx := fq) B MT.
Let Pb4e : vrP := fun fq => vr_b4e (fx := fq) B MT.
Let Pb4t : vrP := fun fq => vr_b4t (fx := fq) B MT.
Let Prt (r : VRR.vroute) : vrP := fun fq => vr_atr (fx := fq) B MT r.
Let Ppr (pc : Z) : vrP := fun fq => vr_atpr (fx := fq) B MT pc.
Let Phd (pc : Z) : vrP := fun fq => vr_athd (fx := fq) B MT pc.
Let Par : vrP := fun fq => vr_ar (fx := fq) B MT.
Let Paf : vrP := fun fq => vr_af (fx := fq) B MT.
Let Pled : vrP := fun fq => vr_led (fx := fq) B MT.
Let Ps27 : vrP := fun fq => vr_s27in (fx := fq) B MT.
Let Ps28 : vrP := fun fq => vr_s28in (fx := fq) B MT.
Let Ptail : vrP := fun fq => vr_rt_tail (fx := fq) B MT.

(* the epilogue 0x8d71c, the call after the reply 0x8d6b8 *)
Let K_af : vr_K Paf := VR32.
Let K_ar : vr_K Par := vr_K_segF Par Paf VR31 K_af.
Let K_ar_af : vr_K (vrP_or Par Paf) := vr_K_or _ _ K_ar K_af.
(* the six join entries (S30). J1 answers a one-word message and runs to the epilogue; the two JB entries always
   reach the after-reply block; the three JA entries test `ntok = 1` at 0x8d6b4 and take either. *)
Let K_j3b0 : vr_K (Phd 0x8d3b0) := vr_K_seg _ Paf (fun fq => proj1 (VR30 fq)) K_af.
Let K_j4cc : vr_K (Phd 0x8d4cc) := vr_K_seg _ Par (fun fq => proj1 (proj2 (VR30 fq))) K_ar.
Let K_j4d0 : vr_K (Phd 0x8d4d0) := vr_K_seg _ Par (fun fq => proj1 (proj2 (proj2 (VR30 fq)))) K_ar.
Let K_j55c : vr_K (Phd 0x8d55c) :=
  vr_K_seg _ (vrP_or Par Paf) (fun fq => proj1 (proj2 (proj2 (proj2 (VR30 fq))))) K_ar_af.
Let K_j6a0 : vr_K (Phd 0x8d6a0) :=
  vr_K_seg _ (vrP_or Par Paf) (fun fq => proj1 (proj2 (proj2 (proj2 (proj2 (VR30 fq)))))) K_ar_af.
Let K_j6a4 : vr_K (Phd 0x8d6a4) :=
  vr_K_seg _ (vrP_or Par Paf) (fun fq => proj2 (proj2 (proj2 (proj2 (proj2 (VR30 fq)))))) K_ar_af.
(* the six refusal stubs (S29): four call sup_resp, and 0x8d64c / 0x8d884 only set the code (0x8d884 also reloads
   tok) before the shared sup_resp at 0x8d88c *)
Let K_pr88c : vr_K (Ppr 0x8d88c) :=
  vr_K_segF _ (Phd 0x8d55c) (fun fq => proj1 (proj2 (proj2 (proj2 (VR29 fq))))) K_j55c.
Let K_pr4c4 : vr_K (Ppr 0x8d4c4) := vr_K_segF _ (Phd 0x8d4cc) (fun fq => proj1 (VR29 fq)) K_j4cc.
Let K_pr68c : vr_K (Ppr 0x8d68c) := vr_K_segF _ (Phd 0x8d6a4) (fun fq => proj1 (proj2 (VR29 fq))) K_j6a4.
Let K_pr870 : vr_K (Ppr 0x8d870) :=
  vr_K_segF _ (Phd 0x8d4d0) (fun fq => proj1 (proj2 (proj2 (VR29 fq)))) K_j4d0.
Let K_pr64c : vr_K (Ppr 0x8d64c) :=
  vr_K_seg _ (Ppr 0x8d88c) (fun fq => proj1 (proj2 (proj2 (proj2 (proj2 (VR29 fq)))))) K_pr88c.
Let K_pr884 : vr_K (Ppr 0x8d884) :=
  vr_K_seg _ (Ppr 0x8d88c) (fun fq => proj2 (proj2 (proj2 (proj2 (proj2 (VR29 fq)))))) K_pr88c.
(* the scan of g_instance_info_verbs and its three routes *)
Let K_s28 : vr_K Ps28 := vr_K_segF _ (vrP_or (Phd 0x8d4cc) (Phd 0x8d6a4)) VR28 (vr_K_or _ _ K_j4cc K_j6a4).
Let K_s27 : vr_K Ps27 := vr_K_segF _ (vrP_or (Phd 0x8d4cc) Ps28) VR27 (vr_K_or _ _ K_j4cc K_s28).
Let K_led : vr_K Pled := vr_K_segF _ (Phd 0x8d6a0) VR26 K_j6a0.
Let K_tail : vr_K Ptail := vr_K_seg _ (vrP_or Pled Ps27) VR25 (vr_K_or _ _ K_led K_s27).

(* the routes *)
Lemma vr_K_route : vr_K (fun fq e => vr_rt (fx := fq) B MT e (VRR.route (Verbs.toks (e_D e)))).
Proof.
intros fq e W cf He H. destruct (VRR.route (Verbs.toks (e_D e))).
- exact (vr_K_segF (Prt VRR.RAdd) _ VR07 (vr_K_or _ _ K_pr68c (vr_K_or _ _ K_pr4c4 K_j4d0)) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RDget) _ VR08 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RPget) _ VR09 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RRemove) _ VR10 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RWlist) _ VR11 (vr_K_or _ _ K_pr4c4 K_j3b0) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RIinfo) _ VR12 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RReset) _ VR13 (vr_K_or _ _ K_pr4c4 K_j55c) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RQclear) _ VR14 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RPolicy) _ VR15 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RLv2) _ VR16 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RPool) _ VR17 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.REnv) _ VR18 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RChain) _ VR19 K_j55c fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RChclear) _ VR20 (vr_K_or _ _ K_pr64c K_j55c) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RPinset) _ VR21 K_pr88c fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RPinacc) _ VR22 (vr_K_or _ _ K_pr68c K_j4cc) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RPinclr) _ VR23 (vr_K_or _ _ K_pr884 K_pr88c) fq e W cf He H).
- exact (vr_K_segF (Prt VRR.RQuit) _ VR24 (vr_K_or _ _ K_pr870 K_j3b0) fq e W cf He H).
- apply (K_tail fq e W cf He). eexists. split; [|exact H]. reflexivity.
- apply (K_tail fq e W cf He). eexists. split; [|exact H]. reflexivity.
- apply (K_tail fq e W cf He). eexists. split; [|exact H]. reflexivity.
- apply (K_tail fq e W cf He). eexists. split; [|exact H]. reflexivity.
Qed.

(* the dispatch, the tokenizer, the trim, the duplication *)
Let K_b4t : vr_K Pb4t := vr_K_seg _ _ VR06 vr_K_route.
Let K_b4e : vr_K Pb4e := vr_K_segF _ Paf VR05 K_af.
Let K_b3 : vr_K Pb3 := vr_K_seg _ (vrP_or Pb4e Pb4t) VR04 (vr_K_or _ _ K_b4e K_b4t).
Let K_b2 : vr_K Pb2 := vr_K_seg _ Pb3 VR03 K_b3.
Let K_b1 : vr_K Pb1 := vr_K_seg _ (vrP_or Pb2 Pb3) VR02 (vr_K_or _ _ K_b2 K_b3).

(* the record facts the entry state needs beyond the statement's premises (verbs_receive_iface.v vr_ent) *)
Hypothesis RECC : vr_rec_cells B.
Hypothesis ROIN : vr_ro_in_img.

Theorem tverbs_receive_spec_of_segs : forall fx : YK11.FPState, tverbs_receive_spec (fx := fx) B MT.
Proof.
intros fx ly S W regs mem md ch msg fd data n q0 D R O rest
  HPRE HFRM HARO Ha0 Hmsg Hobj Hfd Hdat Hdr Hn Hn8 HlenD Hin Hnot Hab Hrec Hcalls Hans Hrep Hnr Href Hperm Hq
  Hro Hvo Hfr Hev Hbb Hmo.
pose proof HPRE as (HAR & _).
destruct (RECC ly S W mem md HAR) as (Hflag & Hguard & ev & Herr).
pose proof (vri_got_of_ro _ Hro) as Hgot.
pose proof ROIN as Hroin. unfold vr_ro_in_img in Hroin.
assert (He : vr_ent (fx := fx) B MT (mkVrE ly S W regs mem md ch msg fd data n q0 ev D R O rest)).
{ unfold vr_ent, frm0. cbv beta zeta iota delta [e_ly e_S e_W e_regs e_mem e_md e_ch e_msg e_fd e_data e_n e_q0 e_ev e_D e_R e_O e_rest].
  repeat (split; [eassumption|]); eassumption. }
eapply SRr_bind; [exact (VR01 fx _ He)|].
intros W' cf' _ HB1. exact (K_b1 fx _ W' cf' He HB1).
Qed.

End e.
End f.
End d.
