(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the parts the walk of plugin-hostd/fuzz_command's strdup entry needs that no file of this tree holds: the code table of the entry (the shape of lib/A/AE34.v), the two phase lemmas (the shape of lib/A/AE2y.v icpt_phase), and one lemma that carries an [amreal] post through a later run. *)
(* Modified by Theorem Labs, 2026-10: moved from this harness's lib/A/Rt/RtDStrdupD.v to plugin-hostd/fuzz_command's ASan+UBSan image (fuzz_command.asan-ubsan), whose ___interceptor_strdup (0x4ccfc) is the ASan image's (0x4ccb0) word for word modulo pc-relative fields: module paths lib/A to lib/B, and the addresses by the name-keyed A-to-B address map (the trampoline 0x45228, the body 0x4ccfc, the helpers 0x60414 and 0x78ed4, the unwinder pc 0x4ce1c, UnwindImpl 0x60424, asan_malloc 0x34574, and the read-only cells as lib/B/YF0m.v holds them); the comments re-read from that image; the proof text is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The entry, measured on the pinned fuzz_command.asan-ubsan: the trampoline 0x45228 is one [j], the body 0x4ccfc is 230
   instructions (nm size 0x398). The two helpers the body calls that tbl_icpt does not hold are
   GetMallocContextSize 0x60414 (4 instructions) and StackTrace::GetCurrentPc 0x78ed4 (2); TryAsanInitFromRtl
   0x5f68c, internal_strlen 0x69b5c and __asan_region_is_poisoned 0x5a1f8 are already in tbl_icpt (YE34.v:25-30). *)
Definition SD_TRAMP : Z := 0x45228.
Definition SD_ENTRY : Z := 0x4ccfc.
Definition SD_RA0 : Z := 0x4ce1c.
Definition SD_UNWIND : Z := 0x60424.
Definition SD_MALLOC : Z := 0x34574.
Definition SD_FRAME : Z := 2144.
Definition SD_WIN : Z := 2176.
Definition sd_ranges : list (Z * nat) :=
[(SD_TRAMP, 1%nat); (SD_ENTRY, 230%nat); (0x60414, 4%nat); (0x78ed4, 2%nat)].
Definition tbl_sd : ctable := Eval vm_compute in build_ranges sd_ranges tbl_icpt.
Lemma tbl_sd_eq : tbl_sd = build_ranges sd_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_sd). Qed.
Lemma tbl_sd_ok : table_ok tfibsegs tbl_sd.
Proof.
rewrite tbl_sd_eq. apply build_ranges_ok; [unfold sd_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok].
Qed.

(* The read-only words the entry loads, on top of the ones every interceptor loads (YE2y.v:69-76): the
   replace_str flag byte asan+29 = 0xae455, the malloc-context-size cache 0xb193c, the common-flags pointer
   0xa5f40 and the word of the common flags that holds fast_unwind_on_malloc (+34, inside 0x142788), and the
   memcpy pointer pair 0xa5f78 -> 0xa7e08. Every one is a cell of Tfib_const (B/YF0m.v), so [rodata_chk] holds. *)
Definition sd_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++
[ (0xae455, 1, [(0, 1%N, 1)]);
(0xb193c, 4, [(0, 4%N, 0x1e)]);
(0xa5f40, 8, [(0, 8%N, 0x142768)]);
(0x142788, 8, [(0, 8%N, 0x1e00010000)]);
(0xa5f78, 8, [(0, 8%N, 0xa7e08)]) ].
Lemma sd_rodata_chk : forall ly, rodata_chk ly sd_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* AE2y.v:32 icpt_phase over tbl_sd. *)
Lemma sd_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_sd FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_sd tbl_sd_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma sd_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_sd FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_sd tbl_sd_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* A model step whose post is followed by a run of the real machine: the shape the entry needs, because the
   allocation happens inside the entry and the copy and the epilogue come after it. *)
Lemma amreal_then_SRr {R} : forall (t : itree astate R) (W : world tfibsegs) c
(P Q : R -> world tfibsegs -> config -> Prop),
amreal tfibsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfibsegs W' c' (Q r)) ->
amreal tfibsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HK; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HP. exact (HK r W' c' HP).
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact HK]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact HK].
- exact H.
- exact I.
Qed.

End e.
