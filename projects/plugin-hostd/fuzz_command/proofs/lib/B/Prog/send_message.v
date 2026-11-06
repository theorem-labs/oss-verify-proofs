(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/send_message.v (the ASan walk,
   a working branch 4f5a539710b, re-fitted d0af25245f3) to the ASan+UBSan build fuzz_command.asan-ubsan
   (lib/B, entry 0x86bf8): `tsend_message_spec_holds : tsend_message_spec B MT` is the statement of
   lib/B/Prog/send_message_c.v at a working branch f490061c104 (passes 4, 4b and 5: callees and runtime entries at every FP
   state, rounding mode 0 in place of astack_pres, the post apost_baseF). The record facts come from a Theorem Labs lane's kit
   (lib/B/Prog/CmdRecBase.v cmd_img_facts and the lemmas of CmdRecImg.v, CmdRecRo.v), the call rules and transport
   lemmas from lib/B/Prog/PaCallPg.v and PaFx.v. *)
(* Modified by Theorem Labs, 2026-10: send_message's walk on plugin-hostd/fuzz_command's ASan+UBSan image, assembled
   from its five segments (send_message_s1.v .. send_message_s5.v) as cgif's cgif_close is assembled from its segment
   chain (proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v, ACke.v at c8557374ad2e; the chain
   ACh1.v:804-805, ACh2.v:1238-1239, the contract ACh5.v:323-341). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import send_message_k send_message_l
  send_message_s1 send_message_s2 send_message_s3 send_message_s4 send_message_s5.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk hypotheses (a Theorem Labs lane's RULING-STMT.md §1) *)
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* the program callees and the runtime entries, as send_message_c.v names them (at every FP state, forall fx0) *)
Hypothesis RCL : forall fx0 : YK11.FPState, @trec_clear_spec fx0 rc SK PI B MT.
Hypothesis VR : forall fx0 : YK11.FPState, @tverbs_receive_spec fx0 rc SK PI B MT.
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA CS___asan_memcpy).
(* the call targets of program functions (RULING-STMT.md §1 SIGP, lib/B/Prog/CmdObj.v) *)
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary record (RULING-STMT.md §1 HB, lib/B/YF0m.v) and the program statics' writability (§2 PRW) *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis PRW : prog_rw SEGS B.
(* the image facts (CmdRecBase.v cmd_img_facts): a Theorem Labs lane's cmd_addressable_chk (CmdRecBase.v), cmd_ro_ok_of_aro
   (CmdRecRo.v) and cmd_prog_unowned (CmdRecImg.v) take them, applied in send_message_s3.v .. send_message_s5.v; the
   read-only range facts arodata_ok_journalP asks (RULING-STMT.md §1 RRO, RO, RPG) are its fields cif_relro_img,
   cif_ro_below_ofl and cif_prog_not_ro (sm_P0) *)
Hypothesis IMG : cmd_img_facts SEGS B.

Definition zr_hits (lo hi : Z) (l : list (Z * Z)) : list (Z * Z) :=
List.filter (fun r => negb (Z.leb (fst r + snd r) lo || Z.leb hi (fst r))) l.
Lemma zr_hits_nil : forall lo hi l a, zr_hits lo hi l = [] -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l a H Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
assert (Hf : In r (zr_hits lo hi l)).
{ unfold zr_hits. apply filter_In. split; [exact Hr|]. unfold in_zr in Hin.
  apply negb_true_iff, orb_false_iff. split; apply Z.leb_gt; lia. }
rewrite H in Hf. destruct Hf.
Qed.
(* g_quitting's GOT word and its neighbours are in the read-only range (cif_relro_img) and are not runtime-owned: no
   range of B's Tfib_owned_static meets 0xa6bc8..0xa6be8 (the nearest owned words are 0xa6ba8..0xa6bb0 and
   0xa6be8..0xa6bf8), and errno is elsewhere *)
Lemma sm_got_unowned : forall a, 0xa6bc8 <= a < 0xa6be8 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. split; [apply (cif_relro_img _ _ IMG); unfold CMD_RLO, CMD_RHI; lia|].
rewrite (YF0m.ts_owned _ HB), (YF0m.ts_errno _ HB). split.
- apply (zr_hits_nil 0xa6bc8 0xa6be8); [vm_compute; reflexivity | exact Ha].
- unfold YF0m.TFIB_ERRNO. lia.
Qed.

Lemma sm_sigma : forall s af, In s cmd_prog_syms -> cmd_af s = af -> SIGMA s = BASE + af.
Proof. intros s af Hs Ha. rewrite (SIGP s Hs), Ha. reflexivity. Qed.
Lemma sm_prog_static : forall lo len a, In (lo, len) YF0m.TFIB_PROG_STATIC -> lo <= a < lo + len ->
Exists (in_zr a) (as_prog_static B).
Proof.
intros lo len a Hin Ha. rewrite (YF0m.ts_prog _ HB). apply Exists_exists. exists (lo, len). split; [exact Hin|].
unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Ltac in_list := cbn [In]; repeat (first [left; reflexivity | right]).

(* the segment chain: s5 proves the statement at verbs_receive's return, at the FP state verbs_receive returns (any
   fx0), s4 .. s1 carry it back to the entry *)
Lemma sm_P0 : SM_P0_stmt B MT.
Proof.
pose proof (sm_sigma CS_rec_clear AF_rec_clear ltac:(unfold cmd_prog_syms; in_list) ltac:(vm_compute; reflexivity))
as SIGMA_rec_clear.
pose proof (sm_sigma CS_verbs_receive AF_verbs_receive ltac:(unfold cmd_prog_syms; in_list)
ltac:(vm_compute; reflexivity)) as SIGMA_verbs_receive.
assert (G_REC_PROG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) (as_prog_static B))
by (intros a Ha; apply (sm_prog_static 0x5e32c0 960); [unfold YF0m.TFIB_PROG_STATIC; in_list | exact Ha]).
assert (G_SPILL_PROG : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) (as_prog_static B))
by (intros a Ha; apply (sm_prog_static 0x5e3760 56); [unfold YF0m.TFIB_PROG_STATIC; in_list | exact Ha]).
assert (G_QUITTING_PROG : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> Exists (in_zr a) (as_prog_static B))
by (intros a Ha; apply (sm_prog_static 0x5e37e0 4); [unfold YF0m.TFIB_PROG_STATIC; in_list | exact Ha]).
pose proof sm_got_unowned as CMD_GOT_UNOWNED.
pose proof (cif_relro_img _ _ IMG) as RRO.
pose proof (cif_prog_not_ro _ _ IMG) as RPG.
pose proof (cif_ro_below_ofl _ _ IMG : ro_below_ofl SEGS RLO RHI) as RO.
assert (cmd_prog_writable : forall ly S W mem md a, AR SEGS B ly S W mem md -> inFP cmd_PG a ->
writable_at SEGS (mrestrict (w_H W) mem) a).
{ intros ly S W mem md a _ (r & Hr & Hra). apply PRW. unfold cmd_PG in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra.
  - apply G_REC_PROG. unfold REC_SIZE. lia.
  - apply G_SPILL_PROG. unfold SC_SIZE. lia.
  - apply G_QUITTING_PROG. lia. }
eapply sm_s1; try eassumption.
eapply sm_s2; try eassumption.
eapply sm_s3; try eassumption.
eapply sm_s4; try eassumption.
intros fx0. eapply sm_s5; eassumption.
Qed.

Theorem tsend_message_spec_holds : tsend_message_spec B MT.
Proof.
intros ly S W regs mem md ch src n D R O rest
H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
exact (sm_P0 ly S W regs mem md ch src n D R O rest
(conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
(conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 H20)))))))))))))))))))).
Qed.
End e.
End f.
End d.
