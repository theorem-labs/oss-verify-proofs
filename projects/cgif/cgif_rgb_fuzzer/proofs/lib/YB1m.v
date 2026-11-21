(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (HS_ok, trb_startup_T1 and HS_ok_open are stated over the run's ProcInput and mmap base, with SINV0, argH0, E0 and wrap_mem over the run; trb_startup_T1 takes the mmap base's validity, valid_launch, the launch premise entry_launch_ok_va and valid_input's recorded-kernel conjunct in place of the separate input fields and entry_stack_fits; HS_ok and HS_ok_open over the hand-off states computed from the run at the run's own CONFIG_RSEQ flag, YB01r.v, in place of the recorded ones; trb_startup_T1 takes valid_input's channel-reader conjunct for cs_ok's new co_rdr field). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB11 YB1g YB1j YB1i YB1o YB1k YB05 YB01r YB1l.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Fixpoint all_holes (s : shape) : bool :=
match s with
| SHole _ => true
| SAlt2 a b => all_holes a && all_holes b
| SCase _ _ a b => all_holes a && all_holes b
| _ => false
end.
Section d. Context {fx : YK11.FPState}.
Lemma sd_all_holes : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (T : TSet) D E fs s,
all_holes s = true -> (forall h E' fs', HOLES h E' fs' = T) -> t_eq (sd HOLES D E fs s) T.
Proof.
intros HOLES T D E fs s. induction s as [ | c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h | ];
intros Hs HT; cbn [all_holes] in Hs; try discriminate Hs.
- apply andb_prop in Hs as [Ha Hb]. cbn [sd]. intros tr. unfold t_alt2.
pose proof (IHa Ha HT tr) as X. pose proof (IHb Hb HT tr) as Y. tauto.
- apply andb_prop in Hs as [Ha Hb]. cbn [sd]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa Ha HT) | exact (IHb Hb HT)].
- cbn [sd]. rewrite HT. intros tr. tauto.
Qed.
End d.
Lemma trb_all_holes : all_holes startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Section f.
#[local] Existing Instance YK11.fx0.
(* 08b1429: over the run's input [inp] (recipes/procinput-fields.md step 3), as YA02. *)
Definition HS_ok (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput) (fs : Fs.Fs)
(c : config) : Prop :=
exists ch E R FULL model,
HS_trb_r (APC.rseq_z (kb_rseq (in_kernel inp))) h = Some ch
/\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TRB YA02.LIMIT (YA02.TOP sp)
(SINV0 TRB TPH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) fs E ch R FULL model.
Theorem trb_startup_T1 :
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk0 -> valid_mmap_base mbase ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
(* #38 (rules 12f, 12r): the premise WAS [in_kernel inp = default_kernel], which
   fixes all thirteen kernel fields and is undischargeable from the top, since
   [valid_input]'s conjunct 17 (75d69e00:Run.v:4596) leaves kb_thp, kb_aslr,
   kb_guard, kb_rnd_bits and kb_rseq FREE.  It is now that conjunct itself, so
   the statement is STRENGTHENED: it speaks about every kernel build the
   published statement speaks about, instead of one. *)
in_kernel inp = recorded_kernel (in_kernel inp) ->
(* LPS 727298f3: [valid_input]'s channel-reader conjunct (Run.v:4967
   [valid_input_channel_reader]), for [cs_ok]'s new last field [co_rdr].  The caller
   proves it from [valid_input inp]; it is not a premise above any top theorem. *)
in_channel_reader inp = true ->
forall T : TSet, T [] ->
(forall h c, HS_ok h sp rdraw brk0 mbase inp (in_fs inp) c -> srealizes TSEGS c T) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT inp) T.
Proof.
intros sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrec Hrdr T HT HH.
set (HOLES := fun (_ : nat) (_ : env) (_ : Fs.Fs) => T).
eapply srz_conseq.
- apply (trb_startup_closed sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrec Hrdr HOLES).
+ intros h E E' fs0 _; reflexivity.
+ intros h E fs0; exact HT.
+ intros h' h E fs0 tr _ X; exact X.
+ intros h ch Hh E R FULL model HC. cbn [HOLES].
replace (m_fs model) with (in_fs inp) by (symmetry; exact (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC)).
apply (HH h). exists ch, E, R, FULL, model. split; [exact Hh|]. split; [reflexivity|]. exact HC.
- apply sd_all_holes; [exact trb_all_holes | intros; reflexivity].
Qed.
Lemma HS_ok_open : forall h sp rdraw brk0 mbase inp fs c,
HS_ok h sp rdraw brk0 mbase inp fs c ->
exists ch E R FULL model,
HS_trb_r (APC.rseq_z (kb_rseq (in_kernel inp))) h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TRB YA02.LIMIT (YA02.TOP sp)
(SINV0 TRB TPH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) fs E ch R FULL model
/\ (forall n, (n < NX0G)%nat -> ev E n = ev (E0 sp rdraw brk0 inp) n)
/\ (forall a, argH0 sp rdraw inp E a = true -> FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (a_entry TRB)) sp rdraw a)
/\ eb E = eb (E0 sp rdraw brk0 inp).
Proof.
intros h sp rdraw brk0 mbase inp fs c (ch & E & R & FULL & model & Hh & Hc & HC).
exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
End f.
