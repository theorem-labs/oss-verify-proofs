(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1n.v (donor image sha256 c0661b96b5bd), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AB1n.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB12 YB1h YB1k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1p YB1l YB05 YB01 YB1m.
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
Lemma tfib_all_holes : all_holes startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Section f.
#[local] Existing Instance YK11.fx0.
Definition HS_ok (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs)
(c : config) : Prop :=
exists ch E R FULL model,
HS_tfib h = Some ch
/\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(SINV0 TPH sp rdraw brk0 argv envp uid hw) (argH0 TPH sp rdraw argv envp uid hw) fs E ch R FULL model.
Theorem tfib_startup_T1 :
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
(uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
valid_sp sp -> valid_brk TSEGS brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
valid_id uid -> valid_hwcap hw ->
forall T : TSet, T [] ->
(forall h c, HS_ok h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes TSEGS c T) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.
Proof.
intros sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw T HT HH.
set (HOLES := fun (_ : nat) (_ : env) (_ : Fs.Fs) => T).
eapply srz_conseq.
- apply (tfib_startup_closed sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw HOLES).
+ intros h E E' fs0 _; reflexivity.
+ intros h E fs0; exact HT.
+ intros h' h E fs0 tr _ X; exact X.
+ intros h ch Hh E R FULL model HC. cbn [HOLES].
replace (m_fs model) with (fs_seed_tmp fs tmp) by (symmetry; exact (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC)).
apply (HH h). exists ch, E, R, FULL, model. split; [exact Hh|]. split; [reflexivity|]. exact HC.
- apply sd_all_holes; [exact tfib_all_holes | intros; reflexivity].
Qed.
Lemma HS_ok_open : forall h sp rdraw brk0 argv envp uid hw fs c,
HS_ok h sp rdraw brk0 argv envp uid hw fs c ->
exists ch E R FULL model,
HS_tfib h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(SINV0 TPH sp rdraw brk0 argv envp uid hw) (argH0 TPH sp rdraw argv envp uid hw) fs E ch R FULL model
/\ (forall n, (n < NX0G)%nat -> ev E n = ev (E0 TPH sp rdraw brk0 argv envp uid hw) n)
/\ (forall a, argH0 TPH sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a)
/\ eb E = eb (E0 TPH sp rdraw brk0 argv envp uid hw).
Proof.
intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
End f.
