(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB06 YB0l YB0o YB0n YB0t YB0p YB04 YB00.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
Definition IT0 : itab := mk_itab_ranges TSEGS startup_plan_tra_ranges.
Lemma IT0_ok : itab_sound TSEGS IT0.
Proof. apply mk_itab_ranges_sound. Qed.
Definition hole_le_tra (h1 h2 : nat) : bool := true.
Definition startup_shape : shape :=
SCase (EVar 6) 10 (SAlt2 (SAlt2 (SAlt2 (SHole 14) (SHole 15)) (SAlt2 (SAlt2 (SHole 12) (SHole 13)) (SAlt2 (SAlt2 (SHole 10) (SHole 11)) (SAlt2 (SHole 8) (SHole 9))))) (SAlt2 (SAlt2 (SAlt2 (SHole 6) (SHole 7)) (SAlt2 (SHole 4) (SHole 5))) (SAlt2 (SAlt2 (SAlt2 (SHole 2) (SHole 3)) (SAlt2 (SHole 0) (SHole 1))) (SAlt2 (SAlt2 (SHole 42) (SHole 43)) (SAlt2 (SHole 40) (SHole 41))))))
(SCase (EVar 6) 1802 (SAlt2 (SAlt2 (SAlt2 (SHole 30) (SHole 31)) (SAlt2 (SAlt2 (SHole 28) (SHole 29)) (SAlt2 (SAlt2 (SHole 26) (SHole 27)) (SAlt2 (SHole 24) (SHole 25))))) (SAlt2 (SAlt2 (SAlt2 (SHole 22) (SHole 23)) (SAlt2 (SHole 20) (SHole 21))) (SAlt2 (SAlt2 (SAlt2 (SHole 18) (SHole 19)) (SAlt2 (SHole 16) (SHole 17))) (SAlt2 (SAlt2 (SHole 46) (SHole 47)) (SAlt2 (SHole 44) (SHole 45))))))
(SAlt2 (SAlt2 (SHole 39) (SAlt2 (SHole 38) (SAlt2 (SHole 37) (SHole 36)))) (SAlt2 (SAlt2 (SHole 35) (SHole 34)) (SAlt2 (SAlt2 (SHole 33) (SHole 32)) (SAlt2 (SHole 49) (SHole 48)))))).
Lemma startup_cert :
check TSEGS IT0 TRA NX0G YA02.LIMIT (XNG TSEGS tra_XN1) XE0 XB0 HS_tra hole_le_tra KC0 BFUEL FUEL None
(init_acs_of_g TRA) startup_plan_tra
= COk startup_shape.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
Lemma startup_live : lv startup_plan_tra = true.
Proof. vm_compute. reflexivity. Qed.
#[local] Instance tracert_fx : YK11.FPState := YK11.fx0.
Section a.
Variable sp : word. Variable rdraw : EntryDraw. Variable brk0 mbase : word. Variable argv envp : list (list byte).
Variable fs : Fs.Fs. Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream. Variable tmp : Fs.Fs.
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk TSEGS brk0. Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp. Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le_tra h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound :
holes_stmt TSEGS TRA YA02.LIMIT (YA02.TOP sp) HS_tra
(SINV0 TPH sp rdraw brk0 argv envp uid hw) (argH0 TPH sp rdraw argv envp uid hw) HOLES FSQ.
Theorem tra_startup_closed :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil (E0 TPH sp rdraw brk0 argv envp uid hw) FSQ startup_shape).
Proof.
exact (tra_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
IT0 IT0_ok HS_tra hole_le_tra startup_plan_tra startup_shape KC0 BFUEL FUEL startup_cert startup_live
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound).
Qed.
End a.
