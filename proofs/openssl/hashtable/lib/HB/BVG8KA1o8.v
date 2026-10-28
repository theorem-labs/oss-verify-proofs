(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxReblob CxOpt CxOptGen CxOptK CxRefront CxfL9 CxfFast HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBUsageDefs HBParity
  HBVtHop BVG8T012Lit BFIEndK8A1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition vk_sig_a1o8_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 48)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (ELit 0));
  (1120%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 48)) (ELit 8192)));
  (1121%nat, (ELit 0));
  (100%nat, (EVar 54));
  (234%nat, (EVar 53));
  (235%nat, (EVar 29));
  (236%nat, (EVar 30));
  (284%nat, (EVar 32));
  (285%nat, (EVar 28));
  (286%nat, (EVar 52));
  (334%nat, (EVar 51));
  (399%nat, (EVar 50));
  (400%nat, (EVar 60));
  (433%nat, (EVar 59));
  (497%nat, (EVar 49));
  (514%nat, (EVar 48));
  (515%nat, (EVar 47));
  (548%nat, (EVar 46));
  (549%nat, (EVar 45));
  (550%nat, (EVar 44));
  (551%nat, (EVar 40));
  (552%nat, (EVar 58));
  (553%nat, (EVar 41));
  (554%nat, (EVar 57));
  (555%nat, (EVar 42));
  (556%nat, (EVar 56));
  (557%nat, (EVar 55));
  (558%nat, (EVar 43));
  (574%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 15)) (EVar 16)));
  (575%nat, (EVar 17));
  (602%nat, (EVar 31));
  (603%nat, (EVar 33));
  (604%nat, (EVar 34));
  (605%nat, (EVar 35));
  (606%nat, (EVar 36));
  (607%nat, (EVar 37));
  (608%nat, (EVar 38));
  (609%nat, (EVar 39));
  (610%nat, (EVar 61));
  (611%nat, (EVar 62));
  (612%nat, (EVar 64));
  (613%nat, (EVar 65));
  (614%nat, (EVar 66));
  (615%nat, (EVar 67));
  (616%nat, (EVar 68));
  (617%nat, (EVar 69));
  (618%nat, (EVar 70));
  (619%nat, (EVar 71));
  (620%nat, (EVar 72));
  (621%nat, (EVar 73));
  (622%nat, (EVar 74));
  (623%nat, (EVar 75));
  (624%nat, (EVar 76));
  (625%nat, (EVar 77));
  (626%nat, (EVar 78));
  (1101%nat, (EVar 63));
  (627%nat, (ELit 4096));
  (628%nat, (ELit 8))].
Abbreviation vk_sig_a1o8 := (vk_sig_a1o8_ tt).
Definition vk_F_a1o8_ (_ : unit) : list kentry := [par_odd].
Abbreviation vk_F_a1o8 := (vk_F_a1o8_ tt).
Definition vkpl_a1o8_ (_ : unit) : plan := PJoin (ELit 0) 12554992 8 (PExt 38 [EVar 6; ELit 11; ELit 255] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 59))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 59) 0 1) (PFact (KRange (EVar 48) 1 34359736318) (PFact (KRange (ELit 0) 0 1) (PHandoff 1164))))))).
Abbreviation vkpl_a1o8 := (vkpl_a1o8_ tt).
Definition htg_a1o8_ (_ : unit) : htgt := (vg8t012, vk_sig_a1o8, vk_F_a1o8).
Abbreviation htg_a1o8 := (htg_a1o8_ tt).
Lemma htok_a1o8 : ht_ok 100 htg_a1o8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma nxge_a1o8 : (NX0 <= 100)%nat. Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma nxspw_a1o8 : CAP.expr_vars_lt 100 e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_a1o8 : CAP.check HASEGS vt_IT HAT 100 AsanInit.LIMIT (hag_XN 100) (hag_XE 100) hag_XB (HS_tg [(1164%nat, htg_a1o8)]) 0 true false true 400000 3000 None (with_facts fiendk8a1 [par_odd]) vkpl_a1o8 = COk (SHole 1164).
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk (SHole 1164))). Qed.
Section M.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  Variable PHI : env -> Prop.
  Hypothesis PHI_agree : forall E E', env_agree NX0 E E' -> PHI E -> PHI E'.
  Variable T : env -> Fs.Fs -> TSet.
  Hypothesis T_agree : t_agree T.
  Hypothesis T_nil : forall E fs0, T E fs0 [].
  (* [comment removed for export] *)
  Hypothesis Htmpl : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts vg8t012 [par_odd]) T.
  Theorem vtail_a1o8 : piece (SVG PHI SV) argH ISP fs (with_facts fiendk8a1 [par_odd]) T.
  Proof.
    exact (vt_hop sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PHI PHI_agree T T_agree T_nil 100%nat nxge_a1o8 nxspw_a1o8
             vg8t012 (with_facts fiendk8a1 [par_odd]) vk_sig_a1o8 vk_F_a1o8 vt_IT vt_IT_ok vkpl_a1o8 1164%nat htok_a1o8 Htmpl chk_a1o8).
  Qed.
End M.
