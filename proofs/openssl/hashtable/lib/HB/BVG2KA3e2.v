(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxReblob CxOpt CxOptGen CxOptK CxRefront CxfL9 CxfFast HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBUsageDefs HBParity
  HBVtHop BVG2T3Lit BFIEndK2A3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition vk_sig_a3e2_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 41)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 41)) (ELit 8192)));
  (1120%nat, (ELit 0));
  (100%nat, (EVar 47));
  (234%nat, (EVar 46));
  (235%nat, (EVar 28));
  (236%nat, (EVar 29));
  (284%nat, (EVar 31));
  (285%nat, (EVar 27));
  (286%nat, (EVar 45));
  (334%nat, (EVar 44));
  (399%nat, (EVar 43));
  (400%nat, (EVar 53));
  (433%nat, (EVar 52));
  (497%nat, (EVar 42));
  (514%nat, (EVar 41));
  (515%nat, (EVar 40));
  (548%nat, (EVar 39));
  (549%nat, (EVar 38));
  (550%nat, (EVar 37));
  (551%nat, (EVar 33));
  (552%nat, (EVar 51));
  (553%nat, (EVar 34));
  (554%nat, (EVar 50));
  (555%nat, (EVar 35));
  (556%nat, (EVar 49));
  (557%nat, (EVar 48));
  (558%nat, (EVar 36));
  (574%nat, (EVar 15));
  (575%nat, (EVar 16));
  (602%nat, (EVar 30));
  (603%nat, (EVar 32));
  (604%nat, (EVar 54));
  (605%nat, (EVar 55));
  (606%nat, (EVar 57));
  (607%nat, (EVar 58));
  (608%nat, (EVar 59));
  (609%nat, (EVar 60));
  (610%nat, (EVar 61));
  (611%nat, (EVar 62));
  (612%nat, (EVar 63));
  (613%nat, (EVar 64));
  (614%nat, (EVar 65));
  (615%nat, (EVar 66));
  (616%nat, (EVar 67));
  (617%nat, (EVar 68));
  (618%nat, (EVar 69));
  (619%nat, (EVar 70));
  (620%nat, (EVar 71));
  (1101%nat, (EVar 56));
  (621%nat, (ELit 64));
  (622%nat, (ELit 2))].
Abbreviation vk_sig_a3e2 := (vk_sig_a3e2_ tt).
Definition vk_F_a3e2_ (_ : unit) : list kentry := [par_even].
Abbreviation vk_F_a3e2 := (vk_F_a3e2_ tt).
Definition vkpl_a3e2_ (_ : unit) : plan := PJoin (ELit 0) 12554992 8 (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 41) 1 34359736318) (PHandoff 1050))).
Abbreviation vkpl_a3e2 := (vkpl_a3e2_ tt).
Definition htg_a3e2_ (_ : unit) : htgt := (vg2t3, vk_sig_a3e2, vk_F_a3e2).
Abbreviation htg_a3e2 := (htg_a3e2_ tt).
Lemma htok_a3e2 : ht_ok 100 htg_a3e2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma nxge_a3e2 : (NX0 <= 100)%nat. Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma nxspw_a3e2 : CAP.expr_vars_lt 100 e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_a3e2 : CAP.check HASEGS vt_IT HAT 100 AsanInit.LIMIT (hag_XN 100) (hag_XE 100) hag_XB (HS_tg [(1050%nat, htg_a3e2)]) 0 true false true 400000 3000 None (with_facts fiendk2a3 [par_even]) vkpl_a3e2 = COk (SHole 1050).
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk (SHole 1050))). Qed.
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
  Hypothesis Htmpl : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts vg2t3 [par_even]) T.
  Theorem vtail_a3e2 : piece (SVG PHI SV) argH ISP fs (with_facts fiendk2a3 [par_even]) T.
  Proof.
    exact (vt_hop sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PHI PHI_agree T T_agree T_nil 100%nat nxge_a3e2 nxspw_a3e2
             vg2t3 (with_facts fiendk2a3 [par_even]) vk_sig_a3e2 vk_F_a3e2 vt_IT vt_IT_ok vkpl_a3e2 1050%nat htok_a3e2 Htmpl chk_a3e2).
  Qed.
End M.
