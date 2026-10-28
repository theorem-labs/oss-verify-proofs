(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxReblob CxOpt CxOptGen CxOptK CxRefront CxfL9 CxfFast HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBUsageDefs HBParity
  HBVtHop BVG1T012Lit BFIEndK1B1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition vk_sig_b1o1_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 0));
  (1120%nat, (ELit 18446744073709551615));
  (1121%nat, (ELit 1));
  (100%nat, (EVar 46));
  (234%nat, (EVar 45));
  (235%nat, (EVar 28));
  (236%nat, (EVar 29));
  (284%nat, (EVar 33));
  (285%nat, (EVar 27));
  (286%nat, (EVar 44));
  (334%nat, (EVar 43));
  (399%nat, (EVar 42));
  (400%nat, (EVar 52));
  (433%nat, (EVar 51));
  (497%nat, (EVar 41));
  (514%nat, (EVar 40));
  (515%nat, (EVar 39));
  (548%nat, (EVar 31));
  (549%nat, (EVar 32));
  (550%nat, (EVar 38));
  (551%nat, (EVar 34));
  (552%nat, (EVar 50));
  (553%nat, (EVar 35));
  (554%nat, (EVar 49));
  (555%nat, (EVar 36));
  (556%nat, (EVar 48));
  (557%nat, (EVar 47));
  (558%nat, (EVar 37));
  (574%nat, (EVar 15));
  (575%nat, (EVar 16));
  (603%nat, (EVar 30));
  (604%nat, (EVar 53));
  (605%nat, (EVar 54));
  (606%nat, (EVar 56));
  (607%nat, (EVar 57));
  (608%nat, (EVar 58));
  (609%nat, (EVar 59));
  (610%nat, (EVar 60));
  (611%nat, (EVar 61));
  (612%nat, (EVar 62));
  (613%nat, (EVar 63));
  (614%nat, (EVar 64));
  (615%nat, (EVar 65));
  (616%nat, (EVar 66));
  (617%nat, (EVar 67));
  (618%nat, (EVar 68));
  (619%nat, (EVar 69));
  (620%nat, (EVar 70));
  (1101%nat, (EVar 55));
  (621%nat, (ELit 32));
  (622%nat, (ELit 1))].
Abbreviation vk_sig_b1o1 := (vk_sig_b1o1_ tt).
Definition vk_F_b1o1_ (_ : unit) : list kentry := [par_odd].
Abbreviation vk_F_b1o1 := (vk_F_b1o1_ tt).
Definition vkpl_b1o1_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 11; ELit 255] (PExt 47 [ELit 43; ELit 42] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 51))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 51) 0 1) (PFact (KRange (ELit 0) 0 1) (PHandoff 1029)))))).
Abbreviation vkpl_b1o1 := (vkpl_b1o1_ tt).
Definition htg_b1o1_ (_ : unit) : htgt := (vg1t012, vk_sig_b1o1, vk_F_b1o1).
Abbreviation htg_b1o1 := (htg_b1o1_ tt).
Lemma htok_b1o1 : ht_ok 100 htg_b1o1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma nxge_b1o1 : (NX0 <= 100)%nat. Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma nxspw_b1o1 : CAP.expr_vars_lt 100 e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_b1o1 : CAP.check HASEGS vt_IT HAT 100 AsanInit.LIMIT (hag_XN 100) (hag_XE 100) hag_XB (HS_tg [(1029%nat, htg_b1o1)]) 0 true false true 400000 3000 None (with_facts fiendk1b1 [par_odd]) vkpl_b1o1 = COk (SHole 1029).
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk (SHole 1029))). Qed.
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
  Hypothesis Htmpl : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts vg1t012 [par_odd]) T.
  Theorem vtail_b1o1 : piece (SVG PHI SV) argH ISP fs (with_facts fiendk1b1 [par_odd]) T.
  Proof.
    exact (vt_hop sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PHI PHI_agree T T_agree T_nil 100%nat nxge_b1o1 nxspw_b1o1
             vg1t012 (with_facts fiendk1b1 [par_odd]) vk_sig_b1o1 vk_F_b1o1 vt_IT vt_IT_ok vkpl_b1o1 1029%nat htok_b1o1 Htmpl chk_b1o1).
  Qed.
End M.
