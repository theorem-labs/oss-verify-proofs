(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxReblob CxOpt CxOptGen CxOptK CxRefront CxfL9 CxfFast HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBUsageDefs HBParity
  HBVtHop BVG6T012Lit BFIEndK6B1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition vk_sig_b1e6_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 0));
  (1120%nat, (ELit 18446744073709551615));
  (1121%nat, (ELit 1));
  (100%nat, (EVar 52));
  (234%nat, (EVar 51));
  (235%nat, (EVar 29));
  (236%nat, (EVar 30));
  (284%nat, (EVar 32));
  (285%nat, (EVar 28));
  (286%nat, (EVar 50));
  (334%nat, (EVar 49));
  (399%nat, (EVar 48));
  (400%nat, (EVar 58));
  (433%nat, (EVar 57));
  (497%nat, (EVar 47));
  (514%nat, (EVar 46));
  (515%nat, (EVar 45));
  (548%nat, (EVar 44));
  (549%nat, (EVar 43));
  (550%nat, (EVar 42));
  (551%nat, (EVar 38));
  (552%nat, (EVar 56));
  (553%nat, (EVar 39));
  (554%nat, (EVar 55));
  (555%nat, (EVar 40));
  (556%nat, (EVar 54));
  (557%nat, (EVar 53));
  (558%nat, (EVar 41));
  (574%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 15)) (EVar 16)));
  (575%nat, (EVar 17));
  (604%nat, (EVar 31));
  (605%nat, (EVar 33));
  (606%nat, (EVar 34));
  (607%nat, (EVar 35));
  (608%nat, (EVar 36));
  (609%nat, (EVar 37));
  (610%nat, (EVar 59));
  (611%nat, (EVar 60));
  (612%nat, (EVar 62));
  (613%nat, (EVar 63));
  (614%nat, (EVar 64));
  (615%nat, (EVar 65));
  (616%nat, (EVar 66));
  (617%nat, (EVar 67));
  (618%nat, (EVar 68));
  (619%nat, (EVar 69));
  (620%nat, (EVar 70));
  (621%nat, (EVar 71));
  (622%nat, (EVar 72));
  (623%nat, (EVar 73));
  (624%nat, (EVar 74));
  (625%nat, (EVar 75));
  (626%nat, (EVar 76));
  (1101%nat, (EVar 61));
  (627%nat, (ELit 1024));
  (628%nat, (ELit 6))].
Abbreviation vk_sig_b1e6 := (vk_sig_b1e6_ tt).
Definition vk_F_b1e6_ (_ : unit) : list kentry := [par_even].
Abbreviation vk_F_b1e6 := (vk_F_b1e6_ tt).
Definition vkpl_b1e6_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 11; ELit 255] (PExt 47 [ELit 48; ELit 47] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 57))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 57) 0 1) (PFact (KRange (ELit 0) 0 1) (PHandoff 1128)))))).
Abbreviation vkpl_b1e6 := (vkpl_b1e6_ tt).
Definition htg_b1e6_ (_ : unit) : htgt := (vg6t012, vk_sig_b1e6, vk_F_b1e6).
Abbreviation htg_b1e6 := (htg_b1e6_ tt).
Lemma htok_b1e6 : ht_ok 100 htg_b1e6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma nxge_b1e6 : (NX0 <= 100)%nat. Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma nxspw_b1e6 : CAP.expr_vars_lt 100 e_spw = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_b1e6 : CAP.check HASEGS vt_IT HAT 100 AsanInit.LIMIT (hag_XN 100) (hag_XE 100) hag_XB (HS_tg [(1128%nat, htg_b1e6)]) 0 true false true 400000 3000 None (with_facts fiendk6b1 [par_even]) vkpl_b1e6 = COk (SHole 1128).
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk (SHole 1128))). Qed.
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
  Hypothesis Htmpl : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts vg6t012 [par_even]) T.
  Theorem vtail_b1e6 : piece (SVG PHI SV) argH ISP fs (with_facts fiendk6b1 [par_even]) T.
  Proof.
    exact (vt_hop sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PHI PHI_agree T T_agree T_nil 100%nat nxge_b1e6 nxspw_b1e6
             vg6t012 (with_facts fiendk6b1 [par_even]) vk_sig_b1e6 vk_F_b1e6 vt_IT vt_IT_ok vkpl_b1e6 1128%nat htok_b1e6 Htmpl chk_b1e6).
  Qed.
End M.
