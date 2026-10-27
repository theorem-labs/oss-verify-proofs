(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0m.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN35.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RDPC : Z := Eval vm_compute in (src0_A_main + 0xcc).
Definition RWPC : Z := Eval vm_compute in (src0_A_main + 0xdc).
Definition TPC : Z := Eval vm_compute in (src0_A_main + 0x88).
Definition RA_CP : Z := Eval vm_compute in (src0_A_main + 0x80).
Definition RA_MG : Z := Eval vm_compute in (src0_A_main + 0xa8).
Definition RA_MC1 : Z := Eval vm_compute in (src0_A_main + 0xc4).
Definition RA_FR : Z := Eval vm_compute in (src0_A_main + 0xcc).
Definition A_LEN : nat := 27.   Definition A_CAP : nat := 28.   Definition J0 : nat := 29.
Definition A_WANT : nat := 46.  Definition A_N : nat := 47.     Definition K_CP : nat := 48.
Definition K_MG : nat := 59.    Definition A_NB : nat := 63.    Definition K_MC : nat := 76.
Definition K_FR : nat := 87.
Definition Jregs : list reg := map R [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat.
Definition fact_len : afact := mkAF 0 (2 ^ 26) 0.
Definition fact_cap : afact := mkAF 65536 (2 ^ 26) 16.
Definition fact_want : afact := mkAF 1 65536 0.
Definition fact_n : afact := mkAF 1 65536 0.
Definition blkq_fact : afact := mkAF 4096 CEIL_MAX 4.
Definition X0 : sstate := Eval vm_compute in (runto_ RDPC ss_m1_ok).
Definition RD_regs : list sv :=
Eval vm_compute in (sr_set (sr_set (sr_sets (ss_regs X0) (junk_upd J0 Jregs)) 19%bv (SOff A_LEN 0)) 21%bv (SOff A_CAP 0)).
Definition RD_facts : facts :=
Eval vm_compute in (mkFacts ((A_LEN, fact_len) :: (A_CAP, fact_cap) :: f_atoms (ss_facts X0)) (f_conds (ss_facts X0)) (f_alias (ss_facts X0))).
Definition LH_mem : smem := Eval vm_compute in (ss_mem X0).
Definition S_RD : sstate := mkSS RDPC RD_regs LH_mem None RD_facts.
Definition LH_facts : facts := RD_facts.
Definition LH_cut : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep MAIN_SP ALLOC_STACK LH_mem).
Lemma LH_statics : drv_add_statics src0_msyms (map snd LH_cut) G_M1 = Some LH_mem.
Proof. vm_compute. reflexivity. Qed.
Definition sv_want : sv := SAlu ALU_ADD (SMd M_MUL (SOff A_LEN 0) (SLit (-1))) (SOff A_CAP 0).
Definition cWa : acond := mkAC BC_LTU sv_want (SLit 65536).
Definition cWb : acond := mkAC BC_GEU sv_want (SLit 65536).
Definition sv_len1 : sv := SAlu ALU_ADD (SOff A_LEN 0) (SOff A_N 0).
Definition cNE : acond := mkAC BC_NE sv_len1 (SOff A_CAP 0).
Definition cEQ : acond := mkAC BC_EQ sv_len1 (SOff A_CAP 0).
Definition sv_big : sv := SAlu ALU_SRL sv_len1 (SLit 26).
Definition cRF : acond := mkAC BC_NE sv_big (SLit 0).
Definition cGR : acond := mkAC BC_EQ sv_big (SLit 0).
Definition S_W : sstate := Eval vm_compute in (run_ S_RD).
Definition S_Wa : sstate := Eval vm_compute in (runto_ RWPC (add_cond S_W cWa)).
Definition S_Wb : sstate := Eval vm_compute in (runto_ RWPC (add_cond S_W cWb)).
Definition RW_regs : list sv := Eval vm_compute in (sr_set (ss_regs S_Wb) 12%bv (SOff A_WANT 0)).
Definition RW_facts : facts := Eval vm_compute in (mkFacts ((A_WANT, fact_want) :: f_atoms RD_facts) (f_conds RD_facts) (f_alias RD_facts)).
Definition S_RW : sstate := mkSS RWPC RW_regs LH_mem None RW_facts.
Definition S_RE : sstate := Eval vm_compute in (run_ S_RW).
Definition S_CP : sstate := Eval vm_compute in
(runto_ src0_A_memcpy (add_atom (resume S_RE (SOff A_N 0) (ss_mem S_RE) (ss_facts S_RE)) A_N fact_n)).
Definition S_CPp : sstate := Eval vm_compute in (memcpy_post S_CP RA_CP K_CP).
Definition S_T : sstate := Eval vm_compute in (run_ S_CPp).
Definition S_RDn : sstate := Eval vm_compute in (runto_ RDPC (add_cond S_T cNE)).
Definition S_CL : sstate := Eval vm_compute in (run_ (resume S_RE (SLit 0) (ss_mem S_RE) (ss_facts S_RE))).
Definition S_HDR : sstate := Eval vm_compute in (resume S_CL (SLit 0) (ss_mem S_CL) (ss_facts S_CL)).
Definition S_G : sstate := Eval vm_compute in (run_ (add_cond S_T cEQ)).
Definition S_RF : sstate := Eval vm_compute in (add_cond S_G cRF).
Definition S_MG : sstate := Eval vm_compute in (runto_ src0_A_malloc (add_cond S_G cGR)).
Definition L_MG : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep MAIN_SP ALLOC_STACK (ss_mem S_MG)).
Definition RS_MG : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd L_MG) (K_MG + 16) with Some x => x | None => [] end).
Definition S_MGp : sstate := Eval vm_compute in (post_state S_MG RA_MG K_MG RS_MG).
Definition S_MGn : sstate := Eval vm_compute in (mkSS (ss_pc S_MGp) (sr_set (ss_regs S_MGp) 10%bv (SLit 0)) (ss_mem S_MGp) None (ss_facts S_MGp)).
Definition S_MC : sstate := Eval vm_compute in (runto_ src0_A_memcpy (add_atom S_MGp A_NB blkq_fact)).
Definition S_MCp : sstate := Eval vm_compute in (memcpy_post S_MC RA_MC1 K_MC).
Definition S_FR : sstate := Eval vm_compute in (runto_ src0_A_free S_MCp).
Definition L_FR : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep MAIN_SP ALLOC_STACK (ss_mem S_FR)).
Definition RS_FR : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd L_FR) (K_FR + 16) with Some x => x | None => [] end).
Definition S_RD' : sstate := Eval vm_compute in (post_state S_FR RA_FR K_FR RS_FR).
Lemma S_W_facts : ss_pc S_W = src0_A_main + 0xd4 /\ sr_get (ss_regs S_Wa) 12%bv = sv_want /\ sr_get (ss_regs S_Wb) 12%bv = SLit 65536 /\
ss_pc S_Wa = RWPC /\ ss_pc S_Wb = RWPC /\ ss_mem S_Wa = LH_mem /\ ss_mem S_Wb = LH_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RE_facts : ss_pc S_RE = src0_A_syscall_cp_c + 0x1c /\ sr_get (ss_regs S_RE) 17%bv = SLit 63 /\ sr_get (ss_regs S_RE) 10%bv = SLit 3 /\
sr_get (ss_regs S_RE) 11%bv = SLit RS_LO /\ sr_get (ss_regs S_RE) 12%bv = SOff A_WANT 0 /\ ss_resv S_RE = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RE_dest : win_check (ss_mem S_RE) RS_LO 65536 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma read_stage_seg : seg_win_check src0segs RS_LO (Z.to_nat 65536) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma S_CL_facts : ss_pc S_CL = src0_A_syscall_cp_c + 0x1c /\ sr_get (ss_regs S_CL) 17%bv = SLit 57 /\ sr_get (ss_regs S_CL) 10%bv = SLit 3 /\ ss_resv S_CL = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_CP_facts : ss_pc S_CP = src0_A_memcpy /\ sr_get (ss_regs S_CP) 1%bv = SLit RA_CP /\
sr_get (ss_regs S_CP) 10%bv = SAlu ALU_ADD (SOff A_BUF 0) (SOff A_LEN 0) /\ sr_get (ss_regs S_CP) 11%bv = SLit RS_LO /\
sr_get (ss_regs S_CP) 12%bv = SOff A_N 0 /\ ss_resv S_CP = None /\ ss_mem S_CP = ss_mem S_RE.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_T_facts : ss_pc S_T = TPC /\ sr_get (ss_regs S_T) 19%bv = sv_len1 /\ sr_get (ss_regs S_T) 9%bv = SOff A_BUF 0 /\ ss_mem S_T = ss_mem S_RE.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RDn_facts : ss_pc S_RDn = RDPC /\ sr_get (ss_regs S_RDn) 19%bv = sv_len1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_G_facts : ss_pc S_G = src0_A_main + 0x98 /\ sr_get (ss_regs S_G) 10%bv = sv_big.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma refused_check : diag_exit_check K_MG S_RF msg_refused 2 = Some 2.
Proof. vm_compute. reflexivity. Qed.
Lemma site_MG : site_check src0_msyms S_MG src0_A_malloc RA_MG MAIN_SP src0_keep [] K_MG L_MG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statics_MG : drv_add_statics src0_msyms (map snd L_MG) (K_MG + 16) = Some RS_MG.
Proof. vm_compute. reflexivity. Qed.
Lemma S_MG_facts : sr_get (ss_regs S_MG) 10%bv = SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1)) /\
sr_get (ss_regs S_MGp) 10%bv = SOff A_NB 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma oom_check : diag_exit_check K_MC S_MGn msg_oom 2 = Some 2.
Proof. vm_compute. reflexivity. Qed.
Lemma ck_MC : memcpy_check S_MC RA_MC1 A_NB K_MC = true.
Proof. vm_compute. reflexivity. Qed.
Lemma S_MC_facts : sr_get (ss_regs S_MC) 10%bv = SOff A_NB 0 /\ sr_get (ss_regs S_MC) 11%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_MC) 12%bv = sv_len1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma site_FR : site_check src0_msyms S_FR src0_A_free RA_FR MAIN_SP src0_keep [] K_FR L_FR = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statics_FR : drv_add_statics src0_msyms (map snd L_FR) (K_FR + 16) = Some RS_FR.
Proof. vm_compute. reflexivity. Qed.
Lemma S_FR_facts : sr_get (ss_regs S_FR) 10%bv = SOff A_BUF 0.
Proof. vm_compute. reflexivity. Qed.
Lemma S_RD'_facts : ss_pc S_RD' = RDPC /\ sr_get (ss_regs S_RD') 9%bv = SOff A_NB 0 /\ sr_get (ss_regs S_RD') 19%bv = sv_len1 /\
sr_get (ss_regs S_RD') 21%bv = SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma L_FR_cut : map snd L_FR = map snd LH_cut.
Proof. vm_compute. reflexivity. Qed.
Definition back (rs : smem) : list (nat * YP09.region) := combine (seq 0 (length rs)) rs.
Lemma relayout_RDn : relayout_ok src0segs (ss_mem S_RDn) (back LH_mem) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma relayout_RD' : relayout_ok src0segs (ss_mem S_RD') (back (map snd LH_cut)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma relayout_X0 : relayout_ok src0segs (ss_mem X0) (back LH_mem) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma back_LH_mem : map snd (back LH_mem) = LH_mem.
Proof. vm_compute. reflexivity. Qed.
Lemma back_cut : map snd (back (map snd LH_cut)) = map snd LH_cut.
Proof. vm_compute. reflexivity. Qed.
Definition P_junk (n : nat) : bool := (n <? 29)%nat.
Definition P_X0 (n : nat) : bool := (n <? 10)%nat || (n =? 14)%nat || (n =? 26)%nat.
Lemma reabs_X0 : reabs_check P_X0 X0 RD_regs RD_facts = true.
Proof. vm_compute. reflexivity. Qed.
Definition P_W (n : nat) : bool := negb (n =? 46)%nat.
Lemma reabs_Wa : reabs_check P_W S_Wa RW_regs RW_facts = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reabs_Wb : reabs_check P_W S_Wb RW_regs RW_facts = true.
Proof. vm_compute. reflexivity. Qed.
Definition P_RDLH (n : nat) : bool := P_junk n && negb (n =? 27)%nat.
Lemma reabs_RDn : reabs_check P_RDLH S_RDn RD_regs RD_facts = true.
Proof. vm_compute. reflexivity. Qed.
Definition P_GR (n : nat) : bool := P_junk n && negb (n =? 14)%nat && negb (n =? 26)%nat && negb (n =? 27)%nat && negb (n =? 28)%nat.
Lemma reabs_RD' : reabs_check P_GR S_RD' RD_regs RD_facts = true.
Proof. vm_compute. reflexivity. Qed.
Definition P_26 (n : nat) : bool := negb (Nat.eqb n 26).
Lemma LH_mem_atoms : mem_atoms_pd P_GR PT (map snd LH_cut) = true /\ mem_atoms_pd (fun _ => true) (not_in [2%nat]) LH_mem = true /\
mem_atoms_pd P_26 PT (map snd LH_cut) = true /\ mem_atoms_pd P_RDLH PT LH_mem = true /\ mem_atoms_pd P_X0 (not_in [2%nat]) LH_mem = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_HDR_pd : ss_atoms_pd (fun _ => true) (not_in [2%nat]) S_HDR = true.
Proof. vm_compute. reflexivity. Qed.
Definition S_RDc : sstate := mkSS RDPC RD_regs (map snd LH_cut) None RD_facts.
Lemma S_RDc_pd : ss_atoms_pd P_26 PT S_RDc = true /\ ss_atoms_pd PT PT S_RD = true /\ ss_atoms_lt A_N S_RE = true /\ ss_atoms_lt K_CP S_CP = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma obl_X0 : forall E' regs,
(forall k r, nth_error Jregs (k - 29) = Some r -> (29 <= k)%nat -> ew E' k = getr regs r) ->
ew E' 27%nat = getr regs (R 19) -> ew E' 28%nat = getr regs (R 21) ->
Forall (fun rj : reg * nat => ew E' (snd rj) = getr regs (fst rj)) (reabs_obl P_X0 RD_regs).
Proof.
intros E' regs HJ H27 H28.
match goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change (Forall f l') end.
repeat (apply Forall_cons; [cbn [fst snd]; first [exact H27 | exact H28 | apply HJ; [reflexivity | lia]] |]). apply Forall_nil.
Qed.
Lemma obl_W : forall E' regs,
ew E' 46%nat = getr regs (R 12) ->
Forall (fun rj : reg * nat => ew E' (snd rj) = getr regs (fst rj)) (reabs_obl P_W RW_regs).
Proof.
intros E' regs H46.
match goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change (Forall f l') end.
repeat (apply Forall_cons; [cbn [fst snd]; exact H46 |]). apply Forall_nil.
Qed.
Lemma obl_RDn : forall E' regs,
(forall k r, nth_error Jregs (k - 29) = Some r -> (29 <= k)%nat -> ew E' k = getr regs r) ->
ew E' 27%nat = getr regs (R 19) ->
Forall (fun rj : reg * nat => ew E' (snd rj) = getr regs (fst rj)) (reabs_obl P_RDLH RD_regs).
Proof.
intros E' regs HJ H27.
match goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change (Forall f l') end.
repeat (apply Forall_cons; [cbn [fst snd]; first [exact H27 | apply HJ; [reflexivity | lia]] |]). apply Forall_nil.
Qed.
Lemma obl_RD : forall E' regs,
(forall k r, nth_error Jregs (k - 29) = Some r -> (29 <= k)%nat -> ew E' k = getr regs r) ->
ew E' 14%nat = getr regs (R 9) -> ew E' 27%nat = getr regs (R 19) -> ew E' 28%nat = getr regs (R 21) ->
Forall (fun rj : reg * nat => ew E' (snd rj) = getr regs (fst rj)) (reabs_obl P_GR RD_regs).
Proof.
intros E' regs HJ H14 H27 H28.
match goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change (Forall f l') end.
repeat (apply Forall_cons; [cbn [fst snd]; first [exact H14 | exact H27 | exact H28 | apply HJ; [reflexivity | lia]] |]). apply Forall_nil.
Qed.
Lemma fobl_X0 : fact_obls P_X0 RD_facts = [(27%nat, fact_len); (28%nat, fact_cap)].
Proof. vm_compute. reflexivity. Qed.
Lemma fobl_W : fact_obls P_W RW_facts = [(46%nat, fact_want)].
Proof. vm_compute. reflexivity. Qed.
Lemma fobl_RDn : fact_obls P_RDLH RD_facts = [(27%nat, fact_len)].
Proof. vm_compute. reflexivity. Qed.
Lemma fobl_RD : fact_obls P_GR RD_facts = [(27%nat, fact_len); (28%nat, fact_cap); (14%nat, mkAF 4096 CEIL_MAX 4)].
Proof. vm_compute. reflexivity. Qed.
End a.
