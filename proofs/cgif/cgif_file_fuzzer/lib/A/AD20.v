(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition lp_ranges : list (Z * nat) :=
drv_ranges ++
[(0x41910, 1%nat)     ;
(0x4361c, 22%nat)    ;
(0x436cc, 9%nat)     ;
(0x595ec, 13%nat)    ;
(0x92b9c, 1%nat)     ;
(0x8d2f8, 3%nat)     ].
Definition tfibtbl_lp : ctable := Eval vm_compute in build_ranges lp_ranges TEmpty.
Lemma tfibtbl_lp_eq : tfibtbl_lp = build_ranges lp_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tfibtbl_lp). Qed.
Lemma tfibtbl_lp_ok : table_ok tfibsegs tfibtbl_lp.
Proof. rewrite tfibtbl_lp_eq. apply build_ranges_ok; [repeat constructor; cbn; lia | apply table_ok_empty]. Qed.
Definition run_lp (ss : sstate) : sstate := fst (sym_runN tfibsegs tfibtbl_lp FUEL ss).
Definition runto_lp (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfibsegs tfibtbl_lp FUEL pc ss).
Definition RDPC : Z := 0x800bc.
Definition RWPC : Z := 0x800cc.
Definition TPC : Z := 0x80078.
Definition RA_RD : Z := 0x800d8.
Definition RA_CP : Z := 0x80070.
Definition RA_MG : Z := 0x80098.
Definition RA_MC1 : Z := 0x800b4.
Definition RA_FR : Z := 0x800bc.
Definition A_CHK : Z := 0x43674.
Definition A_CHK_END : Z := 0x436cc.
Definition A_HDR : Z := 0x800f0.
Definition A_RDERR : Z := 0x8021c.
Definition A_REFUSED : Z := 0x80238.
Definition A_OOM2 : Z := 0x80258.
Definition A_icpt_fprintf : Z := 0x4192c.
Definition RS_LO : Z := 0x5c8650.
Definition RS_HI : Z := 0x5d8650.
Definition R_inited : YP09.region := mkRegion None 0xa6cd8 0xa6cd9 0 0 [mkChunk 0xa6cd8 (CVal 1 (SLit 1))].
Definition R_realrd : YP09.region := mkRegion None 0x9fce8 0x9fcf0 0 0 [mkChunk 0x9fce8 (CVal 8 (SLit 0x9c998))].
Definition R_errno : YP09.region := mkRegion None 0x5d8eec 0x5d8ef0 0x5d8eec 0x5d8ef0 [].
Definition RT_REGIONS : smem := [R_inited; R_realrd; R_errno].
Definition A_BUF : nat := 46.   Definition A_LEN : nat := 58.   Definition A_CAP : nat := 59.   Definition J0 : nat := 60.
Definition A_WANT : nat := 77.  Definition A_N : nat := 78.
Definition K_CHK : nat := 79.
Definition K_CP : nat := 97.
Definition K_MG : nat := 113.
Definition A_NB : nat := 117.
Definition K_MC : nat := 129.
Definition K_FR : nat := 145.
Definition gkeep_at (spo : Z) (r : YP09.region) : bool :=
(forallb (fun c => match YP09.c_val c with CData _ _ _ => false | _ => true end) (r_chunks r) && drv_keep_ok spo r)%bool.
Definition gkeep : YP09.region -> bool := gkeep_at (-128).
Definition cNULL (k : nat) : acond := mkAC BC_EQ (SOff k 0) (SLit 0).
Definition cPTR (k : nat) : acond := mkAC BC_NE (SOff k 0) (SLit 0).
Definition Jregs : list reg := map (fun n => Z_to_bv 5 (Z.of_nat n)) [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat.
Definition fact_len : afact := mkAF 0 (2 ^ 26) 0.
Definition fact_cap : afact := mkAF 65536 (2 ^ 26) 16.
Definition fact_want : afact := mkAF 1 65536 0.
Definition fact_n : afact := mkAF 1 65536 0.
Definition blkq_fact : afact := mkAF 4096 (2 ^ 47) 4.
Definition X0 : sstate := ss_rd0.
Lemma X0_eq : X0 = runto_ RDPC (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition RD_regs : list sv :=
Eval vm_compute in (sr_set (sr_set (sr_sets (ss_regs X0) (junk_upd J0 Jregs)) 19%bv (SOff A_LEN 0)) 21%bv (SOff A_CAP 0)).
Definition RD_facts : facts :=
Eval vm_compute in (mkFacts ((A_LEN, fact_len) :: (A_CAP, fact_cap) :: f_atoms (ss_facts X0))
(List.filter (fun c => negb (acond_eqb c (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0)))) (f_conds (ss_facts X0)))
(f_alias (ss_facts X0))).
Definition LH_mem : smem := Eval vm_compute in (ss_mem X0 ++ RT_REGIONS).
Definition S_RD : sstate := mkSS RDPC RD_regs LH_mem None RD_facts.
Lemma X0_pc : ss_pc X0 = RDPC. Proof. reflexivity. Qed.
Example RD_regs_chk : nth 9 RD_regs (SLit 0) = SOff A_BUF 0 /\ nth 18 RD_regs (SLit 0) = SOff 2 0 /\ nth 20 RD_regs (SLit 0) = SLit 3
/\ nth 22 RD_regs (SLit 0) = SLit RS_LO /\ nth 8 RD_regs (SLit 0) = SLit 2 /\ nth 2 RD_regs (SLit 0) = SOff 0 (-128).
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition sv_want : sv := SAlu ALU_ADD (SMd M_MUL (SOff A_LEN 0) (SLit (-1))) (SOff A_CAP 0).
Definition cWa : acond := mkAC BC_LTU sv_want (SLit 65536).
Definition cWb : acond := mkAC BC_GEU sv_want (SLit 65536).
Definition sv_len1 : sv := SAlu ALU_ADD (SOff A_LEN 0) (SOff A_N 0).
Definition cNE : acond := mkAC BC_NE sv_len1 (SOff A_CAP 0).
Definition cEQ : acond := mkAC BC_EQ sv_len1 (SOff A_CAP 0).
Definition sv_big : sv := SAlu ALU_SRL sv_len1 (SLit 26).
Definition cRF : acond := mkAC BC_NE sv_big (SLit 0).
Definition cGR : acond := mkAC BC_EQ sv_big (SLit 0).
Definition S_W : sstate := Eval vm_compute in (run_lp S_RD).
Definition S_Wa : sstate := Eval vm_compute in (runto_lp RWPC (add_cond S_W cWa)).
Definition S_Wb : sstate := Eval vm_compute in (runto_lp RWPC (add_cond S_W cWb)).
Definition RW_regs : list sv := Eval vm_compute in (sr_set (ss_regs S_Wb) 12%bv (SOff A_WANT 0)).
Definition RW_facts : facts := Eval vm_compute in (mkFacts ((A_WANT, fact_want) :: f_atoms RD_facts) (f_conds RD_facts) (f_alias RD_facts)).
Definition S_RW : sstate := mkSS RWPC RW_regs LH_mem None RW_facts.
Definition S_RE : sstate := Eval vm_compute in (run_lp S_RW).
Definition S_CHK : sstate := Eval vm_compute in
(runto_lp A_CHK (add_atom (resume S_RE (SOff A_N 0) (ss_mem S_RE) (ss_facts S_RE)) A_N fact_n)).
Definition CLOB' : list reg := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition CLOB_CHK : list reg := CLOB' ++ [9; 18; 20]%bv.
Definition drop_below (cut : Z) (r : YP09.region) : YP09.region :=
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (List.filter (fun c => cut <=? c_off c) (r_chunks r)).
Definition ICPT_SP : Z := -128 - 2128.
Definition S_CHK' : sstate := Eval vm_compute in
mkSS A_CHK_END (sr_sets (ss_regs S_CHK) ([(10%bv, SOff A_N 0)] ++ junk_upd K_CHK CLOB_CHK))
(match ss_mem S_CHK with w :: rest => drop_below ICPT_SP w :: rest | [] => [] end) None (ss_facts S_CHK).
Definition S_CP : sstate := Eval vm_compute in (runto_lp A_icpt_memcpy S_CHK').
Definition rs_CP : smem := Eval vm_compute in List.filter gkeep (tl (ss_mem S_CP)).
Definition S_CPp : sstate := Eval vm_compute in (drv_after S_CP rs_CP K_CP RA_CP (-128)).
Definition S_T : sstate := Eval vm_compute in (run_lp S_CPp).
Definition S_RDn : sstate := Eval vm_compute in (runto_lp RDPC (add_cond S_T cNE)).
Definition S_CL : sstate := Eval vm_compute in (run_lp (resume S_RE (SLit 0) (ss_mem S_RE) (ss_facts S_RE))).
Definition S_HDR : sstate := Eval vm_compute in (run_lp (resume S_CL (SLit 0) (ss_mem S_CL) (ss_facts S_CL))).
Definition S_G : sstate := Eval vm_compute in (run_lp (add_cond S_T cEQ)).
Definition S_RF : sstate := Eval vm_compute in (run_lp (add_cond S_G cRF)).
Definition S_MG : sstate := Eval vm_compute in (runto_lp A_wrap_malloc (add_cond S_G cGR)).
Definition rs_MG : smem := Eval vm_compute in List.filter gkeep (tl (ss_mem S_MG)).
Definition S_MGp : sstate := Eval vm_compute in (drv_after S_MG rs_MG K_MG RA_MG (-128)).
Definition S_OOM2 : sstate := Eval vm_compute in (run_lp (add_cond S_MGp (cNULL A_NB))).
Definition S_MC : sstate := Eval vm_compute in (runto_lp A_icpt_memcpy (add_atom (add_cond S_MGp (cPTR A_NB)) A_NB blkq_fact)).
Definition rs_MC : smem := Eval vm_compute in List.filter gkeep (tl (ss_mem S_MC)).
Definition S_MCp : sstate := Eval vm_compute in (drv_after S_MC rs_MC K_MC RA_MC1 (-128)).
Definition S_FR : sstate := Eval vm_compute in (runto_lp A_wrap_free S_MCp).
Definition rs_FR : smem := Eval vm_compute in List.filter gkeep (tl (ss_mem S_FR)).
Definition S_RD' : sstate := Eval vm_compute in (drv_after S_FR rs_FR K_FR RA_FR (-128)).
Lemma S_W_facts : ss_pc S_W = 0x800c4 /\ sr_get (ss_regs S_Wa) 12%bv = sv_want /\ sr_get (ss_regs S_Wb) 12%bv = SLit 65536 /\
ss_pc S_Wa = RWPC /\ ss_pc S_Wb = RWPC /\ ss_mem S_Wa = LH_mem /\ ss_mem S_Wb = LH_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RE_facts : ss_pc S_RE = 0x97e7c /\ sr_get (ss_regs S_RE) 17%bv = SLit 63 /\ sr_get (ss_regs S_RE) 10%bv = SLit 3 /\
sr_get (ss_regs S_RE) 11%bv = SLit RS_LO /\ sr_get (ss_regs S_RE) 12%bv = SOff A_WANT 0 /\ ss_resv S_RE = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_CHK_facts : ss_pc S_CHK = A_CHK /\ sr_get (ss_regs S_CHK) 10%bv = SOff A_N 0 /\ sr_get (ss_regs S_CHK) 2%bv = SOff 0 ICPT_SP.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_CP_facts : ss_pc S_CP = A_icpt_memcpy /\ sr_get (ss_regs S_CP) 1%bv = SLit RA_CP /\
sr_get (ss_regs S_CP) 10%bv = SAlu ALU_ADD (SOff A_BUF 0) (SOff A_LEN 0) /\ sr_get (ss_regs S_CP) 11%bv = SLit RS_LO /\
sr_get (ss_regs S_CP) 12%bv = SOff A_N 0 /\ ss_resv S_CP = None /\ sr_get (ss_regs S_CP) 2%bv = SOff 0 (-128).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_T_facts : ss_pc S_T = TPC /\ sr_get (ss_regs S_T) 19%bv = sv_len1 /\ sr_get (ss_regs S_T) 9%bv = SOff A_BUF 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RDn_facts : ss_pc S_RDn = RDPC /\ sr_get (ss_regs S_RDn) 19%bv = sv_len1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_CL_facts : ss_pc S_CL = 0x97e7c /\ sr_get (ss_regs S_CL) 17%bv = SLit 57 /\ sr_get (ss_regs S_CL) 10%bv = SLit 3 /\ ss_resv S_CL = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_HDR_facts : ss_pc S_HDR = A_HDR /\ sr_get (ss_regs S_HDR) 9%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_HDR) 19%bv = SOff A_LEN 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_G_facts : ss_pc S_G = 0x80088 /\ sr_get (ss_regs S_G) 10%bv = sv_big.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RF_facts : ss_pc S_RF = A_icpt_fprintf /\ sr_get (ss_regs S_RF) 11%bv = SLit 0x196bf /\ sr_get (ss_regs S_RF) 12%bv = SLit 67108864 /\ sr_get (ss_regs S_RF) 1%bv = SLit 0x80254.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_MG_facts : ss_pc S_MG = A_wrap_malloc /\ sr_get (ss_regs S_MG) 1%bv = SLit RA_MG /\
sr_get (ss_regs S_MG) 10%bv = SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1)) /\ sr_get (ss_regs S_MGp) 10%bv = SOff A_NB 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_OOM2_facts : ss_pc S_OOM2 = A_icpt_fwrite /\ sr_get (ss_regs S_OOM2) 10%bv = SLit 0x147d6 /\ sr_get (ss_regs S_OOM2) 11%bv = SLit 19
/\ sr_get (ss_regs S_OOM2) 12%bv = SLit 1 /\ sr_get (ss_regs S_OOM2) 13%bv = SLit 0xa2578 /\ sr_get (ss_regs S_OOM2) 1%bv = SLit 0x80278.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_MC_facts : ss_pc S_MC = A_icpt_memcpy /\ sr_get (ss_regs S_MC) 1%bv = SLit RA_MC1 /\ sr_get (ss_regs S_MC) 10%bv = SOff A_NB 0 /\
sr_get (ss_regs S_MC) 11%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_MC) 12%bv = sv_len1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_FR_facts : ss_pc S_FR = A_wrap_free /\ sr_get (ss_regs S_FR) 1%bv = SLit RA_FR /\ sr_get (ss_regs S_FR) 10%bv = SOff A_BUF 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_RD'_facts : ss_pc S_RD' = RDPC /\ sr_get (ss_regs S_RD') 9%bv = SOff A_NB 0 /\ sr_get (ss_regs S_RD') 19%bv = sv_len1
/\ sr_get (ss_regs S_RD') 21%bv = SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma cp_checks : ss_atoms_lt K_CP S_CP = true /\ regions_wf (WIN (-128) :: rs_CP) = true /\ no_cdata rs_CP = true
/\ mem_atoms_lt K_CP (WIN (-128) :: rs_CP) = true /\ forallb (drv_keep_ok (-128)) rs_CP = true /\ rs_CP = List.filter gkeep (tl (ss_mem S_CP)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma mg_checks : ss_atoms_lt K_MG S_MG = true /\ regions_wf (WIN (-128) :: rs_MG) = true /\ no_cdata rs_MG = true
/\ mem_atoms_lt K_MG (WIN (-128) :: rs_MG) = true /\ forallb (drv_keep_ok (-128)) rs_MG = true /\ rs_MG = List.filter gkeep (tl (ss_mem S_MG)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma mc_checks : ss_atoms_lt K_MC S_MC = true /\ regions_wf (WIN (-128) :: rs_MC) = true /\ no_cdata rs_MC = true
/\ mem_atoms_lt K_MC (WIN (-128) :: rs_MC) = true /\ forallb (drv_keep_ok (-128)) rs_MC = true /\ rs_MC = List.filter gkeep (tl (ss_mem S_MC)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma fr_checks : ss_atoms_lt K_FR S_FR = true /\ regions_wf (WIN (-128) :: rs_FR) = true /\ no_cdata rs_FR = true
/\ mem_atoms_lt K_FR (WIN (-128) :: rs_FR) = true /\ forallb (drv_keep_ok (-128)) rs_FR = true /\ rs_FR = List.filter gkeep (tl (ss_mem S_FR)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rs_kept_eq : rs_CP = tl (ss_mem X0) /\ rs_MG = rs_CP /\ rs_MC = rs_CP /\ rs_FR = rs_CP /\ tl (ss_mem X0) = rs_m1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma mem_RDn : ss_mem S_RDn ++ RT_REGIONS = LH_mem /\ ss_mem S_RD' ++ RT_REGIONS = LH_mem.
Proof. vm_compute. split; reflexivity. Qed.
Lemma S_eq_certs : drv_after S_CP rs_CP K_CP RA_CP (-128) = S_CPp /\ run_lp S_CPp = S_T /\ runto_lp RDPC (add_cond S_T cNE) = S_RDn
/\ run_lp (add_cond S_T cEQ) = S_G /\ run_lp (add_cond S_G cRF) = S_RF /\ runto_lp A_wrap_malloc (add_cond S_G cGR) = S_MG
/\ drv_after S_MG rs_MG K_MG RA_MG (-128) = S_MGp /\ run_lp (add_cond S_MGp (cNULL A_NB)) = S_OOM2
/\ runto_lp A_icpt_memcpy (add_atom (add_cond S_MGp (cPTR A_NB)) A_NB blkq_fact) = S_MC /\ drv_after S_MC rs_MC K_MC RA_MC1 (-128) = S_MCp
/\ runto_lp A_wrap_free S_MCp = S_FR /\ drv_after S_FR rs_FR K_FR RA_FR (-128) = S_RD'.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition blk (H : word -> bool) (m : word -> option byte) (buf len : Z) (data : list byte) : Prop :=
forall i, 0 <= i < len -> mrestrict H m (Z_to_bv 64 (buf + i)) = nth_error data (Z.to_nat i).
Lemma blk_le : forall H m buf len len' data, blk H m buf len data -> len' <= len -> blk H m buf len' data.
Proof. intros H m buf len len' data HB Hle i Hi. apply HB. lia. Qed.
Lemma blk_bytes_at : forall H m buf data, blk H m buf (Z.of_nat (length data)) data <-> YP03.bytes_at (mrestrict H m) buf data.
Proof.
intros H m buf data. split.
- intros HB j Hj. rewrite <- (Nat2Z.id j) at 2. apply HB. lia.
- intros HB i Hi. rewrite <- (Z2Nat.id i) at 1 by lia. apply HB. lia.
Qed.
