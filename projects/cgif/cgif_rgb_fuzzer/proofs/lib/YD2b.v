(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK00 YQ0j YQ0b YQ03 YQ0i YQ09 YQ04 YQ0e YQ0a YO3p YO3v YI00 YL07 YL02 YL03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YB1u YF9j YD2f YD2e YD1p YD1v YD1t YD1z YD2d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YCe8 YCrd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition add0 (x : sv) : sv := SAlu ALU_ADD x (SLit 0).
Definition sv_cl00 : sv := add0 (add0 sv_cl).
Definition sv_pl : sv := SAlu ALU_ADD (SAlu ALU_SUB (SOff A_LEN 0) sv_cl) (SLit (-6)).
Definition sv_pl00 : sv := add0 (add0 sv_pl).
Definition sv_calls : sv := SAlu ALU_ADD (SAlu ALU_AND (SData 2 2 1) (SLit 3)) (SLit 1).
Definition A_TR_B : Z := 0x810e8.
Definition A_TR_Q0 : Z := 0x81144.
Definition A_TR_Q1 : Z := 0x810f8.
Definition RA_PM : Z := 0x81104.
Definition RA_PC : Z := 0x81118.
Definition A_INITFLAG : Z := 0x5dd8d0.
Definition A_EMPTY_tfa : Z := 0x5dd8e0.
Definition K_PP : nat := 161.
Definition R161 : YQ0b.region := YQ0b.mkRegion (Some 161%nat) 0 4 0 0 [mkChunk 0 (CData 3 0 4)].
Definition RBh (h : Z) : YQ0b.region := YQ0b.mkRegion (Some A_BUF) 0 h 0 0 [mkChunk 0 (CData 2 0 h)].
Definition fact_P : afact := mkAF 4098 140737479966720 0.
Definition S_Pm : sstate := Eval vm_compute in mkSS (ss_pc S_P) (ss_regs S_P) (removelast (ss_mem S_P)) None (ss_facts S_P).
Definition ssP (h : Z) : sstate :=
mkSS (ss_pc S_P) (sr_set (ss_regs S_P) 10%bv (SOff 161 0))
(ss_mem S_Pm ++ [RBh h; R161]) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_P)) (f_conds (ss_facts S_P)) (f_alias (ss_facts S_P))).
Definition ssP0 : sstate := Eval vm_compute in (ssP 2).
Definition ssP1 : sstate := Eval vm_compute in (ssP 3).
Definition sB0 : sstate := Eval vm_compute in (run_lp ssP0).
Definition sB1 : sstate := Eval vm_compute in (run_lp ssP1).
Definition cond_CL0 : acond := mkAC BC_EQ sv_cl00 (SLit 0).
Definition cond_CL1 : acond := mkAC BC_NE sv_cl00 (SLit 0).
Definition cond_PL0 : acond := mkAC BC_EQ sv_pl00 (SLit 0).
Definition cond_PL1 : acond := mkAC BC_NE sv_pl00 (SLit 0).
Definition sQ0 : sstate := Eval vm_compute in (run_lp (add_cond sB0 cond_CL0)).
Definition sQ1 : sstate := Eval vm_compute in (run_lp (add_cond sB1 cond_CL1)).
Definition setreg_ (r : reg) (v : sv) (ss : sstate) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition sQ1k (k : Z) : sstate := setreg_ 21%bv (SLit k) sQ1.
Definition sQ (c0 : bool) (k : Z) : sstate := if c0 then sQ0 else sQ1k k.
Definition sPM (c0 : bool) (k : Z) : sstate := run_lp (add_cond (sQ c0 k) cond_PL1).
Definition sPE (c0 : bool) (k : Z) : sstate := run_lp (add_cond (sQ c0 k) cond_PL0).
Definition sPM0 : sstate := Eval vm_compute in sPM true 1.
Definition sPE0 : sstate := Eval vm_compute in sPE true 1.
Definition sPM1 (k : Z) : sstate := Eval vm_compute in sPM false k.
Definition sPE1 (k : Z) : sstate := Eval vm_compute in sPE false k.
Definition IMG_E : smem := firstn 32 (skipn 3 (ss_mem sPE0)).
Lemma S_Pm_facts : ss_mem S_P = ss_mem S_Pm ++ [blkreg6] /\ ss_pc S_Pm = A_P /\ ss_resv S_Pm = None /\ ss_regs S_Pm = ss_regs S_P
/\ ss_facts S_Pm = ss_facts S_P /\ regions_wf (ss_mem S_Pm) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_Pm_pd : ss_atoms_pd (fun n => negb (Nat.eqb n 161)) (not_in [3%nat]) S_Pm = true. Proof. vm_compute. reflexivity. Qed.
Lemma ssP_eq : ssP 2 = ssP0 /\ ssP 3 = ssP1. Proof. vm_compute. split; reflexivity. Qed.
Lemma RBh_wf : forall h, 2 <= h <= 3 -> regions_wf [RBh h; R161] = true.
Proof. intros h Hh. assert (h = 2 \/ h = 3) as [-> | ->] by lia; reflexivity. Qed.
Lemma S_Pm_hext : forallb hext_chk (ss_mem S_Pm) = true. Proof. vm_compute. reflexivity. Qed.



Lemma sBQ_facts : ss_pc sB0 = A_TR_B /\ ss_pc sB1 = A_TR_B /\ ss_pc sQ0 = A_TR_Q0 /\ ss_pc sQ1 = A_TR_Q1
/\ sr_get (ss_regs sB0) 18%bv = sv_cl00 /\ sr_get (ss_regs sB1) 18%bv = sv_cl00
/\ sr_get (ss_regs sQ0) 21%bv = SLit 1 /\ sr_get (ss_regs sQ1) 21%bv = sv_calls
/\ sr_get (ss_regs sQ0) 8%bv = sv_pl00 /\ sr_get (ss_regs sQ1) 8%bv = sv_pl00
/\ ss_resv sB0 = None /\ ss_resv sB1 = None /\ ss_resv sQ0 = None /\ ss_resv sQ1 = None
/\ ss_mem sQ0 = ss_mem sB0 /\ ss_mem sQ1 = ss_mem sB1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sPM0_facts : ss_pc sPM0 = A_wrap_malloc /\ sr_get (ss_regs sPM0) 10%bv = add0 sv_pl00 /\ sr_get (ss_regs sPM0) 1%bv = SLit RA_PM
/\ sr_get (ss_regs sPM0) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs sPM0) 8%bv = sv_pl00 /\ sr_get (ss_regs sPM0) 21%bv = SLit 1
/\ sr_get (ss_regs sPM0) 9%bv = SOff 161 4 /\ ss_resv sPM0 = None /\ ss_mem sPM0 = ss_mem sB0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sPE0_facts : ss_pc sPE0 = A_LLVMF /\ sr_get (ss_regs sPE0) 10%bv = SLit A_EMPTY_tfa /\ sr_get (ss_regs sPE0) 11%bv = add0 sv_pl00
/\ sr_get (ss_regs sPE0) 1%bv = SLit RA_LLVMF /\ sr_get (ss_regs sPE0) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs sPE0) 8%bv = sv_pl00
/\ sr_get (ss_regs sPE0) 9%bv = SLit A_EMPTY_tfa /\ sr_get (ss_regs sPE0) 18%bv = SLit 0 /\ sr_get (ss_regs sPE0) 21%bv = SLit 1
/\ ss_resv sPE0 = None /\ ss_mem sPE0 = firstn 3 (ss_mem sB0) ++ IMG_E ++ skipn 35 (ss_mem sB0).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sPM1_facts : forall k, ss_pc (sPM1 k) = A_wrap_malloc /\ sr_get (ss_regs (sPM1 k)) 10%bv = add0 sv_pl00 /\ sr_get (ss_regs (sPM1 k)) 1%bv = SLit RA_PM
/\ sr_get (ss_regs (sPM1 k)) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs (sPM1 k)) 8%bv = sv_pl00 /\ sr_get (ss_regs (sPM1 k)) 21%bv = SLit k
/\ sr_get (ss_regs (sPM1 k)) 9%bv = SOff 161 4 /\ ss_resv (sPM1 k) = None /\ ss_mem (sPM1 k) = ss_mem sB1.
Proof. intros k. vm_compute. repeat split; reflexivity. Qed.
Lemma sPE1_facts : forall k, ss_pc (sPE1 k) = A_LLVMF /\ sr_get (ss_regs (sPE1 k)) 10%bv = SLit A_EMPTY_tfa /\ sr_get (ss_regs (sPE1 k)) 11%bv = add0 sv_pl00
/\ sr_get (ss_regs (sPE1 k)) 1%bv = SLit RA_LLVMF /\ sr_get (ss_regs (sPE1 k)) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs (sPE1 k)) 8%bv = sv_pl00
/\ sr_get (ss_regs (sPE1 k)) 9%bv = SLit A_EMPTY_tfa /\ sr_get (ss_regs (sPE1 k)) 18%bv = SLit 0 /\ sr_get (ss_regs (sPE1 k)) 21%bv = SLit k
/\ ss_resv (sPE1 k) = None /\ ss_mem (sPE1 k) = firstn 3 (ss_mem sB1) ++ IMG_E ++ skipn 35 (ss_mem sB1).
Proof. intros k. vm_compute. repeat split; reflexivity. Qed.
Lemma ssP0_win_ok : forallb drv_win_ok (ss_mem ssP0) = true. Proof. reflexivity. Qed.
Lemma ssP1_win_ok : forallb drv_win_ok (ss_mem ssP1) = true. Proof. reflexivity. Qed.

Lemma skel_B : skeleton (ss_mem sB0) = skeleton (ss_mem ssP0) /\ skeleton (ss_mem sB1) = skeleton (ss_mem ssP1).
Proof. vm_compute. split; reflexivity. Qed.

Lemma wbs_Q : wr_below_sp (ss_facts sQ0) (ss_mem ssP0) = true /\ wr_below_sp (ss_facts sQ1) (ss_mem ssP1) = true.
Proof. vm_compute. split; reflexivity. Qed.

Definition E_P (E : YQ0j.env) (data : list byte) (pP : Z) : YQ0j.env :=
ewset (edset E 3 (skipn (Z.to_nat (2 + config_len data)) data)) 161 (Z_to_bv 64 pP).
Lemma E_P_agree : forall E data pP, env_agree_pd (fun n => negb (Nat.eqb n 161)) (not_in [3%nat]) E (E_P E data pP).
Proof.
intros E data pP. split.
- intros n Hn. unfold E_P, ewset, edset. cbn [ew]. destruct (Nat.eqb_spec n 161); [subst; discriminate | reflexivity].
- intros d Hd. unfold E_P, ewset, edset. cbn [ed]. unfold not_in in Hd. cbn in Hd.
destruct (Nat.eqb_spec d 3); [subst; discriminate | reflexivity].
Qed.
Lemma E_P_old : forall E data pP n, n <> 161%nat -> ew (E_P E data pP) n = ew E n.
Proof. intros. unfold E_P. rewrite ew_ewset_other by assumption. reflexivity. Qed.
Lemma E_P_161 : forall E data pP, 0 <= pP < 2 ^ 64 -> bv_unsigned (ew (E_P E data pP) 161) = pP.
Proof. intros. unfold E_P. rewrite ew_ewset_same. apply u64_lit. lia. Qed.
Lemma E_P_ed3 : forall E data pP, ed (E_P E data pP) 3 = skipn (Z.to_nat (2 + config_len data)) data.
Proof. intros. reflexivity. Qed.
Lemma E_P_ed : forall E data pP d, d <> 3%nat -> ed (E_P E data pP) d = ed E d.
Proof. intros E data pP d Hd. unfold E_P, ewset, edset. cbn [ed]. destruct (Nat.eqb_spec d 3); [contradiction | reflexivity]. Qed.
Definition K_L : nat := 162.
Definition WIN208 : YQ0b.region := YQ0b.mkRegion (Some 0%nat) (-65536) (-208) (-65536) (-208) [].
Definition TRF : YQ0b.region :=
match ss_mem sB1 with
| r :: _ => YQ0b.mkRegion (Some 0%nat) (-208) (-128) (-208) (-128) (List.filter (fun c => -208 <=? YQ0b.c_off c) (r_chunks r))
| [] => WIN208
end.
Definition clip_chunk (lo hi : Z) (c : YQ0b.chunk) : list YQ0b.chunk :=
let a := YQ0b.c_off c in let l := c_len c in
let a' := Z.max a lo in let b' := Z.min (a + l) hi in
if b' <=? a' then [] else
match YQ0b.c_val c with
| CImg _ => [mkChunk a' (CImg (b' - a'))]
| CZero _ => [mkChunk a' (CZero (b' - a'))]
| CVal w v => if ((lo <=? a) && (a + l <=? hi))%bool then [c] else []
| CData d s _ => [mkChunk a' (CData d (s + (a' - a)) (b' - a'))]
end.
Definition clip_region (lo hi : Z) (r : YQ0b.region) : YQ0b.region :=
YQ0b.mkRegion (r_base r) (Z.max (r_lo r) lo) (Z.min (r_hi r) hi)
(if (r_whi r <=? r_wlo r)%bool then 0 else Z.max (r_wlo r) lo) (if (r_whi r <=? r_wlo r)%bool then 0 else Z.min (r_whi r) hi)
(flat_map (clip_chunk lo hi) (r_chunks r)).
Definition STDOUT_LO : Z := 0xa7930.  Definition STDOUT_HI : Z := 0xa7a18.
Definition SOBUF_LO : Z := 0x5fe918.   Definition SOBUF_HI : Z := 0x5fed28.
Definition IMG_B : smem := firstn 32 (skipn 3 (ss_mem sB1)).
Definition clip_out (lo hi : Z) (r : YQ0b.region) : list YQ0b.region :=
if ((hi <=? r_lo r) || (r_hi r <=? lo))%bool then [r] else
(if (r_lo r <? lo)%bool then [clip_region (r_lo r) lo r] else []) ++ (if (hi <? r_hi r)%bool then [clip_region hi (r_hi r) r] else []).
Definition IMG_L : smem := Eval vm_compute in flat_map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_B.
Definition IMG_LC : smem := Eval vm_compute in flat_map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_E.
Definition L_regs : list sv :=
[SLit 0; SLit RA_LLVMF; SOff 0 (-208); SLit 67584; SLit 6152720; SOff 167 0; SOff 168 0; SOff 169 0;
SOff 162 0; SOff 163 0; SOff 163 0; SOff 162 0; SOff 170 0; SOff 171 0; SOff 172 0; SOff 173 0;
SOff 174 0; SOff 175 0; SOff 164 0; SOff 165 0; SLit A_INITFLAG; SOff 166 0; SLit 0; SLit 18446744073709551614;
SLit 0; SLit 0; SLit 0; SLit 0; SOff 176 0; SOff 177 0; SOff 178 0; SOff 179 0].
Definition fact_n : afact := mkAF 0 (2 ^ 26) 0.
Definition fact_p : afact := mkAF 4096 (2 ^ 47) 0.
Definition fact_q : afact := mkAF 0 (2 ^ 47) 0.
Definition fact_r : afact := mkAF 1 4 0.
Definition L_facts : facts :=
mkFacts ((162%nat, fact_n) :: (163%nat, fact_p) :: (164%nat, fact_q) :: (166%nat, fact_r) :: (161%nat, fact_P) :: f_atoms (ss_facts S_P)) [] [].
Definition L_mem : smem := Eval vm_compute in ([WIN208; TRF] ++ firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_LC).
Definition S_L : sstate := mkSS A_LLVMF L_regs L_mem None L_facts.
Lemma L_mem_wf : regions_wf L_mem = true /\ mem_atoms_lt K_L L_mem = true /\ length IMG_L = 34%nat /\ forallb drv_win_ok L_mem = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition LT162 (j : nat) : bool := (j <? 162)%nat.
Definition L_srcs : list (bv 5) := [8; 9; 18; 19; 21; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition E_L (E3 : YQ0j.env) (regs : bvmap 5 word) : YQ0j.env := havoc E3 K_L (map (getr regs) L_srcs).
Lemma L_fact_obls_eq : fact_obls LT162 L_facts = [(162%nat, fact_n); (163%nat, fact_p); (164%nat, fact_q); (166%nat, fact_r)].
Proof. vm_compute. reflexivity. Qed.
Lemma reabs_chk_PE : reabs_check LT162 sPE0 L_regs L_facts = true /\ forall k, reabs_check LT162 (sPE1 k) L_regs L_facts = true.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Definition L_pieces : list smem :=
[ [WIN208; TRF] ] ++ map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_E ++ [ []; []; []; []; [] ].

Definition L_piecesC : list smem := Eval vm_compute in L_pieces.
Lemma L_piecesC_eq : L_piecesC = L_pieces /\ concat L_piecesC = L_mem. Proof. vm_compute. split; reflexivity. Qed.
Lemma sPE_mem : ss_mem sPE0 = firstn 3 (ss_mem sB0) ++ IMG_E ++ skipn 35 (ss_mem sB0) /\ (forall k, ss_mem (sPE1 k) = firstn 3 (ss_mem sB1) ++ IMG_E ++ skipn 35 (ss_mem sB1))
/\ ss_pc sPE0 = A_LLVMF /\ (forall k, ss_pc (sPE1 k) = A_LLVMF)
/\ ss_resv sPE0 = None /\ (forall k, ss_resv (sPE1 k) = None).
Proof. repeat split; intros; vm_compute; reflexivity. Qed.
Lemma sPE_eq : sPE true 1 = sPE0 /\ forall k, sPE false k = sPE1 k. Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Lemma sQ_win_ok : forallb drv_win_ok (ss_mem sQ0) = true /\ forall k, forallb drv_win_ok (ss_mem (sQ1k k)) = true.
Proof. split; [| intros k]; reflexivity. Qed.

Lemma wbs_PM : wr_below_sp (ss_facts sPM0) (ss_mem sQ0) = true /\ forall k, wr_below_sp (ss_facts (sPM1 k)) (ss_mem (sQ1k k)) = true.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Lemma sPM_eq : sPM true 1 = sPM0 /\ forall k, sPM false k = sPM1 k. Proof. split; [| intros k]; vm_compute; reflexivity. Qed.

Definition K_PM : nat := 180.
Definition A_PBLK : nat := 184.
Definition gkeep208 : YQ0b.region -> bool := gkeep_at (-208).
Definition rs_PM (c0 : bool) (k : Z) : smem := TRF :: List.filter gkeep208 (tl (ss_mem (if c0 then sPM0 else sPM1 k))).
Definition S_PMr0 : sstate := Eval vm_compute in drv_after sPM0 (rs_PM true 1) K_PM RA_PM (-208).
Definition S_PMr1 (k : Z) : sstate := Eval vm_compute in drv_after (sPM1 k) (rs_PM false k) K_PM RA_PM (-208).
Definition S_PMr (c0 : bool) (k : Z) : sstate := if c0 then S_PMr0 else S_PMr1 k.
Definition A_CM : Z := 0x80f44.
Definition S_PF0 : sstate := Eval vm_compute in run_lp (add_cond S_PMr0 (cNULL A_PBLK)).
Definition S_PF1 (k : Z) : sstate := Eval vm_compute in run_lp (add_cond (S_PMr1 k) (cNULL A_PBLK)).
Definition S_PC0 : sstate := Eval vm_compute in run_lp (add_cond S_PMr0 (cPTR A_PBLK)).
Definition S_PC1 (k : Z) : sstate := Eval vm_compute in run_lp (add_cond (S_PMr1 k) (cPTR A_PBLK)).




Definition TRF0 : YQ0b.region := YQ0b.mkRegion (Some 0%nat) (-208) (-128) (-208) (-128) [].
Definition K_CM : nat := 180.
Definition CM_regs : list sv :=
[SLit 0; SLit A_CM; SOff 0 (-128); SLit 67584; SLit 6152720; SOff 182 0; SOff 183 0; SOff 184 0;
SOff A_BUF 2; SOff A_BUF 0; SOff 180 0; SOff 185 0; SOff 186 0; SOff 187 0; SOff 188 0; SOff 189 0;
SOff 190 0; SOff 191 0; sv_cl; SOff 161 4; sv_pl; sv_b1s; SLit RS_LO; SLit 0;
SLit 0; SLit 0; SLit 0; SLit 0; SOff 192 0; SOff 193 0; SOff 194 0; SOff 195 0].
Definition fact_v : afact := mkAF 0 2 0.
Definition CM_facts : facts := mkFacts ((180%nat, fact_v) :: (161%nat, fact_P) :: f_atoms (ss_facts S_P)) [] [].
Definition CM_mem : smem := Eval vm_compute in (WIN208 :: TRF0 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_L).
Definition S_CM : sstate := mkSS A_CM CM_regs CM_mem None CM_facts.
Definition LT180 (j : nat) : bool := (j <? 180)%nat.
Definition CM_srcs : list (bv 5) := [10; 10; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition E_CM (E : YQ0j.env) (regs : bvmap 5 word) : YQ0j.env := havoc E K_CM (map (getr regs) CM_srcs).
Definition cond_CMt : acond := mkAC BC_LT sv_b1s (SLit 0).
Definition cond_CMf : acond := mkAC BC_GE sv_b1s (SLit 0).
Definition S_FBt : sstate := Eval vm_compute in run_lp (add_cond S_CM cond_CMt).
Definition S_FBf : sstate := Eval vm_compute in run_lp (add_cond S_CM cond_CMf).
Definition K_FB : nat := 196.
Definition rs_FB : smem := Eval vm_compute in List.filter gkeep (ss_mem S_FBt).
Definition RA_FB : Z := 0x80fcc.
Definition S_FBrt : sstate := Eval vm_compute in drv_after S_FBt rs_FB K_FB RA_FB (-128).
Definition S_FBrf : sstate := Eval vm_compute in drv_after S_FBf rs_FB K_FB RA_FB (-128).
Definition A_XT : Z := 0x9214c.
Definition S_XTt : sstate := Eval vm_compute in run_lp S_FBrt.
Definition S_XTf : sstate := Eval vm_compute in run_lp S_FBrf.
Lemma CM_mem_wf : regions_wf CM_mem = true /\ mem_atoms_lt K_CM CM_mem = true /\ forallb drv_win_ok CM_mem = true /\ skipn 4 CM_mem = IMG_L /\ firstn 2 (skipn 2 CM_mem) = firstn 2 (skipn 2 L_mem).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma CM_fact_obls_eq : fact_obls LT180 CM_facts = [(180%nat, fact_v)]. Proof. vm_compute. reflexivity. Qed.

Lemma S_FB_facts : ss_pc S_FBt = A_wrap_free /\ ss_pc S_FBf = A_wrap_free /\ sr_get (ss_regs S_FBt) 1%bv = SLit RA_FB /\ sr_get (ss_regs S_FBf) 1%bv = SLit RA_FB
/\ sr_get (ss_regs S_FBt) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_FBf) 2%bv = SOff 0 (-128)
/\ sr_get (ss_regs S_FBt) 8%bv = SLit 0 /\ sr_get (ss_regs S_FBf) 8%bv = SOff 180 0 /\ sr_get (ss_regs S_FBt) 10%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_FBf) 10%bv = SOff A_BUF 0
/\ ss_resv S_FBt = None /\ ss_resv S_FBf = None /\ ss_mem S_FBt = CM_mem /\ ss_mem S_FBf = CM_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma fb_checks : ss_atoms_lt K_FB S_FBt = true /\ ss_atoms_lt K_FB S_FBf = true /\ regions_wf (WIN (-128) :: rs_FB) = true /\ no_cdata rs_FB = true
/\ mem_atoms_lt K_FB (WIN (-128) :: rs_FB) = true /\ forallb (drv_keep_ok (-128)) rs_FB = true /\ rs_FB = List.filter gkeep CM_mem /\ skipn 2 rs_FB = IMG_L.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_XT_facts : ss_pc S_XTt = A_XT /\ ss_pc S_XTf = A_XT /\ sr_get (ss_regs S_XTt) 10%bv = SLit 0 /\ sr_get (ss_regs S_XTf) 10%bv = SOff 180 0
/\ sr_get (ss_regs S_XTt) 2%bv = SOff 0 (-48) /\ sr_get (ss_regs S_XTf) 2%bv = SOff 0 (-48)
/\ ss_mem S_XTt = WIN (-128) :: rs_FB /\ ss_mem S_XTf = WIN (-128) :: rs_FB /\ ss_resv S_XTt = None /\ ss_resv S_XTf = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma S_FBr_win_ok : forallb drv_win_ok (WIN (-128) :: rs_FB) = true. Proof. reflexivity. Qed.
Lemma S_FBr_eq : drv_after S_FBt rs_FB K_FB RA_FB (-128) = S_FBrt /\ drv_after S_FBf rs_FB K_FB RA_FB (-128) = S_FBrf.
Proof. vm_compute. split; reflexivity. Qed.
Lemma S_XT_regs : sr_get (ss_regs S_XTt) 3%bv = SLit 67584 /\ sr_get (ss_regs S_XTf) 3%bv = SLit 67584
/\ sr_get (ss_regs S_XTt) 4%bv = SLit 6152720 /\ sr_get (ss_regs S_XTf) 4%bv = SLit 6152720.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition so_win_ok (r : YQ0b.region) : bool :=
((r_whi r <=? r_wlo r) || match r_base r with Some 0%nat => (-65536 <=? r_wlo r) | Some _ => false | None =>
((r_whi r <=? STDOUT_LO) || (STDOUT_HI <=? r_wlo r)) && ((r_whi r <=? SOBUF_LO) || (SOBUF_HI <=? r_wlo r)) end)%bool.
Lemma CM_so_ok : forallb so_win_ok CM_mem = true /\ forallb so_win_ok (WIN (-128) :: rs_FB) = true /\ forallb so_win_ok L_mem = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma IMG_L_wf : regions_wf IMG_L = true. Proof. reflexivity. Qed.
