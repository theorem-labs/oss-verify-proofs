(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK14 YP0m YP09 YP02 YP0l YP06 YP03 YP01 YN3v YI04 YL09 YK04 YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AD2j AD2i AD1t AD1y AD20 AD26 AD2h AD2f AD1s AD1w AD1x AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition JUNK : list (bv 5) := [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Fixpoint index_of (r : bv 5) (l : list (bv 5)) (i : nat) : nat := match l with [] => i | x :: t => if bv_eqb x r then i else index_of r t (S i) end.
Definition KJ : nat := 200.
Definition jregs (spo : Z) : list sv :=
map (fun i : nat => if Nat.eqb i 0 then SLit 0 else if Nat.eqb i 2 then SOff 0 spo else if Nat.eqb i 3 then SLit TFIB_GP else if Nat.eqb i 4 then SLit TFIB_TP
else SOff (KJ + index_of (Z_to_bv 5 (Z.of_nat i)) JUNK 0)%nat 0) (seq 0 32).
Definition E_J (E : YP0m.env) (regs : bvmap 5 word) : YP0m.env := havoc E KJ (map (getr regs) JUNK).
Definition JFR_chunks : list YP09.chunk :=
[mkChunk (-120) (CVal 8 (SLit 0)); mkChunk (-112) (CVal 8 (SLit 0)); mkChunk (-104) (CVal 8 (SLit 0)); mkChunk (-96) (CVal 8 (SLit 0)); mkChunk (-88) (CVal 8 (SOff 4 0));
mkChunk (-80) (CVal 8 (SLit 524272)); mkChunk (-72) (CVal 8 (SOff 3 0)); mkChunk (-64) (CVal 8 (SOff 0 8)); mkChunk (-56) (CVal 8 (SLit 577284))].
Definition JFR : YP09.region := mkRegion (Some 0%nat) (-128) 0 (-128) 0 JFR_chunks.
Definition noG : facts := mkFacts [] [] [].
Definition JW (spo : Z) : YP09.region := mkRegion (Some 0%nat) spo 0 spo 0 [].
Definition jmemI (I : smem) (spo : Z) (wf : bool) : smem := WIN spo :: (if wf then JFR else JW spo) :: I.
Definition jmem (spo : Z) (wf : bool) : smem := jmemI IMG_X spo wf.
Definition jmemL (spo : Z) (wf : bool) : smem := jmemI IMG_XL spo wf.
Definition XIok (I : smem) : Prop := I = IMG_X \/ I = IMG_XL.
Definition S_J7 : sstate := Eval vm_compute in mkSS 0x80278 (jregs (-128)) (jmem (-128) false) None noG.
Definition S_J5 : sstate := Eval vm_compute in mkSS 0x80254 (jregs (-128)) (jmem (-128) false) None noG.
Definition S_JX : sstate := Eval vm_compute in mkSS 0x8cf04 (jregs (-48)) (jmemL (-48) false) None noG.
Definition S_JU : sstate := Eval vm_compute in mkSS 0x801a4 (sr_set (jregs (-128)) 8%bv (SLit 2)) (jmem (-128) true) None noG.
Definition S_JF : sstate := Eval vm_compute in mkSS 0x801e4 (sr_set (sr_set (jregs (-128)) 8%bv (SLit 2)) 9%bv (SOff A_BUF 0)) (jmem (-128) true) None noG.
Lemma S_J_defs :
S_J7 = mkSS 0x80278 (jregs (-128)) (jmemI IMG_X (-128) false) None noG /\ S_J5 = mkSS 0x80254 (jregs (-128)) (jmemI IMG_X (-128) false) None noG /\
S_JX = mkSS 0x8cf04 (jregs (-48)) (jmemI IMG_XL (-48) false) None noG /\
S_JU = mkSS 0x801a4 (sr_set (jregs (-128)) 8%bv (SLit 2)) (jmemI IMG_X (-128) true) None noG /\
S_JF = mkSS 0x801e4 (sr_set (sr_set (jregs (-128)) 8%bv (SLit 2)) 9%bv (SOff A_BUF 0)) (jmemI IMG_X (-128) true) None noG.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition tbl_x : ctable := Eval vm_compute in build_ranges [(0x8cf04, 1%nat)] tfibtbl_lp.
Lemma tbl_x_eq : tbl_x = build_ranges [(0x8cf04, 1%nat)] tfibtbl_lp. Proof. vm_cast_no_check (eq_refl tbl_x). Qed.
Lemma tbl_x_ok : table_ok tfibsegs tbl_x.
Proof. rewrite tbl_x_eq. apply build_ranges_ok; [repeat constructor; cbn; lia | exact tfibtbl_lp_ok]. Qed.
Definition run_x (ss : sstate) : sstate := fst (sym_runN tfibsegs tbl_x FUEL ss).
Definition S_J7x : sstate := Eval vm_compute in run_x S_J7.
Definition S_J5x : sstate := Eval vm_compute in run_x S_J5.
Definition S_JXx : sstate := Eval vm_compute in run_x S_JX.
Definition S_JUx : sstate := Eval vm_compute in run_x S_JU.
Definition S_JFc : sstate := Eval vm_compute in run_x S_JF.
Definition K_JF : nat := 230.
Definition RA_JF : Z := 0x801ec.
Definition S_JFr : sstate := Eval vm_compute in drv_after S_JFc (JFR :: IMG_X) K_JF RA_JF (-128).
Definition S_JFx : sstate := Eval vm_compute in run_x S_JFr.
Lemma S_Jx_eq : run_x S_J7 = S_J7x /\ run_x S_J5 = S_J5x /\ run_x S_JX = S_JXx /\ run_x S_JU = S_JUx /\ run_x S_JF = S_JFc /\ run_x S_JFr = S_JFx
/\ drv_after S_JFc (JFR :: IMG_X) K_JF RA_JF (-128) = S_JFr.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition XSTS : list sstate := [S_J7x; S_J5x; S_JXx; S_JUx; S_JFx].
Lemma XSTS_facts : Forall (fun s => ss_pc s = A_exit /\ sr_get (ss_regs s) 3%bv = SLit TFIB_GP /\ sr_get (ss_regs s) 4%bv = SLit TFIB_TP /\ ss_resv s = None
/\ atom_lookup (f_atoms (ss_facts s)) 8%nat = None) XSTS.
Proof. vm_compute. repeat (constructor; [repeat split; reflexivity|]). constructor. Qed.
Lemma XSTS_regs :
map (fun s => (sr_get (ss_regs s) 10%bv, sr_get (ss_regs s) 2%bv, sr_get (ss_regs s) 1%bv)) XSTS
= [(SLit 2, SOff 0 (-128), SLit 0x80280); (SLit 2, SOff 0 (-128), SLit 0x80280); (SOff 206 0, SOff 0 (-48), SLit 0x8cf08);
(SLit 2, SOff 0 (-48), SLit 0x8cf08); (SLit 2, SOff 0 (-48), SLit 0x8cf08)]
/\ map ss_mem XSTS = [jmem (-128) false; jmem (-128) false; jmemL (-48) false; jmem (-128) true; jmem (-128) true].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_JFc_facts : ss_pc S_JFc = 0x5292c /\ sr_get (ss_regs S_JFc) 10%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_JFc) 1%bv = SLit RA_JF /\
sr_get (ss_regs S_JFc) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_JFc) 8%bv = SLit 2 /\ sr_get (ss_regs S_JFc) 3%bv = SLit TFIB_GP /\
sr_get (ss_regs S_JFc) 4%bv = SLit TFIB_TP /\ ss_mem S_JFc = jmem (-128) true /\ ss_resv S_JFc = None /\ ss_mem S_JFr = jmem (-128) true /\ ss_mem S_JF = jmem (-128) true
/\ ss_mem S_JU = jmem (-128) true /\ ss_mem S_J7 = jmem (-128) false /\ ss_mem S_J5 = jmem (-128) false /\ ss_mem S_JX = jmemL (-48) false.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma jf_checks : ss_atoms_lt K_JF S_JFc = true /\ regions_wf (WIN (-128) :: JFR :: IMG_X) = true /\ no_cdata (JFR :: IMG_X) = true /\
mem_atoms_lt K_JF (WIN (-128) :: JFR :: IMG_X) = true /\ forallb (drv_keep_ok (-128)) (JFR :: IMG_X) = true /\ submem (JFR :: IMG_X) (ss_mem S_JFc).
Proof. vm_compute. repeat split; try reflexivity. apply submem_drop. apply submem_refl. Qed.
Definition fact_err : afact := mkAF (2 ^ 64 - 4095) (2 ^ 64 - 1) 0.
Definition A_NEGE : nat := 42.
Definition G_CO : facts := mkFacts ((A_NEGE, fact_err) :: f_atoms (ss_facts ss_open)) (f_conds (ss_facts ss_open)) (f_alias (ss_facts ss_open)).
Definition S_COr : sstate := resume ss_open (SOff A_NEGE 0) (ss_mem ss_open) G_CO.
Definition S_CO : sstate := Eval vm_compute in mkSS (ss_pc S_COr) (ss_regs S_COr) (ss_mem S_COr ++ [R_errno]) None (ss_facts S_COr).
Lemma S_CO_eq : S_CO = mkSS (ss_pc S_COr) (ss_regs S_COr) (ss_mem S_COr ++ [R_errno]) None (ss_facts S_COr). Proof. vm_compute. reflexivity. Qed.
Definition S_CO1 : sstate := Eval vm_compute in run_x S_CO.
Definition sv_nege : sv := SAluw ALU_ADD (SOff A_NEGE 0) (SLit 0).
Definition LIT_M4095 : Z := 18446744073709547521.
Definition cond_CO : acond := mkAC BC_GEU sv_nege (SLit LIT_M4095).
Definition S_COf : sstate := Eval vm_compute in run_x (add_cond S_CO1 cond_CO).
Definition cond_US : acond := mkAC BC_NE (SOff 3 0) (SLit 2).
Definition S_US : sstate := Eval vm_compute in run_x (add_cond ss_pro_f cond_US).
Lemma S_COUS_eq : run_x S_CO = S_CO1 /\ run_x (add_cond S_CO1 cond_CO) = S_COf /\ run_x (add_cond ss_pro_f cond_US) = S_US /\ run_ (ss_main false) = ss_pro_f.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_CO1_facts : ss_pc S_CO1 = 0x8d964 /\ sr_get (ss_regs S_CO1) 10%bv = sv_nege /\ sr_get (ss_regs S_CO1) 11%bv = SLit LIT_M4095 /\ ss_resv S_CO1 = None
/\ ss_mem S_CO1 = ss_mem S_CO /\ ss_atoms_lt A_NEGE ss_open = true /\ regions_wf [R_errno] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_COf_facts : ss_pc S_COf = 0x4192c /\ sr_get (ss_regs S_COf) 1%bv = SLit 0x80254 /\ sr_get (ss_regs S_COf) 2%bv = SOff 0 (-128) /\
sr_get (ss_regs S_COf) 10%bv = SLit 0xa2578 /\ sr_get (ss_regs S_COf) 11%bv = SLit 0x1d727 /\ sr_get (ss_regs S_COf) 12%bv = SOff 2 0 /\
sr_get (ss_regs S_COf) 3%bv = SLit TFIB_GP /\ sr_get (ss_regs S_COf) 4%bv = SLit TFIB_TP /\ ss_resv S_COf = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_US_facts : ss_pc S_US = 0x4192c /\ sr_get (ss_regs S_US) 1%bv = SLit 0x801a4 /\ sr_get (ss_regs S_US) 2%bv = SOff 0 (-128) /\
sr_get (ss_regs S_US) 10%bv = SLit 0xa2578 /\ sr_get (ss_regs S_US) 11%bv = SLit 0x15859 /\ sr_get (ss_regs S_US) 12%bv = SOff 1 0 /\
sr_get (ss_regs S_US) 3%bv = SLit TFIB_GP /\ sr_get (ss_regs S_US) 4%bv = SLit TFIB_TP /\ sr_get (ss_regs S_US) 8%bv = SLit 2 /\ ss_resv S_US = None
/\ ss_pc ss_pro_f = A_argc_test /\ ss_resv ss_pro_f = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_COf_mem : exists cs, hd R_errno (ss_mem S_COf) = mkRegion (Some 0%nat) (-65536) 0 (-65536) 0 cs /\ skipn 4 (ss_mem S_COf) = IMG_REGIONS ++ [hd R_errno (skipn 37 (ss_mem S_COf))]
/\ r_base (hd R_errno (skipn 37 (ss_mem S_COf))) = None /\ r_lo (hd R_errno (skipn 37 (ss_mem S_COf))) = 0x5d8eec /\ r_hi (hd R_errno (skipn 37 (ss_mem S_COf))) = 0x5d8ef0
/\ length (ss_mem S_COf) = 38%nat.
Proof. eexists. vm_compute. repeat split; reflexivity. Qed.
Lemma S_US_mem : hd R_errno (ss_mem S_US) = mkRegion (Some 0%nat) (-65536) 0 (-65536) 0 JFR_chunks /\ skipn 3 (ss_mem S_US) = IMG_REGIONS /\ length (ss_mem S_US) = 36%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition ext_chk2 (r1 r2 : YP09.region) : bool :=
match r_base r1, r_base r2 with
| None, None => (r_hi r1 <=? r_lo r2) || (r_hi r2 <=? r_lo r1)
| Some 0%nat, None => (-65536 <=? r_lo r1) | Some (1 | 2 | 6)%nat, None => (0 <=? r_lo r1) | _, _ => false end%bool.
Lemma S_CO_ext : forallb (fun r1 => ext_chk2 r1 R_errno) (ss_mem ss_open) = true /\ forallb drv_win_ok (ss_mem S_CO) = true /\ forallb drv_win_ok (ss_mem ss_pro_f) = true
/\ wr_below_sp (ss_facts S_COf) (ss_mem S_CO) = true /\ wr_below_sp (ss_facts S_US) (ss_mem ss_pro_f) = true /\ wr_below_sp (ss_facts ss_pro_f) (ss_mem (ss_main false)) = true
/\ forallb drv_win_ok (ss_mem (ss_main false)) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition se_ext_ok (r : YP09.region) : bool := ext_avoids (r_lo r) (r_hi r) (F_STDERR_LO, F_STDERR_HI - F_STDERR_LO).
Definition is_abs (r : YP09.region) : bool := match r_base r with None => true | _ => false end.
Definition win_avoids (lo hi : Z) (r : YP09.region) : bool :=
((r_whi r <=? r_wlo r) || match r_base r with Some 0%nat => (-65536 <=? r_wlo r) | Some _ => false
| None => (r_whi r <=? lo) || (hi <=? r_wlo r) end)%bool.
Definition se_win_ok (r : YP09.region) : bool := win_avoids F_STDERR_LO F_STDERR_HI r.
Definition sx_win_ok (r : YP09.region) : bool := (win_avoids STDOUT_LO STDOUT_HI r && win_avoids SOBUF_LO SOBUF_HI r)%bool.
Lemma IMG_X_keep : forallb (drv_keep_ok (-128)) IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_X_abs : forallb is_abs IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_X_se : forallb se_ext_ok IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_X_nocdata : no_cdata IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_X_atM1 : mem_atoms_lt K_M1 IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_X_atKJ : mem_atoms_lt KJ IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_X_wf : regions_wf IMG_X = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_keep : forallb (drv_keep_ok (-128)) IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_abs : forallb is_abs IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_se : forallb se_ext_ok IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_nocdata : no_cdata IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_atM1 : mem_atoms_lt K_M1 IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_atKJ : mem_atoms_lt KJ IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XL_wf : regions_wf IMG_XL = true. Proof. vm_compute. reflexivity. Qed.
Lemma XI_checks : forall I, XIok I -> forallb (drv_keep_ok (-128)) I = true /\ forallb is_abs I = true /\ forallb se_ext_ok I = true /\ no_cdata I = true
/\ mem_atoms_lt K_M1 I = true /\ mem_atoms_lt KJ I = true /\ regions_wf I = true.
Proof. intros I [-> | ->]; repeat split; vm_compute; reflexivity. Qed.
Lemma JFR_at : forallb (fun c => cval_atoms_lt KJ (YP09.c_val c)) JFR_chunks = true. Proof. vm_compute. reflexivity. Qed.
Lemma jmemI_checks : forall I spo wf, XIok I -> (spo = -128 \/ spo = -48) ->
forallb drv_win_ok (jmemI I spo wf) = true /\ forallb se_win_ok (jmemI I spo wf) = true /\ forallb sx_win_ok (jmemI I spo wf) = true /\ regions_wf (jmemI I spo wf) = true
/\ mem_atoms_lt KJ (jmemI I spo wf) = true.
Proof. intros I spo wf [-> | ->] [-> | ->]; destruct wf; vm_compute; repeat split; reflexivity. Qed.
Lemma jmem_checks : forall spo wf, (spo = -128 \/ spo = -48) ->
forallb drv_win_ok (jmem spo wf) = true /\ forallb se_win_ok (jmem spo wf) = true /\ forallb sx_win_ok (jmem spo wf) = true /\ regions_wf (jmem spo wf) = true
/\ mem_atoms_lt KJ (jmem spo wf) = true.
Proof. intros spo wf H. exact (jmemI_checks IMG_X spo wf (or_introl eq_refl) H). Qed.
Definition clipX1 (r : YP09.region) : smem :=
flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1))
(flat_map (clip_out F_STDERR_LO F_STDERR_HI) (flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r))).
Definition XR_pieces : list smem := Eval vm_compute in map clipX1 IMG_REGIONS.
Definition XL_pieces : list smem := Eval vm_compute in map (fun r => flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1)) (clip_out F_STDERR_LO F_STDERR_HI r)) IMG_L.
Lemma X_pieces_eq : concat XR_pieces = IMG_X /\ concat XL_pieces = IMG_XL. Proof. vm_compute. split; reflexivity. Qed.
Lemma XR_pieces_unfold : XR_pieces = map clipX1 IMG_REGIONS. Proof. vm_compute. reflexivity. Qed.
Lemma XL_pieces_unfold : XL_pieces = map (fun r => flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1)) (clip_out F_STDERR_LO F_STDERR_HI r)) IMG_L.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_RL_lohi : forallb (fun r => r_lo r <=? r_hi r) IMG_REGIONS = true /\ forallb (fun r => r_lo r <=? r_hi r) IMG_L = true.
Proof. vm_compute. split; reflexivity. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma refines_R_X : forall E3 (m : word -> option byte), refines E3 m IMG_REGIONS XR_pieces.
Proof.
intros E3 m. rewrite XR_pieces_unfold. apply refines_map. intros r Hr.
pose proof (proj1 (forallb_forall _ _) (proj1 IMG_RL_lohi) r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh. unfold clipX1.
apply flat_map_pieces_ok; [| intros q _ Hq; apply clip_out_ok; [unfold A_INITFLAGB, A_INITFLAG; lia | exact Hq]].
apply flat_map_pieces_ok; [| intros q _ Hq; apply clip_out_ok; [unfold F_STDERR_LO, F_STDERR_HI; lia | exact Hq]].
apply flat_map_pieces_ok; [| intros q _ Hq; apply clip_out_ok; [unfold SOBUF_LO, SOBUF_HI; lia | exact Hq]].
apply clip_out_ok; [unfold STDOUT_LO, STDOUT_HI; lia | exact Hlh].
Qed.
Lemma refines_L_X : forall E3 (m : word -> option byte), refines E3 m IMG_L XL_pieces.
Proof.
intros E3 m. rewrite XL_pieces_unfold. apply refines_map. intros r Hr.
pose proof (proj1 (forallb_forall _ _) (proj2 IMG_RL_lohi) r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply flat_map_pieces_ok; [| intros q _ Hq; apply clip_out_ok; [unfold A_INITFLAGB, A_INITFLAG; lia | exact Hq]].
apply clip_out_ok; [unfold F_STDERR_LO, F_STDERR_HI; lia | exact Hlh].
Qed.
Lemma mem_ok_X_of_R : forall E (m : word -> option byte), mem_ok tfibsegs E m IMG_REGIONS -> mem_ok tfibsegs E m IMG_X.
Proof. intros E m HM. rewrite <- (proj1 X_pieces_eq). apply (mem_ok_refine E m IMG_REGIONS XR_pieces HM (refines_R_X E m)). rewrite (proj1 X_pieces_eq). exact IMG_X_wf. Qed.
Lemma mem_ok_XL_of_L : forall E (m : word -> option byte), mem_ok tfibsegs E m IMG_L -> mem_ok tfibsegs E m IMG_XL.
Proof. intros E m HM. rewrite <- (proj2 X_pieces_eq). apply (mem_ok_refine E m IMG_L XL_pieces HM (refines_L_X E m)). rewrite (proj2 X_pieces_eq). exact IMG_XL_wf. Qed.
Lemma E_J_old : forall E regs j, (j < KJ)%nat -> ew (E_J E regs) j = ew E j.
Proof. intros E regs j Hj. unfold E_J. apply ew_havoc_old. exact Hj. Qed.
Lemma E_J_new : forall E regs i r, (i < 28)%nat -> nth i JUNK 0%bv = r -> ew (E_J E regs) (KJ + i) = getr regs r.
Proof. intros E regs i r Hi <-. unfold E_J. rewrite (ew_havoc_new E KJ _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. Qed.
Lemma E_J_ed : forall E regs, ed (E_J E regs) = ed E. Proof. intros; reflexivity. Qed.
Lemma regs_ok_J : forall E regs (spo usp : Z),
bv_unsigned (ew E 0) = usp -> spZ regs = usp + spo -> sp_window_lo <= usp -> -128 <= spo <= 0 ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
regs_ok (E_J E regs) (jregs spo) regs.
Proof.
intros E regs spo usp E0 Hsp Ulo Hspo R3 R4. unfold sp_window_lo in Ulo.
pose proof (E_J_old E regs) as Eold. pose proof (E_J_new E regs) as NEW.
apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?E' (sr_get ?sr ?r) => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| exact R3 | exact R4
|   rewrite (Eold 0%nat) by (unfold KJ; lia); rewrite E0, <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
| rewrite Z.add_0_r;
match goal with |- getr regs ?x = Z_to_bv 64 (bv_unsigned (ew _ ?a)) =>
let i := eval vm_compute in (a - KJ)%nat in
replace a with (KJ + i)%nat by reflexivity; rewrite (NEW i x) by (first [cbn; lia | vm_compute; reflexivity]) end;
rewrite Z_to_bv_bv_unsigned; reflexivity ]
| ]).
destruct Hr.
Qed.
Lemma regs_ok_ovr : forall E sr regs (r : bv 5) v,
regs_ok E sr regs -> bv_eqb r 0%bv = false -> getr regs r = sv_denot E v -> regs_ok E (sr_set sr r v) regs.
Proof.
intros E sr regs r v HR Hr0 Hv. pose proof (regs_ok_set E sr regs r (getr regs r) v HR (eq_sym Hv)) as X. rewrite Hr0 in X.
assert (Hr : r <> 0%bv) by (intros ->; discriminate Hr0).
intros r'. rewrite <- (X r'). destruct (bv_eqb r' r) eqn:EQ.
- apply (proj1 (Fs.bv_eqb_eq r' r)) in EQ. subst r'. rewrite (getr_same regs r _ Hr). reflexivity.
- rewrite (getr_other regs r _ r'); [reflexivity|]. intros ->. rewrite bv_eqb_refl in EQ. discriminate EQ.
Qed.
Lemma st_ok_J : forall (XI : smem) E regs sr (spo pc usp : Z) (wf : bool) (H : word -> bool) (mem : word -> option byte), XIok XI ->
regs_ok (E_J E regs) sr regs ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp -> (spo = -128 \/ (spo = -48 /\ wf = false)) ->
mem_ok tfibsegs E (mrestrict H mem) XI -> (forall a, usp - 65536 <= a < usp -> apresent H mem a) ->
(wf = true -> Forall (chunk_ok tfibsegs E (mrestrict H mem) usp) JFR_chunks) ->
st_ok tfibsegs (E_J E regs) (mkSS pc sr (jmemI XI spo wf) None noG) (mkst regs (Z_to_bv 64 pc) (mrestrict H mem) (seg_rom tfibsegs)).
Proof.
intros XI E regs sr spo pc usp wf H mem HI HR E0 Ulo Hspo HM Hwin Hfr. unfold sp_window_lo in Ulo. set (m := mrestrict H mem) in *.
pose proof (XI_checks XI HI) as (IMG_X_keep & IMG_X_abs & _ & _ & _ & IMG_X_atKJ & _).
pose proof (E_J_old E regs) as Eold. pose proof (u64_range (ew E 0)) as U0.
assert (AG : env_agree KJ E (E_J E regs)) by (split; [intros j Hj; exact (Eold j Hj) | reflexivity]).
pose proof (jmemI_checks XI spo wf HI ltac:(lia)) as (_ & _ & _ & Jwf & _).
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact HR|].
split; [| split; [constructor | split; exact I]].
assert (HM' : mem_ok tfibsegs (E_J E regs) m XI).
{ apply (mem_ok_agree tfibsegs KJ E); [exact AG | exact IMG_X_atKJ | exact HM]. }
destruct HM' as (Hwf & Hok & Hpd).
assert (WINOK : region_ok tfibsegs (E_J E regs) m (WIN spo)).
{ split; [cbn [base_val r_base r_lo WIN]; rewrite (Eold 0%nat) by (unfold KJ; lia); lia|].
split; [cbn [base_val r_base r_hi WIN]; rewrite (Eold 0%nat) by (unfold KJ; lia); lia|].
split; [| constructor]. cbn [base_val r_base r_wlo r_whi WIN]. rewrite (Eold 0%nat) by (unfold KJ; lia). rewrite E0.
intros o Ho. apply (apresent_writable tfibsegs). apply Hwin. lia. }
assert (DISJ : forall lo hi, -65536 <= lo -> hi <= 0 -> Forall (extent_disjoint (E_J E regs) (YP09.mkRegion (Some 0%nat) lo hi lo hi [])) XI).
{ intros lo hi Hlo Hhi. apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) IMG_X_keep r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (forallb_forall _ _) IMG_X_abs r Hr) as Ha. unfold is_abs in Ha.
unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite (Eold 0%nat) by (unfold KJ; lia). rewrite E0.
destruct (r_base r) as [bb|]; [discriminate Ha|].
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
cbn [base_val]. lia. }
split; [exact Jwf|].
assert (Hlo : exists lo, -128 <= lo <= 0 /\ lo <= spo /\ (wf = false -> lo = spo) /\ r_lo (if wf then JFR else JW spo) = lo /\ r_wlo (if wf then JFR else JW spo) = lo
/\ r_hi (if wf then JFR else JW spo) = 0 /\ r_whi (if wf then JFR else JW spo) = 0 /\ r_base (if wf then JFR else JW spo) = Some 0%nat
/\ r_chunks (if wf then JFR else JW spo) = (if wf then JFR_chunks else [])).
{ exists (if wf then -128 else spo). destruct wf; (repeat split; try reflexivity; try lia); try (intros X; discriminate X); try (intros _; reflexivity). }
destruct Hlo as (lo & Hlo & Hlospo & Hlowf & L1 & L2 & L3 & L4 & L5 & L6).
assert (FROK : region_ok tfibsegs (E_J E regs) m (if wf then JFR else JW spo)).
{ unfold region_ok. rewrite L1, L2, L3, L4, L5, L6. cbn [base_val]. rewrite (Eold 0%nat) by (unfold KJ; lia).
split; [lia|]. split; [lia|]. split.
+ rewrite E0. intros o Ho. apply (apresent_writable tfibsegs). apply Hwin. lia.
+ rewrite E0. destruct wf; [| constructor].
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (Hfr eq_refl) c Hc) as X.
intros i Hi. destruct (X i Hi) as (b & Hb1 & Hb2). exists b. split; [| exact Hb2].
rewrite <- Hb1. apply (cbyte_agree tfibsegs KJ E (E_J E regs)); [exact AG|].
exact (proj1 (forallb_forall _ _) JFR_at c Hc). }
assert (Hspo' : wf = true \/ lo = spo) by (destruct wf; [left; reflexivity | right; exact (Hlowf eq_refl)]).
assert (Hlo2 : (wf = true -> spo = -128)) by (intros ->; lia).
assert (Hlo3 : lo = spo \/ (lo = -128 /\ spo = -128)) by (destruct Hspo' as [Hw|Hw]; [right; split; [| exact (Hlo2 Hw)]; subst wf; cbn in L1; congruence | left; exact Hw]).
split.
- constructor; [exact WINOK|]. constructor; [exact FROK | exact Hok].
- split.
+ split; [| apply (proj2 (all_disjoint_Forall _ _ _)); exact (DISJ (-65536) spo ltac:(lia) ltac:(lia))].
unfold extent_disjoint. rewrite L1, L3, L5. cbn [r_base r_lo r_hi WIN base_val]. lia.
+ split; [| exact Hpd]. apply (proj2 (all_disjoint_Forall _ _ _)).
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) (DISJ lo 0 ltac:(lia) ltac:(lia)) r Hr) as X.
unfold extent_disjoint in X |- *. rewrite L1, L3, L5. cbn [r_base r_lo r_hi base_val] in X |- *. exact X.
Qed.
Lemma img_at_of_cimg : forall E (H : word -> bool) m lo l w1 w2 a b,
region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion None lo (lo + l) w1 w2 [YP09.mkChunk lo (CImg l)]) -> lo <= a -> b <= lo + l ->
img_at H m a b.
Proof.
intros E H m lo l w1 w2 a b (_ & _ & _ & HC) Ha Hb x Hx. cbn [r_chunks r_base base_val] in HC.
pose proof (Forall_inv HC) as Hc. destruct (Hc (x - lo) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2.
unfold img_byte in Hb1. replace (0 + lo + (x - lo)) with x in Hb1, Hb2 by lia. unfold aview. rewrite Hb2, <- Hb1. reflexivity.
Qed.
Lemma imgs_of_R : forall E (H : word -> bool) m, mem_ok tfibsegs E (mrestrict H m) IMG_REGIONS ->
stdout_img H m /\ img_at H m F_STDERR_LO F_STDERR_HI.
Proof.
intros E H m (_ & Hok & _).
assert (Hr : region_ok tfibsegs E (mrestrict H m) R_A3) by (apply (proj1 (Forall_forall _ _) Hok); unfold IMG_REGIONS; cbn; tauto).
unfold R_A3 in Hr. change 665712 with (664880 + 832) in Hr.
split; [unfold stdout_img | ]; eapply (img_at_of_cimg E H m 664880 832); try exact Hr; unfold STDOUT_LO, STDOUT_HI, F_STDERR_LO, F_STDERR_HI; lia.
Qed.
Lemma stderr_of_L : forall E (H : word -> bool) m, mem_ok tfibsegs E (mrestrict H m) IMG_L -> img_at H m F_STDERR_LO F_STDERR_HI.
Proof.
intros E H m (_ & Hok & _).
assert (Hr : region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion None 664880 (664880 + 312) 664880 665192 [YP09.mkChunk 664880 (CImg 312)])).
{ apply (proj1 (Forall_forall _ _) Hok). unfold IMG_L. cbn. tauto. }
eapply (img_at_of_cimg E H m 664880 312); [exact Hr | |]; unfold F_STDERR_LO, F_STDERR_HI; lia.
Qed.
Lemma aview_frame_off : forall E rs (H : word -> bool) m m' a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hw. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite u64_lit by exact Ha. exact Hw.
Qed.
Lemma aview_kept_run : forall (lo hi : Z) E rs (H : word -> bool) m m' a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (win_avoids lo hi) rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
0 <= lo -> hi <= 0x5fb000 -> lo <= a < hi -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros lo hi E rs H m m' a HF Hok U0 Hlo Hhi Ha.
apply (aview_frame_off E rs H m m' a HF ltac:(lia)). intros (r & Hr & Hw).
pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X. unfold win_avoids in X.
apply orb_prop in X as [X|X]; [apply Z.leb_le in X; lia|]. unfold sp_window_lo in U0.
destruct (r_base r) as [[|n]|]; try discriminate X; cbn [base_val] in Hw.
- apply Z.leb_le in X. lia.
- apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma stdout_img_run : forall E rs (H : word -> bool) m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb sx_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
stdout_img H m -> stdout_img H m'.
Proof.
intros E rs H m m' HF Hok U0 HI a Ha.
assert (H1 : forallb (win_avoids STDOUT_LO STDOUT_HI) rs = true).
{ apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X. unfold sx_win_ok in X. apply andb_prop in X. tauto. }
rewrite (aview_kept_run STDOUT_LO STDOUT_HI E rs H m m' a HF H1 U0 ltac:(unfold STDOUT_LO; lia) ltac:(unfold STDOUT_HI; lia) Ha). exact (HI a Ha).
Qed.
End d.
