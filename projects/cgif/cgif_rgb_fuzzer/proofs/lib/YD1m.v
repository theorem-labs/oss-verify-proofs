(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK00 YK0i YK14 YK1b YK15 YK0l YK18 YK0q YQ0k YK0s YN02
YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0e YQ0c YO3p YO3v YI00 YL08 YL07 YL02 YL03
YK05 YA0i YA0l YA0m YA0n YA0k YK0a YA0e
YG00 YG01 YG0m YG0h YG10 YG0u YG0d YCcz YB1u YB11 YF9i YB1g
YB12 YF9j YD2f YD2e YD1p YD1v YD1q YD1t YD21 YD1z YE31   YCe8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YD1w YD20 YD1y YD2d YD1r YD2b YD26 YD2c YD1o YD28 YD29 YD24 YD2a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition RA_EMITC : Z := 0x8117c.
Definition A_BNEZ : Z := 0x8118c.
Definition RA_FQ : Z := 0x81198.
Definition K_LR : nat := 180.
Definition S_LR : sstate := Eval vm_compute in mkSS RA_LLVMF (sr_sets L_regs ([(10%bv, SLit 0)] ++ junk_upd K_LR CLOB')) L_mem None L_facts.
Definition S_VP : sstate := Eval vm_compute in run_lp S_LR.
Definition L_mem0 : smem := Eval vm_compute in ss_mem S_VP.
Definition K_VP : nat := 196.
Definition S_VPr : sstate := Eval vm_compute in mkSS RA_EMIT (sr_sets (ss_regs S_VP) ([(10%bv, SLit 2)] ++ junk_upd K_VP CLOB')) (ss_mem S_VP) None (ss_facts S_VP).
Definition S_BR : sstate := Eval vm_compute in run_lp S_VPr.
Definition cond_BRt : acond := mkAC BC_NE (SOff 166 (-1)) (SLit 0).
Definition cond_BRf : acond := mkAC BC_EQ (SOff 166 (-1)) (SLit 0).
Definition S_L2 : sstate := Eval vm_compute in run_lp (add_cond S_BR cond_BRt).
Definition S_FQ : sstate := Eval vm_compute in run_lp (add_cond S_BR cond_BRf).
Definition K_FQ : nat := 212.
Definition rsFQ : smem := Eval vm_compute in List.filter gkeep208 (tl (ss_mem S_FQ)).
Definition S_FQr : sstate := Eval vm_compute in drv_after S_FQ rsFQ K_FQ RA_FQ (-208).
Definition S_XM : sstate := Eval vm_compute in run_lp S_FQr.
Definition LT165 (j : nat) : bool := (j <? 165)%nat.
Definition L2_srcs : list (bv 5) := [19; 21; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition E_L2 (E : YQ0j.env) (regs : bvmap 5 word) : YQ0j.env := havoc E 165 (map (getr regs) L2_srcs).
Definition XM_pieces : list smem := map (fun r => [r]) CM_mem.
Definition cval_eqb (a b : cval) : bool :=
match a, b with
| CVal w v, CVal w' v' => (N.eqb w w' && sv_eqb v v')%bool
| CZero l, CZero l' => Z.eqb l l' | CImg l, CImg l' => Z.eqb l l'
| CData d o l, CData d' o' l' => (Nat.eqb d d' && Z.eqb o o' && Z.eqb l l')%bool
| _, _ => false
end.
Definition chunk_eqb (a b : YQ0b.chunk) : bool := (Z.eqb (YQ0b.c_off a) (YQ0b.c_off b) && cval_eqb (YQ0b.c_val a) (YQ0b.c_val b))%bool.
Definition obase_eqb (a b : option nat) : bool := match a, b with None, None => true | Some x, Some y => Nat.eqb x y | _, _ => false end.
Definition subregion_chk (r' r : YQ0b.region) : bool :=
(obase_eqb (r_base r') (r_base r) && (r_lo r <=? r_lo r') && (r_hi r' <=? r_hi r) && (r_lo r' <=? r_hi r')
&& ((r_whi r' <=? r_wlo r') || ((r_wlo r <=? r_wlo r') && (r_whi r' <=? r_whi r)))
&& forallb (fun c => existsb (chunk_eqb c) (r_chunks r)) (r_chunks r'))%bool.
Fixpoint subregions_chk (rs' rs : smem) : bool :=
match rs', rs with [], [] => true | r' :: a, r :: b => (subregion_chk r' r && subregions_chk a b)%bool | _, _ => false end.
Lemma cval_eqb_eq : forall a b, cval_eqb a b = true -> a = b.
Proof.
intros [w v|l|l|d o l] [w' v'|l'|l'|d' o' l'] H; cbn in H; try discriminate H.
- apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
- apply Z.eqb_eq in H. subst. reflexivity.
- apply Z.eqb_eq in H. subst. reflexivity.
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Lemma chunk_eqb_eq : forall a b, chunk_eqb a b = true -> a = b.
Proof. intros [o v] [o' v'] H. unfold chunk_eqb in H. cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply cval_eqb_eq in H2. subst. reflexivity. Qed.
Lemma subregion_chk_sound : forall r' r, subregion_chk r' r = true -> subregion r' r /\ r_lo r' <= r_hi r' /\ ext_in r' r.
Proof.
intros r' r H. unfold subregion_chk in H.
apply andb_prop in H as [H HC]. apply andb_prop in H as [H HW]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
assert (HB : r_base r' = r_base r) by (destruct (r_base r') as [x|], (r_base r) as [y|]; cbn in H1; try discriminate H1; [apply Nat.eqb_eq in H1; subst|]; reflexivity).
apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
assert (HWW : r_whi r' <= r_wlo r' \/ (r_wlo r <= r_wlo r' /\ r_whi r' <= r_whi r)).
{ apply orb_prop in HW as [HW|HW]; [left; apply Z.leb_le in HW; exact HW | right]. apply andb_prop in HW as [X Y]. apply Z.leb_le in X. apply Z.leb_le in Y. lia. }
assert (HCC : forall c, In c (r_chunks r') -> In c (r_chunks r)).
{ intros c Hc. pose proof (proj1 (forallb_forall _ _) HC c Hc) as X. apply existsb_exists in X as (c2 & Hc2 & E2). apply chunk_eqb_eq in E2. subst c2. exact Hc2. }
split; [| split; [exact H4 | unfold ext_in; repeat split; [exact HB | lia | lia]]].
unfold subregion. repeat split; try assumption.
Qed.
Lemma S_VP_eq : run_lp S_LR = S_VP. Proof. vm_compute. reflexivity. Qed.
Lemma S_BR_eq : run_lp S_VPr = S_BR. Proof. vm_compute. reflexivity. Qed.
Lemma S_L2_eq : run_lp (add_cond S_BR cond_BRt) = S_L2. Proof. vm_compute. reflexivity. Qed.
Lemma S_FQ_eq : run_lp (add_cond S_BR cond_BRf) = S_FQ. Proof. vm_compute. reflexivity. Qed.
Lemma S_XM_eq : run_lp S_FQr = S_XM. Proof. vm_compute. reflexivity. Qed.
Lemma S_FQr_eq : drv_after S_FQ rsFQ K_FQ RA_FQ (-208) = S_FQr. Proof. vm_compute. reflexivity. Qed.
Lemma S_VPr_eq : S_VPr = mkSS RA_EMIT (sr_sets (ss_regs S_VP) ([(10%bv, SLit 2)] ++ junk_upd K_VP CLOB')) (ss_mem S_VP) None (ss_facts S_VP).
Proof. vm_compute. reflexivity. Qed.
Lemma S_LR_eq : S_LR = mkSS RA_LLVMF (sr_sets (ss_regs S_L) ([(10%bv, SLit 0)] ++ junk_upd K_LR CLOB')) L_mem None (ss_facts S_L).
Proof. vm_compute. reflexivity. Qed.
Lemma rsFQ_eq : rsFQ = tl L_mem0 /\ ss_mem S_XM = WIN (-208) :: rsFQ /\ ss_mem S_FQr = WIN (-208) :: rsFQ /\ concat XM_pieces = CM_mem
/\ tl (ss_mem S_FQ) = tl L_mem0 /\ tl (ss_mem S_VP) = tl L_mem0 /\ tl (ss_mem S_L2) = tl L_mem /\ ss_mem S_BR = ss_mem S_VP /\ ss_mem S_FQ = ss_mem S_VP
/\ ss_mem S_LR = L_mem /\ ss_mem S_L = L_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma XM_sub_chk : subregions_chk CM_mem (WIN (-208) :: rsFQ) = true /\ length XM_pieces = length (WIN (-208) :: rsFQ). Proof. vm_compute. split; reflexivity. Qed.
Lemma L_mem0_shape : tl L_mem0 = tl (ss_mem S_VP) /\ length L_mem0 = length L_mem /\ mem_atoms_lt 165 (tl L_mem0) = true /\ no_cdata (tl L_mem0) = true /\ regions_wf L_mem0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma calls_pcs : ss_pc S_VP = A_icpt_vprintf /\ ss_pc S_BR = A_BNEZ /\ ss_pc S_L2 = A_LLVMF /\ ss_pc S_FQ = A_wrap_free /\ ss_pc S_XM = A_CM
/\ ss_pc S_LR = RA_LLVMF /\ ss_pc S_VPr = RA_EMIT /\ ss_pc S_FQr = RA_FQ
/\ ss_resv S_VP = None /\ ss_resv S_L2 = None /\ ss_resv S_FQ = None /\ ss_resv S_XM = None /\ ss_resv S_BR = None /\ ss_resv S_L = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma calls_checks : ss_atoms_lt K_LR S_L = true /\ mem_atoms_lt K_LR L_mem = true /\ ss_atoms_lt K_VP S_VP = true /\ mem_atoms_lt K_VP (ss_mem S_VP) = true
/\ ss_atoms_lt K_FQ S_FQ = true /\ regions_wf (WIN (-208) :: rsFQ) = true /\ no_cdata rsFQ = true /\ mem_atoms_lt K_FQ (WIN (-208) :: rsFQ) = true
/\ forallb (drv_keep_ok (-208)) rsFQ = true /\ forallb drv_win_ok (ss_mem S_VP) = true /\ forallb so_win_ok (ss_mem S_VP) = true
/\ forallb drv_win_ok (WIN (-208) :: rsFQ) = true /\ forallb so_win_ok (WIN (-208) :: rsFQ) = true
/\ regions_wf (ss_mem S_VP) = true /\ mem_atoms_lt 165 L_mem = true /\ regions_wf rsFQ = true /\ no_cdata (tl L_mem) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma reabs_chk_L2 : reabs_check LT165 S_L2 L_regs L_facts = true. Proof. vm_compute. reflexivity. Qed.
Lemma reabs_chk_XM : reabs_check LT180 S_XM CM_regs CM_facts = true. Proof. vm_compute. reflexivity. Qed.
Lemma L2_fact_obls_eq : fact_obls LT165 L_facts = [(166%nat, fact_r)]. Proof. vm_compute. reflexivity. Qed.
Lemma S_L_regs : sr_get (ss_regs S_L) 1%bv = SLit RA_LLVMF /\ sr_get (ss_regs S_L) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs S_L) 3%bv = SLit TRB_GP
/\ sr_get (ss_regs S_L) 4%bv = SLit TRB_TP /\ sr_get (ss_regs S_L) 8%bv = SOff 162 0 /\ sr_get (ss_regs S_L) 10%bv = SOff 163 0
/\ sr_get (ss_regs S_L) 11%bv = SOff 162 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_VP_regs : sr_get (ss_regs S_VP) 1%bv = SLit RA_EMIT /\ sr_get (ss_regs S_VP) 2%bv = SOff 0 (-288) /\ sr_get (ss_regs S_VP) 3%bv = SLit TRB_GP
/\ sr_get (ss_regs S_VP) 4%bv = SLit TRB_TP /\ sr_get (ss_regs S_VP) 10%bv = SLit A_FMT_D /\ sr_get (ss_regs S_VP) 11%bv = SOff 0 (-264).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_L2_regs : sr_get (ss_regs S_L2) 8%bv = SOff 162 0 /\ sr_get (ss_regs S_L2) 9%bv = SOff 163 0 /\ sr_get (ss_regs S_L2) 10%bv = SOff 163 0
/\ sr_get (ss_regs S_L2) 11%bv = SOff 162 0 /\ sr_get (ss_regs S_L2) 18%bv = SOff 164 0 /\ sr_get (ss_regs S_L2) 19%bv = SLit 18446744073709551615
/\ sr_get (ss_regs S_L2) 21%bv = SOff 166 (-1).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_FQ_regs : sr_get (ss_regs S_FQ) 1%bv = SLit RA_FQ /\ sr_get (ss_regs S_FQ) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs S_FQ) 3%bv = SLit TRB_GP
/\ sr_get (ss_regs S_FQ) 4%bv = SLit TRB_TP /\ sr_get (ss_regs S_FQ) 8%bv = SOff 162 0 /\ sr_get (ss_regs S_FQ) 10%bv = SOff 164 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_XM_regs : sr_get (ss_regs S_XM) 10%bv = SLit 0. Proof. vm_compute. reflexivity. Qed.
Lemma S_VP_vararg : exists r rest, ss_mem S_VP = r :: rest /\ r_base r = Some 0%nat /\ In (YQ0b.mkChunk (-264) (CVal 8 (SLit 0))) (r_chunks r)
/\ r_lo r = -65536 /\ r_hi r = -208 /\ r_wlo r = -65536 /\ r_whi r = -208 /\ forallb (fun c => (-288 <=? YQ0b.c_off c) && (YQ0b.c_off c + c_len c <=? -208)) (r_chunks r) = true.
Proof. eexists. eexists. split; [reflexivity|]. cbn. repeat split; try reflexivity. tauto. Qed.
Lemma submem_L_L2 : submem L_mem (ss_mem S_L2).
Proof.
lazymatch goal with |- submem ?l ?m => let v := eval vm_compute in l in change l with v; let w := eval vm_compute in m in change m with w end.
apply submem_keep; [| apply submem_refl].
split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; right; lia | intros c Hc; destruct Hc].
Qed.
Lemma submem_FQ : submem rsFQ (ss_mem S_FQ).
Proof.
lazymatch goal with |- submem ?l ?m => let v := eval vm_compute in l in change l with v; let w := eval vm_compute in m in change m with w end.
apply submem_drop. apply submem_refl.
Qed.
Definition so_ext_ok (r : YQ0b.region) : bool :=
match r_base r with
| None => (((r_hi r <=? STDOUT_LO) || (STDOUT_HI <=? r_lo r)) && ((r_hi r <=? SOBUF_LO) || (SOBUF_HI <=? r_lo r)))%bool
| _ => true
end.

Lemma so_ext_ok_L0 : forallb so_ext_ok (tl L_mem0) = true /\ forallb (drv_keep_ok (-208)) (tl L_mem0) = true.
Proof. vm_compute. split; reflexivity. Qed.
Fixpoint bsum (l : list (Z * Z)) : Z := match l with [] => 0 | b :: t => snd b + bsum t end.
Lemma bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma wr_app : forall ch l1 l2 T, t_eq (wr ch l1 (wr ch l2 T)) (wr ch (l1 ++ l2) T).
Proof. intros ch l1 l2 T. unfold wr. rewrite map_app. apply t_emit_app. Qed.

Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma refines_subregions : forall E3 (m : word -> option byte) rs rs', subregions_chk rs' rs = true -> refines E3 m rs (map (fun r => [r]) rs').
Proof.
intros E3 m rs. induction rs as [|r rs IH]; intros [|r' rs'] H; cbn in H; try discriminate H; [constructor|].
apply andb_prop in H as [H1 H2]. apply subregion_chk_sound in H1 as (S1 & S2 & S3). cbn [map].
apply refines_cons; [intros Hr; constructor; [exact (region_ok_sub trbsegs E3 m r r' S1 S2 Hr) | constructor] | constructor; [exact S3 | constructor] | cbn; split; exact I | apply IH; exact H2].
Qed.
Lemma refines_XM_CM : forall E3 (m : word -> option byte), refines E3 m (WIN (-208) :: rsFQ) XM_pieces.
Proof. intros E3 m. unfold XM_pieces. apply refines_subregions. exact (proj1 XM_sub_chk). Qed.
Section g.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Hypothesis ARL : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis LIB : lib_site_tfa B.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Hypothesis FREE : free_site_tfa B.
Hypothesis FREEN : free_null_site_tfa B.
Hypothesis EXITL : exit_leaf_tfa B xst.
Hypothesis XFR : xst_frame_tfa xst.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
#[local] Notation EL := (YQ0a.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
Let HWXi : wx_segs_nowrap trbsegs := Hwx_tfa.
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YQ0a.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma arodata_keep : forall (H H' : word -> bool) m m',
(forall a, in_ro_tfa a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview trbsegs H' m' a = aview trbsegs H m a) ->
arodata_ok B (aview trbsegs H m) -> arodata_ok B (aview trbsegs H' m').
Proof. intros H H' m m' HE HRO a H1 H2 H3. rewrite (HE a H1 H2 H3). exact (HRO a H1 H2 H3). Qed.
Lemma in_ro_range : forall a, in_ro_tfa a -> 0x10000 <= a < 0xa2000 \/ 0xa2cf0 <= a < 0xa3f70.
Proof.
intros a [(sg & Hs & Hws & Hrg) | H]; [left | right; exact H].
cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
Qed.
Lemma arodata_frame : forall H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
arodata_ok B (aview trbsegs H m) -> arodata_ok B (aview trbsegs H m').
Proof.
intros H E rs m m' HF Hok U0 HRO. apply (arodata_keep H H m m'); [| exact HRO].
intros a Hro _ _. pose proof (in_ro_range a Hro) as Ha.
unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros Hw. rewrite u64_lit in Hw by lia. apply (in_wrange_drv E rs a Hok) in Hw.
destruct Hw as [Hw|Hw]; [unfold sp_window_lo in U0; lia | apply DRVW_lo in Hw; lia].
Qed.
Lemma journal_regions_kept : forall E rs ly S (W : world trbsegs) mem md ly' S' W' mem' md' k sp0,
ajournal trbsegs B LLVMF_STK sp0 [] ly S W mem md [] ly' S' W' mem' md' k ->
AR trbsegs B ly S W mem md ->
regions_wf rs = true ->
Forall (region_ok trbsegs E (mrestrict (w_H W) mem)) rs ->
forallb (drv_keep_ok (-208)) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> sp0 = usp - 208 -> YN05.ceil_of_top (usp - stack_max_size) ->
Forall (region_ok trbsegs E (mrestrict (w_H W') mem')) rs.
Proof.
intros E rs ly S W mem md ly' S' W' mem' md' k sp0 HJ HAR Hwf Hok Hchk E0 E6 Hsp0 HCT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. unfold sp_window_lo in Ulo.
pose proof (YN05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
pose proof (ts_errno B HB) as Eerr.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as HR. pose proof HR as (B1 & B2 & RW & _).
pose proof (chunk_inside_In r) as CI. specialize (CI) with (1 := regions_wf_In rs r Hwf Hr).
pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.
assert (HIGH : forall a, usp - 208 <= a < 2 ^ 64 ->
mbyte trbsegs (mrestrict (w_H W') mem') a = mbyte trbsegs (mrestrict (w_H W) mem) a
/\ (writable_at trbsegs (mrestrict (w_H W) mem) a -> writable_at trbsegs (mrestrict (w_H W') mem') a)).
{ intros a Ha.
assert (EQA : aview trbsegs (w_H W') mem' a = aview trbsegs (w_H W) mem a).
{ apply F1; [lia | unfold LLVMF_STK; lia]. }
assert (EQ : mbyte trbsegs (mrestrict (w_H W') mem') a = mbyte trbsegs (mrestrict (w_H W) mem) a) by (apply (mbyte_of_aview trbsegs); exact EQA).
split; [exact EQ|]. intros Hw. apply (apresent_writable trbsegs).
apply (apresent_transfer trbsegs (w_H W) (w_H W') mem mem' a);
[lia | apply not_in_img_high; lia | exact EQA | apply apresent_of_writable; [lia | exact Hw]]. }
apply (region_ok_kept_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') r HR).
- intros c i Hcin Hi. pose proof (CI c Hcin) as [L1 L2].
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+   apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *. apply (proj1 (HIGH (usp + YQ0b.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply (proj1 (HIGH (bv_unsigned (ew E 6) + YQ0b.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc Hav]. apply andb_prop in Hc as [Hilo Hihi].
apply Z.leb_le in Hilo. apply Z.leb_le in Hihi.
apply andb_prop in Hav as [Herr Hav]. unfold ext_avoids in Herr. cbn [fst snd] in Herr.
pose proof (proj1 (forallb_forall _ _) Hav c Hcin) as Havc. unfold chunk_avoids in Havc.
apply orb_prop in Havc as [Hsh|Havc].
{
destruct (shared_const_chunk_sound c Hsh) as [Hoff Hlen]. rewrite !Z.add_0_l, Hoff.
apply (canary_got_kept B HB _ _ _ _ _ _ _ _ _ _ i HAR HAR'). lia. }
pose proof (ext_avoids_sound _ _ _ (YQ0b.c_off c + i) Havc ltac:(lia)) as Hno.
assert (Hne : ~ (TRB_ERRNO <= YQ0b.c_off c + i < TRB_ERRNO + 4)) by (apply orb_prop in Herr as [Herr|Herr]; apply Z.leb_le in Herr; lia).
pose proof (in_img_hull (YQ0b.c_off c + i) ltac:(lia)) as Himg.
rewrite !Z.add_0_l. apply (mbyte_of_aview trbsegs). apply F3; [exact Himg | rewrite (ts_owned B HB); exact Hno | rewrite Eerr; exact Hne].
- intros o Ho.
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+ apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *.
apply orb_prop in Hcw as [Hcw|Hcw]; [apply Z.leb_le in Hcw; lia|]. apply andb_prop in Hcw as [Hw1 Hw2].
apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. apply (proj2 (HIGH (usp + o) ltac:(lia))). apply RW. exact Ho.
+ apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc2. lia.
+ apply andb_prop in Hc as [Hc Hw]. apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
unfold writable_at. rewrite Z.add_0_l. apply trb_rw_window. rewrite u64_lit by lia. lia.
Qed.
Lemma lib_reseat : forall E (W W' : world trbsegs) regs mem regs' mem' ly S md ly' S' md' k,
st_ok trbsegs E S_L (mkst regs (w64 A_LLVMF) (mrestrict (w_H W) mem) (seg_rom trbsegs)) ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) ->
ajournal trbsegs B LLVMF_STK (usp - 208) [] ly S W mem md [] ly' S' W' mem' md' k ->
AR trbsegs B ly S W mem md ->
aregs_preserved regs regs' -> getr regs' 10%bv = w64 0 -> YN05.ceil_of_top (usp - stack_max_size) ->
st_ok trbsegs (havoc E K_LR (map (getr regs') CLOB')) S_LR (mkst regs' (Z_to_bv 64 RA_LLVMF) (mrestrict (w_H W') mem') (seg_rom trbsegs)).
Proof.
intros E W W' regs mem regs' mem' ly S md ly' S' md' k HS E0 E6 HJ HAR HP Ha0 HCT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (YN05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof calls_checks as (CKa & CKm & _).
rewrite S_LR_eq.
apply (st_ok_splice_havoc trbsegs K_LR E S_L regs regs' (w64 A_LLVMF) RA_LLVMF (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')
L_mem [(10%bv : bv 5, SLit 0)] CLOB' HS).
- exact CKa.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact CKm.
- exact (regs_kept_CLOB' regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. reflexivity.
-
pose proof (st_ok_mem_ok trbsegs E S_L _ HS) as HM. cbn [ms_mem] in HM.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))))))) in HM.
destruct HM as (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [| exact Hpd].
pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & _).
change L_mem with (WIN208 :: tl L_mem). constructor.
+ apply (region_ok_transport_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')); [exact Hr0 | intros c i Hc; destruct Hc |].
cbn [r_wlo r_whi r_base base_val WIN208]. rewrite E0. intros o Ho. apply (apresent_writable trbsegs).
destruct (Z.lt_ge_cases (usp + o) (usp - 208 - LLVMF_STK)) as [Hlow | Hhi].
* pose proof Hr0 as (_ & _ & RW & _). cbn [r_wlo r_whi r_base base_val WIN208] in RW. rewrite E0 in RW.
assert (EQA : aview trbsegs (w_H W') mem' (usp + o) = aview trbsegs (w_H W) mem (usp + o)).
{ apply F1; [unfold sp_window_lo in Ulo; lia | lia]. }
apply (apresent_transfer trbsegs (w_H W) (w_H W') mem mem' (usp + o));
[unfold sp_window_lo in Ulo; lia | apply not_in_img_high; unfold sp_window_lo in Ulo; lia | exact EQA |].
apply apresent_of_writable; [unfold sp_window_lo in Ulo; lia | apply RW; lia].
* apply Hpres. lia.
+ exact (journal_regions_kept E (tl L_mem) ly S W mem md ly' S' W' mem' md' k (usp - 208) HJ HAR (proj2 (andb_prop _ _ Hwf)) Hrs0
ltac:(vm_compute; reflexivity) E0 E6 eq_refl HCT).
Qed.
Lemma vp_run : forall E (W : world trbsegs) regs mem md,
st_ok trbsegs E S_LR (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom trbsegs))) ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom trbsegs)) md) (at_st S_LR S_VP E W mem md).
Proof.
intros E W regs mem md HS. pose proof HWXi as HWX. rewrite <- S_VP_eq. srr_run_with trbtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma br_run : forall E (W : world trbsegs) regs mem md,
st_ok trbsegs E S_VPr (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom trbsegs))) ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom trbsegs)) md) (at_st S_VPr S_BR E W mem md).
Proof.
intros E W regs mem md HS. pose proof HWXi as HWX. rewrite <- S_BR_eq. srr_run_with trbtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma l2_run : forall E (W : world trbsegs) ms md,
st_ok trbsegs E (add_cond S_BR cond_BRt) (restrict (w_H W) ms) ->
SRr trbsegs W (mkCfg ms md) (at_st S_BR S_L2 E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. rewrite <- S_L2_eq. srr_run_with trbtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma fq_run : forall E (W : world trbsegs) ms md,
st_ok trbsegs E (add_cond S_BR cond_BRf) (restrict (w_H W) ms) ->
SRr trbsegs W (mkCfg ms md) (at_st S_BR S_FQ E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. rewrite <- S_FQ_eq. srr_run_with trbtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma xm_run : forall E (W : world trbsegs) regs mem md,
st_ok trbsegs E S_FQr (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_FQ) mem (seg_rom trbsegs))) ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_FQ) mem (seg_rom trbsegs)) md) (at_st S_FQr S_XM E W mem md).
Proof.
intros E W regs mem md HS. pose proof HWXi as HWX. rewrite <- S_XM_eq. srr_run_with trbtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma rdword_vararg : forall E (H : word -> bool) m,
mem_ok trbsegs E (mrestrict H m) (ss_mem S_VP) -> bv_unsigned (ew E 0) = usp ->
rdword (aview trbsegs H m) (usp - 288 + 24) = Some 0.
Proof.
intros E H m HM E0. destruct S_VP_vararg as (r & rest & Hm & Hb & Hin & _).
rewrite Hm in HM. destruct HM as (_ & Hok & _). pose proof (Forall_inv Hok) as (_ & _ & _ & HC).
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. rewrite Hb in Hc. cbn [base_val] in Hc. rewrite E0 in Hc.
set (a := usp - 288 + 24).
assert (BY : forall d, 0 <= d < 8 -> aview trbsegs H m (a + d) = Some 0).
{ intros d Hd. destruct (Hc d ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte YQ0b.c_val YQ0b.c_off YQ0b.c_len] in Hb1, Hb2.
replace (usp + -264 + d) with (a + d) in Hb2 by lia. unfold aview. rewrite Hb2. cbn [option_map]. injection Hb1 as <-.
assert (D : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7) by lia.
destruct D as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity. }
assert (BY0 : aview trbsegs H m a = Some 0) by (rewrite <- (Z.add_0_r a); apply BY; lia).
unfold rdword. rewrite BY0, !BY by lia. reflexivity.
Qed.
Lemma vp_reseat : forall E (W : world trbsegs) regs mem regs' mem',
st_ok trbsegs E S_VP (mkst regs (w64 A_icpt_vprintf) (mrestrict (w_H W) mem) (seg_rom trbsegs)) ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) ->
aregs_preserved regs regs' -> getr regs' 10%bv = w64 2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (usp - 288 - PF_STK <= a < usp - 288) -> ~ STDOUT_MUT a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
st_ok trbsegs (havoc E K_VP (map (getr regs') CLOB')) S_VPr (mkst regs' (Z_to_bv 64 RA_EMIT) (mrestrict (w_H W) mem') (seg_rom trbsegs)).
Proof.
intros E W regs mem regs' mem' HS E0 E6 HP Ha0 Hfr Hpres.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. unfold sp_window_lo in Ulo.
pose proof calls_checks as (_ & _ & CKa & CKm & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFV & _ & WFQ & NCD).
rewrite (proj1 rsFQ_eq) in WFQ. pose proof L_mem0_shape as (_ & _ & _ & NCD0 & _).
pose proof so_ext_ok_L0 as [SOX KEEP].
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (usp - 288 - PF_STK <= a < usp - 288) -> ~ STDOUT_MUT a ->
mbyte trbsegs (mrestrict (w_H W) mem') a = mbyte trbsegs (mrestrict (w_H W) mem) a).
{ intros a Hr H1 H2. apply (mbyte_of_aview trbsegs). apply Hfr; assumption. }
rewrite S_VPr_eq.
apply (st_ok_splice_havoc trbsegs K_VP E S_VP regs regs' (w64 A_icpt_vprintf) RA_EMIT (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')
(ss_mem S_VP) [(10%bv : bv 5, SLit 2)] CLOB' HS).
- exact CKa.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact CKm.
- exact (regs_kept_CLOB' regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. reflexivity.
- pose proof (st_ok_mem_ok trbsegs E S_VP _ HS) as HM. cbn [ms_mem] in HM. destruct HM as (Hwf & Hok & Hpd).
split; [exact Hwf|]. split; [| exact Hpd].
destruct S_VP_vararg as (r0 & rest & Hm & Hb & _ & Hlo & Hhi & Hwlo & Hwhi & Hoffs).
assert (Hrest : rest = tl L_mem0) by (rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))), Hm; reflexivity).
rewrite Hm in Hok, Hpd |- *. pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0. constructor.
+
apply (region_ok_transport_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')); [exact Hr0 | |].
* intros c i Hc Hi. rewrite Hb. cbn [base_val]. rewrite E0.
pose proof (proj1 (forallb_forall _ _) Hoffs c Hc) as Ho. apply andb_prop in Ho as [Ho Ho2]. apply Z.leb_le in Ho. apply Z.leb_le in Ho2.
apply SCR.
-- unfold sp_window_hi in Uhi. lia.
-- lia.
-- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI. lia.
* rewrite Hb, Hwlo, Hwhi. cbn [base_val]. rewrite E0. intros o Ho. apply (apresent_writable trbsegs). apply Hpres; [unfold sp_window_hi in Uhi; lia | unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; lia|].
pose proof Hr0 as (_ & _ & RW & _). rewrite Hb, Hwlo, Hwhi in RW. cbn [base_val] in RW. rewrite E0 in RW.
apply apresent_of_writable; [lia | apply RW; lia].
+ rewrite Hrest in Hrs0, Hpd |- *. clear Hoffs.
assert (HMt : mem_ok trbsegs E (mrestrict (w_H W) mem) (tl L_mem0)).
{ split; [exact WFQ | split; [exact Hrs0 | exact (proj2 Hpd)]]. }
assert (HK : Forall (region_kept trbsegs E (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')) (tl L_mem0)).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) KEEP r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (forallb_forall _ _) SOX r Hr) as Hx. unfold so_ext_ok in Hx.
pose proof (proj1 (Forall_forall _ _) Hrs0 r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
~ (usp - 288 - PF_STK <= a < usp - 288) /\ ~ STDOUT_MUT a).
{ intros a Ha. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI, PF_STK.
destruct (r_base r) as [[|[|[|[|[|[|[|kk]]]]]]]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E0 in Ha. lia.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. pose proof (u64_range (ew E 6)). lia.
- apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply andb_true_iff in Hx. destruct Hx as [Hx1 Hx2].
apply orb_true_iff in Hx1.
apply orb_true_iff in Hx2.
rewrite !Z.leb_le in Hx1.
rewrite !Z.leb_le in Hx2.
clear - Ha Hc1 Hc2 Hx1 Hx2 Ulo. unfold STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in *. lia. }
split; intros a Ha; [apply SCR; [clear - Ha B1 B2; lia | apply OFF; exact Ha | apply OFF; exact Ha]|].
intros Hw. unfold writable_at, wview in Hw |- *.
assert (Hext : base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r).
{ pose proof (regions_wf_In _ r WFQ Hr) as Hrwf. unfold region_wf in Hrwf.
apply andb_prop in Hrwf as [Hrwf _]. apply andb_prop in Hrwf as [Hlh Hwin].
apply Bool.orb_prop in Hwin as [Hwin|Hwin]; [apply Z.leb_le in Hwin; lia|]. apply andb_prop in Hwin as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2. lia. }
destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|] eqn:Em.
-- assert (Hp : apresent (w_H W) mem a).
{ unfold apresent. unfold mrestrict in Em. destruct (w_H W (Z_to_bv 64 a)); [discriminate|]. split; [reflexivity | exists b; exact Em]. }
destruct (Hpres a ltac:(lia) (proj2 (OFF a Hext)) Hp) as [Hh [b' Hb']]. unfold mrestrict. rewrite Hh, Hb'. discriminate.
-- destruct (mrestrict (w_H W) mem' (Z_to_bv 64 a)); [discriminate | exact Hw]. }
exact (proj1 (proj2 (mem_ok_kept trbsegs E _ (mrestrict (w_H W) mem') (tl L_mem0) HMt NCD HK))).
Qed.
Lemma l2_to_L : forall E (W : world trbsegs) ms (r : Z),
st_ok trbsegs E S_L2 (restrict (w_H W) ms) -> bv_unsigned (ew E 166) = r -> 2 <= r <= 4 ->
let E' := E_L2 E (ms_regs ms) in
st_ok trbsegs E' S_L (restrict (w_H W) ms) /\ bv_unsigned (ew E' 166) = r - 1 /\ (forall j, (j < 165)%nat -> ew E' j = ew E j).
Proof.
intros E W ms r HS V65 Hr E'. set (regs := ms_regs ms) in *.
pose proof S_L2_regs as (P8 & P9 & P10 & P11 & P18 & P19 & P20).
assert (R : forall rg v, sr_get (ss_regs S_L2) rg = v -> getr regs rg = sv_denot E v).
{ intros rg v Hv. subst regs. rewrite (st_ok_restrict_reg trbsegs (w_H W) E S_L2 ms rg HS), Hv. reflexivity. }
assert (R20 : getr regs 21%bv = w64 (r - 1)).
{ rewrite (R 21%bv _ P20). cbn [sv_denot]. rewrite <- V65. unfold w64. f_equal. all: try lia. }
assert (NEW : forall i rg, (i < 15)%nat -> nth i L2_srcs 0%bv = rg -> ew E' (165 + i) = getr regs rg).
{ intros i rg Hi <-. subst E'. unfold E_L2. rewrite (ew_havoc_new E 165 _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < 165)%nat -> ew E' j = ew E j) by (intros j Hj; subst E'; unfold E_L2; apply ew_havoc_old; exact Hj).
assert (V65' : bv_unsigned (ew E' 166) = r - 1).
{ change 166%nat with (165 + 1)%nat. rewrite (NEW 1%nat 21%bv) by (cbn; first [lia | reflexivity]). rewrite R20. apply u64_lit. lia. }
split; [| split; [exact V65' | exact Eold]].
pose proof (st_ok_mem_ok trbsegs E S_L2 _ HS) as HM0. cbn [restrict ms_mem] in HM0.
assert (HM1 : mem_ok trbsegs E (mrestrict (w_H W) (ms_mem ms)) L_mem).
{ apply (mem_ok_sub trbsegs E _ (ss_mem S_L2)); [exact submem_L_L2 | exact (proj1 L_mem_wf) | exact HM0]. }
assert (HM2 : mem_ok trbsegs E' (mrestrict (w_H W) (ms_mem ms)) L_mem).
{ apply (mem_ok_agree trbsegs 165 E); [| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 calls_checks))))))))))))))) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_L. rewrite <- (proj1 (proj2 (proj2 calls_pcs))).
apply (st_ok_reabs trbsegs LT165 E E' S_L2 (restrict (w_H W) ms) L_regs L_mem L_facts HS).
- split; [| intros d _; subst E'; reflexivity]. intros j Hj. unfold LT165 in Hj. apply Nat.ltb_lt in Hj. exact (Eold j Hj).
- exact reabs_chk_L2.
- cbn [ms_regs restrict]. fold regs.
apply Forall_forall. intros [rg j] Hin. vm_compute in Hin. cbn [fst snd].
Ltac oneB NEW i := rewrite <- (NEW i); [apply f_equal; reflexivity | cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ oneB NEW 0%nat | oneB NEW 1%nat | oneB NEW 2%nat | oneB NEW 3%nat | oneB NEW 4%nat | oneB NEW 5%nat | oneB NEW 6%nat | oneB NEW 7%nat
| oneB NEW 8%nat | oneB NEW 9%nat | oneB NEW 10%nat | oneB NEW 11%nat | oneB NEW 12%nat | oneB NEW 13%nat | oneB NEW 14%nat ] |]).
destruct Hin.
- rewrite L2_fact_obls_eq. constructor; [| constructor].
unfold afact_ok; cbn [af_lo af_hi af_al2 fst snd fact_r]. rewrite V65'. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. repeat split; try reflexivity; lia.
- exact HM2.
Qed.
Lemma xm_to_CM : forall E (W : world trbsegs) ms,
st_ok trbsegs E S_XM (restrict (w_H W) ms) ->
let E' := E_CM E (ms_regs ms) in
st_ok trbsegs E' S_CM (restrict (w_H W) ms) /\ bv_unsigned (ew E' 180) = 0 /\ (forall j, (j < K_CM)%nat -> ew E' j = ew E j).
Proof.
intros E W ms HS E'. set (regs := ms_regs ms) in *.
assert (R10 : getr regs 10%bv = w64 0).
{ subst regs. rewrite (st_ok_restrict_reg trbsegs (w_H W) E S_XM ms 10%bv HS), S_XM_regs. reflexivity. }
assert (NEW : forall i rg, (i < 16)%nat -> nth i CM_srcs 0%bv = rg -> ew E' (K_CM + i) = getr regs rg).
{ intros i rg Hi <-. subst E'. unfold E_CM. rewrite (ew_havoc_new E K_CM _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < K_CM)%nat -> ew E' j = ew E j) by (intros j Hj; subst E'; unfold E_CM; apply ew_havoc_old; exact Hj).
assert (V79 : bv_unsigned (ew E' 180) = 0).
{ change 180%nat with (K_CM + 0)%nat. rewrite (NEW 0%nat 10%bv) by (cbn; first [lia | reflexivity]). rewrite R10. apply u64_lit. lia. }
split; [| split; [exact V79 | exact Eold]].
pose proof (st_ok_mem_ok trbsegs E S_XM _ HS) as HM0. cbn [restrict ms_mem] in HM0. rewrite (proj1 (proj2 rsFQ_eq)) in HM0.
assert (HM1 : mem_ok trbsegs E (mrestrict (w_H W) (ms_mem ms)) CM_mem).
{ rewrite <- (proj1 (proj2 (proj2 (proj2 rsFQ_eq)))). apply (mem_ok_refine E _ (WIN (-208) :: rsFQ)); [exact HM0 | apply refines_XM_CM |].
rewrite (proj1 (proj2 (proj2 (proj2 rsFQ_eq)))). exact (proj1 CM_mem_wf). }
assert (HM2 : mem_ok trbsegs E' (mrestrict (w_H W) (ms_mem ms)) CM_mem).
{ apply (mem_ok_agree trbsegs K_CM E); [| exact (proj1 (proj2 CM_mem_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_CM. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 calls_pcs))))).
apply (st_ok_reabs trbsegs LT180 E E' S_XM (restrict (w_H W) ms) CM_regs CM_mem CM_facts HS).
- split; [| intros d _; subst E'; reflexivity]. intros j Hj. unfold LT180 in Hj. apply Nat.ltb_lt in Hj. exact (Eold j Hj).
- exact reabs_chk_XM.
- cbn [ms_regs restrict]. fold regs.
apply Forall_forall. intros [rg j] Hin. vm_compute in Hin. cbn [fst snd].
Ltac oneD NEW i := rewrite <- (NEW i); [apply f_equal; reflexivity | cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ oneD NEW 0%nat | oneD NEW 2%nat | oneD NEW 3%nat | oneD NEW 4%nat | oneD NEW 5%nat | oneD NEW 6%nat | oneD NEW 7%nat
| oneD NEW 8%nat | oneD NEW 9%nat | oneD NEW 10%nat | oneD NEW 11%nat | oneD NEW 12%nat | oneD NEW 13%nat | oneD NEW 14%nat
| oneD NEW 15%nat ] |]).
destruct Hin.
- rewrite CM_fact_obls_eq. constructor; [| constructor].
unfold afact_ok; cbn [af_lo af_hi af_al2 fst snd fact_v]. rewrite V79. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. repeat split; try reflexivity; lia.
- exact HM2.
Qed.
Lemma blocks_bytes_ablocks : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S. rewrite blocks_bytes_blocks. unfold ablocks. induction (blocks S) as [|b l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma STDOUT_static : forall a, STDOUT_MUT a ->
in_img trbsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha.
split; [apply in_img_hull; lia|]. split.
- rewrite (ts_owned B HB). intros X. apply Exists_exists in X as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Trb_owned_static in Hin. cbn in Hin. repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|]). exact Hin.
- rewrite (ts_errno B HB). unfold TRB_ERRNO. lia.
Qed.
Lemma in_ro_static : forall a, in_ro_tfa a -> ~ (usp - 65536 <= a < usp + 65536) /\ ~ STDOUT_MUT a.
Proof.
intros a Ha. pose proof (in_ro_range a Ha). pose proof Hsp as (Ulo & _). unfold sp_window_lo in Ulo.
unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI. lia.
Qed.
End g.
End e.
