(* copied from cgif_file lib/A/AD1r.v by rules r1,r2,r3,r6,r9,rC, generator ed5c0821ce98f1d99fcd7466c0aa65f7671a8daf838ab8f2b2da9f5038f22ee4 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1r.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (5 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: the cf driver loop of plugin-hostd/fuzz_reply (target_run's calls loop over the
   second allocator instance ARcf, Reusable/YG0ncf.v), against the donor A/AD1r.v:
   - the call site is AD1mcf.lib_site_cf (fuzz_reply's cf program interface fr_lib_contract_drv, A/AD1w_cf.v), whose
     journal has the program globals G_fr_c as its PST and the footprint sink_token :: fr_FP;
   - the loop runs on RelocA-2's clipped views (A/AD2f_fp.v S_LF / L_memF, S_CMF / CM_memF), which leave out the
     G_fr_c bytes the call may write; the image regions are carried across the call by A/AD1r_fp.v
     journal_regions_kept_x;
   - the donor's `Permutation (ablocks B ly S) [(buf, cap)]` / `[(buf, cap); (q, len)]` (false for fuzz_reply after
     its first call: the entry keeps g_src's table and g_out's buffer alive and may move the buffer) is
     ATopKeeper's fr_heap (A/AD1r_heap_cf.v), stepped by H_step over the post's fr_surv / fr_live_post and kept by
     H_frame between calls;
   - the donor's event arithmetic (`st_nev S + EV_LIB * r + 3 <= EV_MAX` and every `st_nev` bound) is gone: the
     interface's room LIBROOM is discharged inside AD1mcf, the call's allocator room NP (A/AD1w_cf.v) is threaded
     from call to call (the post gives it back), and after the last call the tail law's ROOM_cf_k S 2 pays the two
     frees (q here, the buffer in the main tail; A/AD1npcf.v);
   - the per-call invariant fr_LI (A/AD1w_cf.v) is threaded from call to call (the post gives call ci0 + 1) and kept
     between calls by A/AD1w_cf_inv.v fr_lib_inv_stable_ok, since the driver's code between calls writes only its
     stack, the stdout FILE and its buffer (no G_fr_c byte, no live block); rom_view is derived at each call from
     arodata_ok (A/AD1r_fp.v rom_view_of_arodata);
   - the main tail is a hypothesis of this file (main_tail_cf, over S_CMF, ROOM_cf, the hull admission and the
     buffer's membership), discharged by the top from A/AD29cf.v;
   - KF-COUNT #7: the run count NS (A/AD1mcf.v) leaves room for the calls still to come, NS S + (4 - j) * XNMAX <=
     NRUN at call j (at most 4 calls, AD2f.v calls_bound), carried by calls_loop beside fr_heap: it gives the call's
     NS S + XNMAX <= NRUN (j < 4, XNMAX >= 0), the post's step NS S' <= NS S + XNMAX moves it to call j + 1, and the code between
     calls does not change S; the loop's entry asks NS S + 4 * XNMAX <= NRUN.  After the last call it gives NS S' <= NRUN,
     so the hull admission (HULL_NS) at the frees after the loop (the main tail's by nsec_free_cf). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD21 AD2h AD2f AD1s AD23 AD24 AD25 AD26 ACeg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_journal W_rep W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn_cf AD2f_fp AD1r_fp AD1r_heap_cf AD1w_cf AD1w_cf_inv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00cf YG01cf YG03cf YG03dcf YG0dcf YG0ncf YG0ucf YGcfNames YGcfTok YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1ucf AD1vcf AD1ycf AE22cf AD1wcf AD1mcf AD1npcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.
Definition RA_EMITC : Z := 0x821f8.
Definition A_BNEZ : Z := 0x82208.
Definition RA_FQ : Z := 0x82214.
Definition K_LR : nat := 180.
Definition S_LR : sstate := Eval vm_compute in mkSS RA_LLVMF (sr_sets L_regs ([(10%bv, SLit 0)] ++ junk_upd K_LR CLOB')) L_memF None L_facts.
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
Definition E_L2 (E : YP0m.env) (regs : bvmap 5 word) : YP0m.env := havoc E 165 (map (getr regs) L2_srcs).
Definition XM_pieces : list smem := map (fun r => [r]) CM_memF.
Definition cval_eqb (a b : cval) : bool :=
match a, b with
| CVal w v, CVal w' v' => (N.eqb w w' && sv_eqb v v')%bool
| CZero l, CZero l' => Z.eqb l l' | CImg l, CImg l' => Z.eqb l l'
| CData d o l, CData d' o' l' => (Nat.eqb d d' && Z.eqb o o' && Z.eqb l l')%bool
| _, _ => false
end.
Definition chunk_eqb (a b : YP09.chunk) : bool := (Z.eqb (YP09.c_off a) (YP09.c_off b) && cval_eqb (YP09.c_val a) (YP09.c_val b))%bool.
Definition obase_eqb (a b : option nat) : bool := match a, b with None, None => true | Some x, Some y => Nat.eqb x y | _, _ => false end.
Definition subregion_chk (r' r : YP09.region) : bool :=
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
Lemma S_LR_eq : S_LR = mkSS RA_LLVMF (sr_sets (ss_regs S_LF) ([(10%bv, SLit 0)] ++ junk_upd K_LR CLOB')) L_memF None (ss_facts S_LF).
Proof. vm_compute. reflexivity. Qed.
Lemma rsFQ_eq : rsFQ = tl L_mem0 /\ ss_mem S_XM = WIN (-208) :: rsFQ /\ ss_mem S_FQr = WIN (-208) :: rsFQ /\ concat XM_pieces = CM_memF
/\ tl (ss_mem S_FQ) = tl L_mem0 /\ tl (ss_mem S_VP) = tl L_mem0 /\ tl (ss_mem S_L2) = tl L_memF /\ ss_mem S_BR = ss_mem S_VP /\ ss_mem S_FQ = ss_mem S_VP
/\ ss_mem S_LR = L_memF /\ ss_mem S_LF = L_memF.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma XM_sub_chk : subregions_chk CM_memF (WIN (-208) :: rsFQ) = true /\ length XM_pieces = length (WIN (-208) :: rsFQ). Proof. vm_compute. split; reflexivity. Qed.
Lemma L_mem0_shape : tl L_mem0 = tl (ss_mem S_VP) /\ length L_mem0 = length L_memF /\ mem_atoms_lt 165 (tl L_mem0) = true /\ no_cdata (tl L_mem0) = true /\ regions_wf L_mem0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma calls_pcs : ss_pc S_VP = A_icpt_vprintf /\ ss_pc S_BR = A_BNEZ /\ ss_pc S_L2 = A_LLVMF /\ ss_pc S_FQ = A_wrap_free /\ ss_pc S_XM = A_CM
/\ ss_pc S_LR = RA_LLVMF /\ ss_pc S_VPr = RA_EMIT /\ ss_pc S_FQr = RA_FQ
/\ ss_resv S_VP = None /\ ss_resv S_L2 = None /\ ss_resv S_FQ = None /\ ss_resv S_XM = None /\ ss_resv S_BR = None /\ ss_resv S_LF = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma calls_checks : ss_atoms_lt K_LR S_LF = true /\ mem_atoms_lt K_LR L_memF = true /\ ss_atoms_lt K_VP S_VP = true /\ mem_atoms_lt K_VP (ss_mem S_VP) = true
/\ ss_atoms_lt K_FQ S_FQ = true /\ regions_wf (WIN (-208) :: rsFQ) = true /\ no_cdata rsFQ = true /\ mem_atoms_lt K_FQ (WIN (-208) :: rsFQ) = true
/\ forallb (drv_keep_ok (-208)) rsFQ = true /\ forallb drv_win_ok (ss_mem S_VP) = true /\ forallb so_win_ok (ss_mem S_VP) = true
/\ forallb drv_win_ok (WIN (-208) :: rsFQ) = true /\ forallb so_win_ok (WIN (-208) :: rsFQ) = true
/\ regions_wf (ss_mem S_VP) = true /\ mem_atoms_lt 165 L_memF = true /\ regions_wf rsFQ = true /\ no_cdata (tl L_memF) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* no absolute region the driver's code between two calls writes through reaches a G_fr_c byte *)
Lemma calls_gf : forallb region_gf_ok L_memF = true /\ forallb region_gf_ok (ss_mem S_VP) = true /\ forallb region_gf_ok (tl L_memF) = true
/\ forallb drv_win_ok L_memF = true /\ regions_wf L_memF = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma reabs_chk_L2 : reabs_check LT165 S_L2 L_regs L_facts = true. Proof. vm_compute. reflexivity. Qed.
Lemma reabs_chk_XM : reabs_check LT180 S_XM CM_regs CM_facts = true. Proof. vm_compute. reflexivity. Qed.
Lemma L2_fact_obls_eq : fact_obls LT165 L_facts = [(166%nat, fact_r)]. Proof. vm_compute. reflexivity. Qed.
Lemma S_L_regs : sr_get (ss_regs S_LF) 1%bv = SLit RA_LLVMF /\ sr_get (ss_regs S_LF) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs S_LF) 3%bv = SLit TFIB_GP
/\ sr_get (ss_regs S_LF) 4%bv = SLit TFIB_TP /\ sr_get (ss_regs S_LF) 8%bv = SOff 162 0 /\ sr_get (ss_regs S_LF) 10%bv = SOff 163 0
/\ sr_get (ss_regs S_LF) 11%bv = SOff 162 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_VP_regs : sr_get (ss_regs S_VP) 1%bv = SLit RA_EMIT /\ sr_get (ss_regs S_VP) 2%bv = SOff 0 (-288) /\ sr_get (ss_regs S_VP) 3%bv = SLit TFIB_GP
/\ sr_get (ss_regs S_VP) 4%bv = SLit TFIB_TP /\ sr_get (ss_regs S_VP) 10%bv = SLit A_FMT_D /\ sr_get (ss_regs S_VP) 11%bv = SOff 0 (-264).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_L2_regs : sr_get (ss_regs S_L2) 8%bv = SOff 162 0 /\ sr_get (ss_regs S_L2) 9%bv = SOff 163 0 /\ sr_get (ss_regs S_L2) 10%bv = SOff 163 0
/\ sr_get (ss_regs S_L2) 11%bv = SOff 162 0 /\ sr_get (ss_regs S_L2) 18%bv = SOff 164 0 /\ sr_get (ss_regs S_L2) 19%bv = SLit 18446744073709551615
/\ sr_get (ss_regs S_L2) 21%bv = SOff 166 (-1).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_FQ_regs : sr_get (ss_regs S_FQ) 1%bv = SLit RA_FQ /\ sr_get (ss_regs S_FQ) 2%bv = SOff 0 (-208) /\ sr_get (ss_regs S_FQ) 3%bv = SLit TFIB_GP
/\ sr_get (ss_regs S_FQ) 4%bv = SLit TFIB_TP /\ sr_get (ss_regs S_FQ) 8%bv = SOff 162 0 /\ sr_get (ss_regs S_FQ) 10%bv = SOff 164 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_XM_regs : sr_get (ss_regs S_XM) 10%bv = SLit 0. Proof. vm_compute. reflexivity. Qed.
Lemma S_VP_vararg : exists r rest, ss_mem S_VP = r :: rest /\ r_base r = Some 0%nat /\ In (YP09.mkChunk (-264) (CVal 8 (SLit 0))) (r_chunks r)
/\ r_lo r = -65536 /\ r_hi r = -208 /\ r_wlo r = -65536 /\ r_whi r = -208 /\ forallb (fun c => (-288 <=? YP09.c_off c) && (YP09.c_off c + c_len c <=? -208)) (r_chunks r) = true.
Proof. eexists. eexists. split; [reflexivity|]. cbn. repeat split; try reflexivity. tauto. Qed.
Lemma submem_L_L2 : submem L_memF (ss_mem S_L2).
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
Definition so_ext_ok (r : YP09.region) : bool :=
match r_base r with
| None => (((r_hi r <=? STDOUT_LO) || (STDOUT_HI <=? r_lo r)) && ((r_hi r <=? SOBUF_LO) || (SOBUF_HI <=? r_lo r)))%bool
| _ => true
end.
Lemma so_ext_ok_L0 : forallb so_ext_ok (tl L_mem0) = true /\ forallb (drv_keep_ok (-208)) (tl L_mem0) = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma wr_app : forall ch l1 l2 T, t_eq (wr ch l1 (wr ch l2 T)) (wr ch (l1 ++ l2) T).
Proof. intros ch l1 l2 T. unfold wr. rewrite map_app. apply t_emit_app. Qed.
Lemma map_single {X Y : Type} : forall (f : X -> Y) (l : list X) (y : Y), map f l = [y] -> exists x, l = [x] /\ f x = y.
Proof. intros f [|x [|x' l]] y H; cbn in H; try discriminate H. injection H as <-. exists x. split; reflexivity. Qed.

(* the three harness words fr_hblks reads are G_fr_c bytes *)
Lemma rg_words_gf : forall i, 0 <= i < 8 ->
  Exists (in_zr (W_rep.rg_src W_rep.fr_globals + i)) GF_RANGES /\ Exists (in_zr (W_rep.rg_out W_rep.fr_globals + i)) GF_RANGES /\
  Exists (in_zr (W_rep.rg_capout W_rep.fr_globals + i)) GF_RANGES.
Proof.
intros i Hi. assert (D : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
repeat split; apply (proj1 (W_journal.inGb_spec _ _));
destruct D as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Lemma refines_subregions : forall E3 (m : word -> option byte) rs rs', subregions_chk rs' rs = true -> refines E3 m rs (map (fun r => [r]) rs').
Proof.
intros E3 m rs. induction rs as [|r rs IH]; intros [|r' rs'] H; cbn in H; try discriminate H; [constructor|].
apply andb_prop in H as [H1 H2]. apply subregion_chk_sound in H1 as (S1 & S2 & S3). cbn [map].
apply refines_cons; [intros Hr; constructor; [exact (region_ok_sub tfibsegs E3 m r r' S1 S2 Hr) | constructor] | constructor; [exact S3 | constructor] | cbn; split; exact I | apply IH; exact H2].
Qed.
Lemma refines_XM_CM : forall E3 (m : word -> option byte), refines E3 m (WIN (-208) :: rsFQ) XM_pieces.
Proof. intros E3 m. unfold XM_pieces. apply refines_subregions. exact (proj1 XM_sub_chk). Qed.

(* a byte whose restricted memory is unchanged keeps its view, its presence and its writability *)
Lemma kept_of_rd : forall (H : word -> bool) (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
  aview tfibsegs H m' a = aview tfibsegs H m a /\ (apresent H m a -> apresent H m' a) /\
  (writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m') a).
Proof.
intros H m m' a E. split; [unfold aview, mbyte; rewrite E; reflexivity|]. split.
- intros [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in E. rewrite Hh in E. rewrite E. exact Hb.
- unfold writable_at, wview. rewrite E. exact (fun X => X).
Qed.
(* presence kept gives writability kept *)
Lemma writable_of_pres : forall (H : word -> bool) (m m' : word -> option byte) a,
  (apresent H m a -> apresent H m' a) ->
  writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m') a.
Proof.
intros H m m' a HP Hw. unfold writable_at, wview in Hw |- *.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em.
- assert (Hp : apresent H m a).
  { unfold apresent. unfold mrestrict in Em. destruct (H (Z_to_bv 64 a)); [discriminate|]. split; [reflexivity | exists b; exact Em]. }
  destruct (HP Hp) as [Hh [b' Hb']]. unfold mrestrict. rewrite Hh, Hb'. discriminate.
- destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* a frame over regions that write only the driver's stack window or image windows off G_fr_c keeps every G_fr_c
   byte and every byte off the image below the allocation ceiling *)
Lemma frame_keep_lo : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> forallb region_gf_ok rs = true ->
  regions_wf rs = true -> alloc_ceiling <= bv_unsigned (ew E 0) - 65536 -> 0 <= a < alloc_ceiling ->
  (Exists (in_zr a) GF_RANGES \/ ~ in_img tfibsegs a) ->
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros E rs H m m' a HF Hok Hgf Hwf Hlo Ha Hga. pose proof YM05.alloc_ceiling_lt as CL.
apply HF. rewrite u64_lit by lia. intros (r & Hin & Hw).
pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr. pose proof (proj1 (forallb_forall _ _) Hgf r Hin) as Hg.
pose proof (regions_wf_In rs r Hwf Hin) as Hrwf. unfold region_wf in Hrwf. apply andb_prop in Hrwf as [Hrwf _].
apply andb_prop in Hrwf as [Hlh Hwin]. apply Z.leb_le in Hlh.
unfold drv_win_ok in Hr. apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
unfold region_gf_ok in Hg.
destruct (r_base r) as [[|n]|] eqn:Hb; try discriminate Hr; cbn [base_val] in Hw.
- apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- apply Bool.orb_prop in Hwin as [Hwin|Hwin]; [apply Z.leb_le in Hwin; lia|].
  apply andb_prop in Hwin as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2.
  destruct Hga as [Hga | Hni].
  + apply orb_prop in Hg as [Hg|Hg]; [apply Z.leb_le in Hg; lia|].
    exact (gf_avoid_sound _ _ a Hg ltac:(lia) Hga).
  + apply existsb_exists in Hr as (iv & Hiv & Hbb). apply andb_prop in Hbb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    assert (HD : DRVW a = true).
    { unfold DRVW. apply existsb_exists. exists iv. split; [exact Hiv|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    apply Hni. apply in_img_rw. pose proof (DRVW_lo a HD). lia.
Qed.

Section g.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.
Hypothesis ML : model_laws_cf (as_universe B).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
(* the call's allocator room between driver allocator calls (A/AD1w_cf.v), with its tail law *)
Variable NP : astate -> Prop.
Hypothesis NPT : iface_room_np_tail NP.
(* the run count, its run bound and its per-call step bound (A/AD1mcf.v), with the step bound's sign (A/AD1pcf.v
   has it from XN_BND at n = 0) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
Hypothesis XNMAX_NN : 0 <= XNMAX.
(* field round 3: the hull admission at the frees after the last call (drv_pre's cf_hull_ok conjunct) and at the main
   tail's free (main_tail_cf's), from the run count's bound (A/AD1pcf.v HULL_NS) and the count's step at the driver's
   free, at the text of A/CfRBridgeRules.v nsec_free_cf with NS for nsec_cf *)
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
Hypothesis nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s).
(* field round 3 (Part A): the image fact behind the RELRO bytes' keep (A/AD1vcf.v relro_ok) *)
Hypothesis RO : relro_ok.
(* route R (RULE-SHAPES.md sec 0): the world relation of the steps whose callee can re-hide shadow, the call of
   LLVMFuzzerTestOneInput (LIB, its journal at R) and the frees after the last call (FREE / FREEN). The loop moves no
   fact across those steps by a wle lemma (it reads the call's journal and post frames), so it needs no law of R. *)
Variable R : world tfibsegs -> world tfibsegs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle tfibsegs W W' -> R W W'.
Hypothesis LIB : lib_site_cf B NP NS NRUN XNMAX R.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Hypothesis FREE : free_site_tfa B R.
Hypothesis FREEN : free_null_site_tfa B R.
Hypothesis XFR : xst_frame_tfa xst.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Let LAWSX : AR_laws_x tfibsegs B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md) cf_head := AR_laws_x_cf tfibsegs B ARL.
(* A/AD29cf.v's so_state, over this file's names *)
Definition so_state (k : nat) (H : word -> bool) (m : word -> option byte) : Prop :=
(k = 0%nat /\ stdout_img H m) \/ ((1 <= k)%nat /\ xst k H m).
Lemma so_state_keep : forall k H H' m m',
(forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> so_state k H m -> so_state k H' m'.
Proof.
intros k H H' m m' HA [[Hk HI]|[Hk HX]]; [left | right]; split; try assumption.
- intros a Ha. rewrite (HA a) by (left; exact Ha). apply HI. exact Ha.
- exact (XFR k H H' m m' HX HA).
Qed.
Lemma so_state_frame : forall k H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb so_win_ok rs = true ->
sp_window_lo <= bv_unsigned (ew E 0) -> bv_unsigned (ew E 0) <= bv_unsigned (ew E 6) ->
so_state k H m -> so_state k H m'.
Proof.
intros k H E rs m m' HF Hok U0 U6 HS. apply (so_state_keep k H H m m'); [| exact HS].
intros a Ha. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Hw). pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X. unfold so_win_ok in X. rewrite u64_lit in Hw by exact Ha'.
apply orb_prop in X as [X|X]; [apply Z.leb_le in X; lia|].
unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI, sp_window_lo in *.
destruct (r_base r) as [[|n]|]; try discriminate X; cbn [base_val] in Hw.
- apply Z.leb_le in X. lia.
- apply andb_prop in X as [X1 X2].
apply orb_prop in X1 as [X1|X1]; apply Z.leb_le in X1; apply orb_prop in X2 as [X2|X2]; apply Z.leb_le in X2; lia.
Qed.
Lemma so_not_owned : forall ly S Hp W mem md a, ARcf tfibsegs B ly S Hp W mem md -> STDOUT_MUT a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Ha X.
assert (Hi : in_img tfibsegs a) by (apply in_img_rw; unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
pose proof (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR Hi) X) as Y. rewrite (ts_owned B HB) in Y.
apply Exists_exists in Y as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Tfib_owned_static in Hin. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. cbn in Hin.
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|]). exact Hin.
Qed.
(* the main tail after the loop (A/AD29cf.v tfib_main_tail), on the clipped view, with the room the tail law left *)
Definition main_tail_cf : Prop :=
forall E (W : world tfibsegs) ms md ly S data (pb : sptr) cap (v : Z) (k : nat) (fs : Fs),
(forall j, (j < K_M1)%nat -> ew E j = ew EL j) -> ed E 2 = data -> (2 <= length data)%nat ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E 180) = v -> (v = 0 \/ v = 2) ->
st_ok tfibsegs E S_CMF (restrict (w_H W) ms) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
In (pb, cap) (blocks S) -> qtight S -> ROOM_cf S -> cf_hull_ok S ->
so_state k (w_H W) (ms_mem ms) ->
(forall fd, fd_lookup (m_fds md) fd = fd_lookup APSG.fds_std fd) -> m_fs md = fs ->
(* field round 3 (Part A): the RELRO bytes, for the free's drv_pre *)
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex (if count_mode data then 0 else v) fs)).
Hypothesis MAINT : main_tail_cf.
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YP08.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma arodata_keep : forall (H H' : word -> bool) m m',
(forall a, in_ro_tfa a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview tfibsegs H' m' a = aview tfibsegs H m a) ->
arodata_ok B (aview tfibsegs H m) -> arodata_ok B (aview tfibsegs H' m').
Proof. intros H H' m m' HE HRO a H1 H2 H3. rewrite (HE a H1 H2 H3). exact (HRO a H1 H2 H3). Qed.
Lemma in_ro_range : forall a, in_ro_tfa a -> 0x10000 <= a < 0x9d000 \/ 0x9d470 <= a < 0x9e6c8.
Proof.
intros a [(sg & Hs & Hws & Hrg) | H]; [left | right; exact H].
cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
Qed.
Lemma arodata_frame : forall H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
arodata_ok B (aview tfibsegs H m) -> arodata_ok B (aview tfibsegs H m').
Proof.
intros H E rs m m' HF Hok U0 HRO. apply (arodata_keep H H m m'); [| exact HRO].
intros a Hro _ _. pose proof (in_ro_range a Hro) as Ha.
unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros Hw. rewrite u64_lit in Hw by lia. apply (in_wrange_drv E rs a Hok) in Hw.
destruct Hw as [Hw|Hw]; [unfold sp_window_lo in U0; lia | apply DRVW_lo in Hw; lia].
Qed.
(* what the driver's code between two calls keeps: fr_LI and fr_heap, when it keeps every G_fr_c byte and every byte
   off the image below the allocation ceiling (the live blocks lie there) *)
Definition lo_kept (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < alloc_ceiling -> (Exists (in_zr a) GF_RANGES \/ ~ in_img tfibsegs a) ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a /\ (apresent (w_H W) m a -> apresent (w_H W) m' a) /\
  (writable_at tfibsegs (mrestrict (w_H W) m) a -> writable_at tfibsegs (mrestrict (w_H W) m') a).
Lemma gf_lo : forall a, Exists (in_zr a) GF_RANGES -> 0 <= a < alloc_ceiling.
Proof.
intros a Ha. destruct (gf_avoids a Ha) as (_ & _ & _ & _ & _ & _ & _ & Hr).
pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV. lia.
Qed.
Lemma between_step : forall ci0 j buf cap q len (regs : bvmap 5 word) ly S (W : world tfibsegs) m md m',
  fr_LI B ci0 ly S W m -> fr_heap B j buf cap q len ly S W m -> ARcf tfibsegs B ly S [] W m md -> lo_kept W m m' ->
  fr_LI B ci0 ly S W m' /\ fr_heap B j buf cap q len ly S W m'.
Proof.
intros ci0 j buf cap q len regs ly S W m md m' HLI HH HAR K.
split.
- apply (fr_lib_inv_stable_ok B ci0 regs ly S W m ly S W m' HLI).
  + intros p0 n0 Hin. pose proof (alc_blocks _ _ ARL ly S [] W m md _ _ HAR Hin) as (_ & H4096 & Hce & _).
    pose proof YM05.alloc_ceiling_lt as CL. unfold req_size in Hce. destruct (Z.eqb_spec n0 0); lia.
  + intros a [Hg | Hfp].
    * unfold W_journal.inG in Hg. rewrite (G_fr_c_TfibB B HB) in Hg. exact (K a (gf_lo a Hg) (or_introl Hg)).
    * destruct (fr_FP_blocks B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md) LAWSX regs ly S [] W m md a HAR (proj2 HLI) Hfp)
        as (p0 & n0 & Hin & Ha).
      pose proof (alc_blocks _ _ ARL ly S [] W m md _ _ HAR Hin) as (_ & H4096 & Hce & _).
      apply K; [lia|]. right.
      exact (proj2 (alc_client_img _ _ ARL ly S [] W m md a HAR (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hin Ha)))))).
  + intros b Hb. exact Hb.
- apply (H_frame B j buf cap q len ly S W m ly S W m' HH); [| | | reflexivity | reflexivity].
  + intros i Hi. destruct (rg_words_gf i Hi) as (G1 & G2 & G3).
    split; [exact (proj1 (K _ (gf_lo _ G1) (or_introl G1)))|]. split; [exact (proj1 (K _ (gf_lo _ G2) (or_introl G2)))|].
    exact (proj1 (K _ (gf_lo _ G3) (or_introl G3))).
  + (* the program globals: G_fr_c bytes *)
    intros a Hg. unfold W_journal.inG in Hg. rewrite (G_fr_c_TfibB B HB) in Hg.
    destruct (K a (gf_lo a Hg) (or_introl Hg)) as (K1 & _ & K3). exact (conj K1 K3).
  + (* the bytes of a live block: below the allocation ceiling and off the image *)
    intros b n a Hin Ha. pose proof (alc_blocks _ _ ARL ly S [] W m md _ _ HAR Hin) as (_ & H4096 & Hce & _).
    assert (Ha' : b <= a < b + req_size n) by (unfold req_size in *; destruct (Z.eqb_spec n 0); lia).
    destruct (K a ltac:(lia) (or_intror (proj2 (alc_client_img _ _ ARL ly S [] W m md a HAR
      (or_introl (ex_intro _ b (ex_intro _ n (conj Hin Ha')))))))) as (K1 & _ & K3).
    exact (conj K1 K3).
Qed.
Lemma lo_kept_frame : forall E rs (W : world tfibsegs) m m',
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forallb drv_win_ok rs = true -> forallb region_gf_ok rs = true ->
  regions_wf rs = true -> alloc_ceiling <= bv_unsigned (ew E 0) - 65536 -> lo_kept W m m'.
Proof.
intros E rs W m m' HF Hok Hgf Hwf Hlo a Ha Hga.
exact (kept_of_rd (w_H W) m m' a (frame_keep_lo E rs (w_H W) m m' a HF Hok Hgf Hwf Hlo Ha Hga)).
Qed.
(* the driver's frames write only below the entry sp (its stack windows) or the image: the bytes at or above the
   entry sp keep their view *)
Lemma frame_keep_high : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
  forall a, bv_unsigned (ew E 0) <= a < 2 ^ 64 -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' HF Hok U0 a Ha. pose proof (u64_range (ew E 0)) as UE. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros Hw. rewrite u64_lit in Hw by lia. apply (in_wrange_drv E rs a Hok) in Hw.
destruct Hw as [Hw|Hw]; [lia | apply DRVW_lo in Hw; unfold sp_window_lo in U0; lia].
Qed.
Lemma aview_of_present : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma stk_up_frame : forall E rs ly (W : world tfibsegs) m m',
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
  top_ok usp ly -> stk_up usp ly W m -> stk_up usp ly W m'.
Proof.
intros E rs ly W m m' HF Hok E0 HT HU. pose proof Hsp as (Ulo & Uhi & _).
apply (stk_up_high usp ly ly W W m m'); [| reflexivity | exact Uhi | exact HT | exact HU].
intros a Ha. apply (frame_keep_high E rs (w_H W) m m' HF Hok); rewrite E0; [exact Ulo | lia].
Qed.
Lemma lo_kept_printf : forall (W : world tfibsegs) m m' spv,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spv - PF_STK <= a < spv) -> ~ STDOUT_MUT a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  alloc_ceiling <= spv - PF_STK -> lo_kept W m m'.
Proof.
intros W m m' spv Hfr Hpres Hlo a Ha Hga. pose proof YM05.alloc_ceiling_lt as CL.
assert (NSO : ~ STDOUT_MUT a).
{ intros X. destruct Hga as [Hg | Hni].
  - exact (proj1 (proj2 (gf_avoids a Hg)) X).
  - apply Hni. apply in_img_rw. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in X. lia. }
assert (HP : apresent (w_H W) m a -> apresent (w_H W) m' a) by (apply Hpres; [lia | exact NSO]).
split; [apply Hfr; [lia | lia | exact NSO]|]. split; [exact HP|]. exact (writable_of_pres (w_H W) m m' a HP).
Qed.
(* the cf call's journal (at the call's world relation R) keeps the driver's image regions (A/AD1r_fp.v
   journal_regions_kept_x at ARcf) *)
Lemma lib_reseat : forall E (W W' : world tfibsegs) regs mem regs' mem' ly S md ly' S' Hp' md' k FP,
st_ok tfibsegs E S_LF (mkst regs (w64 A_LLVMF) (mrestrict (w_H W) mem) (seg_rom tfibsegs)) ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) ->
YCbqG.ajournal_xR (SK := tfib_sink_head) tfibsegs B (W_LLVMFuzzerTestOneInput_G.G_fr_c B) (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md) R
  LLVMF_STK (usp - 208) (YI16.sink_token :: FP) ly S [] W mem md [] ly' S' Hp' W' mem' md' k ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_ofl_head 8 0 -> val_mem tfibsegs (mrestrict (w_H W') mem') A_ofl_head 8 0 ->
ARcf tfibsegs B ly S [] W mem md ->
aregs_preserved regs regs' -> getr regs' 10%bv = w64 0 -> YM05.ceil_of_top (usp - stack_max_size) ->
st_ok tfibsegs (havoc E K_LR (map (getr regs') CLOB')) S_LR (mkst regs' (Z_to_bv 64 RA_LLVMF) (mrestrict (w_H W') mem') (seg_rom tfibsegs)).
Proof.
intros E W W' regs mem regs' mem' ly S md ly' S' Hp' md' k FP HS E0 E6 HJ Hh0 Hh1 HAR HP Ha0 HCT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof calls_checks as (CKa & CKm & _).
rewrite S_LR_eq.
apply (st_ok_splice_havoc tfibsegs K_LR E S_LF regs regs' (w64 A_LLVMF) RA_LLVMF (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')
L_memF [(10%bv : bv 5, SLit 0)] CLOB' HS).
- exact CKa.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact CKm.
- exact (regs_kept_CLOB' regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. reflexivity.
-
pose proof (st_ok_mem_ok tfibsegs E S_LF _ HS) as HM. cbn [ms_mem] in HM.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))))))) in HM.
destruct HM as (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [| exact Hpd].
pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & _).
change L_memF with (WIN208 :: tl L_memF). constructor.
+ apply (region_ok_transport_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')); [exact Hr0 | intros c i Hc; destruct Hc |].
cbn [r_wlo r_whi r_base base_val WIN208]. rewrite E0. intros o Ho. apply (apresent_writable tfibsegs).
destruct (Z.lt_ge_cases (usp + o) (usp - 208 - LLVMF_STK)) as [Hlow | Hhi].
* pose proof Hr0 as (_ & _ & RW & _). cbn [r_wlo r_whi r_base base_val WIN208] in RW. rewrite E0 in RW.
assert (EQA : aview tfibsegs (w_H W') mem' (usp + o) = aview tfibsegs (w_H W) mem (usp + o)).
{ apply F1; [unfold sp_window_lo in Ulo; lia | lia]. }
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' (usp + o));
[unfold sp_window_lo in Ulo; lia | apply not_in_img_high; unfold sp_window_lo in Ulo; lia | exact EQA |].
apply apresent_of_writable; [unfold sp_window_lo in Ulo; lia | apply RW; lia].
* apply Hpres. lia.
+ exact (journal_regions_kept_x B HB (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md) LAWSX sp Hsp R E (tl L_memF)
    ly S [] W mem md ly' S' Hp' W' mem' md' k (usp - 208) FP HJ Hh0 Hh1 HAR (proj2 (andb_prop _ _ Hwf)) Hrs0
    ltac:(vm_compute; reflexivity) (proj1 (proj2 (proj2 calls_gf))) E0 E6 eq_refl HCT).
Qed.
Lemma vp_run : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_LR (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs)) md) (at_st S_LR S_VP E W mem md).
Proof.
intros E W regs mem md HS. pose proof HWXi as HWX. rewrite <- S_VP_eq. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma br_run : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_VPr (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs)) md) (at_st S_VPr S_BR E W mem md).
Proof.
intros E W regs mem md HS. pose proof HWXi as HWX. rewrite <- S_BR_eq. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma l2_run : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_BR cond_BRt) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_BR S_L2 E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. rewrite <- S_L2_eq. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma fq_run : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_BR cond_BRf) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_BR S_FQ E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. rewrite <- S_FQ_eq. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma xm_run : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_FQr (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_FQ) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_FQ) mem (seg_rom tfibsegs)) md) (at_st S_FQr S_XM E W mem md).
Proof.
intros E W regs mem md HS. pose proof HWXi as HWX. rewrite <- S_XM_eq. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma rdword_vararg : forall E (H : word -> bool) m,
mem_ok tfibsegs E (mrestrict H m) (ss_mem S_VP) -> bv_unsigned (ew E 0) = usp ->
rdword (aview tfibsegs H m) (usp - 288 + 24) = Some 0.
Proof.
intros E H m HM E0. destruct S_VP_vararg as (r & rest & Hm & Hb & Hin & _).
rewrite Hm in HM. destruct HM as (_ & Hok & _). pose proof (Forall_inv Hok) as (_ & _ & _ & HC).
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. rewrite Hb in Hc. cbn [base_val] in Hc. rewrite E0 in Hc.
set (a := usp - 288 + 24).
assert (BY : forall d, 0 <= d < 8 -> aview tfibsegs H m (a + d) = Some 0).
{ intros d Hd. destruct (Hc d ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off YP09.c_len] in Hb1, Hb2.
replace (usp + -264 + d) with (a + d) in Hb2 by lia. unfold aview. rewrite Hb2. cbn [option_map]. injection Hb1 as <-.
assert (D : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7) by lia.
destruct D as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity. }
assert (BY0 : aview tfibsegs H m a = Some 0) by (rewrite <- (Z.add_0_r a); apply BY; lia).
unfold rdword. rewrite BY0, !BY by lia. reflexivity.
Qed.
Lemma vp_reseat : forall E (W : world tfibsegs) regs mem regs' mem',
st_ok tfibsegs E S_VP (mkst regs (w64 A_icpt_vprintf) (mrestrict (w_H W) mem) (seg_rom tfibsegs)) ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) ->
aregs_preserved regs regs' -> getr regs' 10%bv = w64 2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (usp - 288 - PF_STK <= a < usp - 288) -> ~ STDOUT_MUT a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
st_ok tfibsegs (havoc E K_VP (map (getr regs') CLOB')) S_VPr (mkst regs' (Z_to_bv 64 RA_EMIT) (mrestrict (w_H W) mem') (seg_rom tfibsegs)).
Proof.
intros E W regs mem regs' mem' HS E0 E6 HP Ha0 Hfr Hpres.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. unfold sp_window_lo in Ulo.
pose proof calls_checks as (_ & _ & CKa & CKm & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFV & _ & WFQ & NCD).
rewrite (proj1 rsFQ_eq) in WFQ. pose proof L_mem0_shape as (_ & _ & _ & NCD0 & _).
pose proof so_ext_ok_L0 as [SOX KEEP].
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (usp - 288 - PF_STK <= a < usp - 288) -> ~ STDOUT_MUT a ->
mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Hr H1 H2. apply (mbyte_of_aview tfibsegs). apply Hfr; assumption. }
rewrite S_VPr_eq.
apply (st_ok_splice_havoc tfibsegs K_VP E S_VP regs regs' (w64 A_icpt_vprintf) RA_EMIT (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')
(ss_mem S_VP) [(10%bv : bv 5, SLit 2)] CLOB' HS).
- exact CKa.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact CKm.
- exact (regs_kept_CLOB' regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. reflexivity.
- pose proof (st_ok_mem_ok tfibsegs E S_VP _ HS) as HM. cbn [ms_mem] in HM. destruct HM as (Hwf & Hok & Hpd).
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
* rewrite Hb, Hwlo, Hwhi. cbn [base_val]. rewrite E0. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres; [unfold sp_window_hi in Uhi; lia | unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; lia|].
pose proof Hr0 as (_ & _ & RW & _). rewrite Hb, Hwlo, Hwhi in RW. cbn [base_val] in RW. rewrite E0 in RW.
apply apresent_of_writable; [lia | apply RW; lia].
+ rewrite Hrest in Hrs0, Hpd |- *. clear Hoffs.
assert (HMt : mem_ok tfibsegs E (mrestrict (w_H W) mem) (tl L_mem0)).
{ split; [exact WFQ | split; [exact Hrs0 | exact (proj2 Hpd)]]. }
assert (HK : Forall (region_kept tfibsegs E (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')) (tl L_mem0)).
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
exact (proj1 (proj2 (mem_ok_kept tfibsegs E _ (mrestrict (w_H W) mem') (tl L_mem0) HMt NCD HK))).
Qed.
Lemma l2_to_L : forall E (W : world tfibsegs) ms (r : Z),
st_ok tfibsegs E S_L2 (restrict (w_H W) ms) -> bv_unsigned (ew E 166) = r -> 2 <= r <= 4 ->
let E' := E_L2 E (ms_regs ms) in
st_ok tfibsegs E' S_LF (restrict (w_H W) ms) /\ bv_unsigned (ew E' 166) = r - 1 /\ (forall j, (j < 165)%nat -> ew E' j = ew E j).
Proof.
intros E W ms r HS V65 Hr E'. set (regs := ms_regs ms) in *.
pose proof S_L2_regs as (P8 & P9 & P10 & P11 & P18 & P19 & P20).
assert (RL : forall rg v, sr_get (ss_regs S_L2) rg = v -> getr regs rg = sv_denot E v).
{ intros rg v Hv. subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L2 ms rg HS), Hv. reflexivity. }
assert (R20 : getr regs 21%bv = w64 (r - 1)).
{ rewrite (RL 21%bv _ P20). cbn [sv_denot]. rewrite <- V65. unfold w64. f_equal. all: try lia. }
assert (NEW : forall i rg, (i < 15)%nat -> nth i L2_srcs 0%bv = rg -> ew E' (165 + i) = getr regs rg).
{ intros i rg Hi <-. subst E'. unfold E_L2. rewrite (ew_havoc_new E 165 _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < 165)%nat -> ew E' j = ew E j) by (intros j Hj; subst E'; unfold E_L2; apply ew_havoc_old; exact Hj).
assert (V65' : bv_unsigned (ew E' 166) = r - 1).
{ change 166%nat with (165 + 1)%nat. rewrite (NEW 1%nat 21%bv) by (cbn; first [lia | reflexivity]). rewrite R20. apply u64_lit. lia. }
split; [| split; [exact V65' | exact Eold]].
pose proof (st_ok_mem_ok tfibsegs E S_L2 _ HS) as HM0. cbn [restrict ms_mem] in HM0.
assert (HM1 : mem_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) L_memF).
{ apply (mem_ok_sub tfibsegs E _ (ss_mem S_L2)); [exact submem_L_L2 | exact (proj1 L_memF_wf) | exact HM0]. }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) L_memF).
{ apply (mem_ok_agree tfibsegs 165 E); [| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 calls_checks))))))))))))))) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_LF. rewrite <- (proj1 (proj2 (proj2 calls_pcs))).
apply (st_ok_reabs tfibsegs LT165 E E' S_L2 (restrict (w_H W) ms) L_regs L_memF L_facts HS).
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
Lemma xm_to_CM : forall E (W : world tfibsegs) ms,
st_ok tfibsegs E S_XM (restrict (w_H W) ms) ->
let E' := E_CM E (ms_regs ms) in
st_ok tfibsegs E' S_CMF (restrict (w_H W) ms) /\ bv_unsigned (ew E' 180) = 0 /\ (forall j, (j < K_CM)%nat -> ew E' j = ew E j).
Proof.
intros E W ms HS E'. set (regs := ms_regs ms) in *.
assert (R10 : getr regs 10%bv = w64 0).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_XM ms 10%bv HS), S_XM_regs. reflexivity. }
assert (NEW : forall i rg, (i < 16)%nat -> nth i CM_srcs 0%bv = rg -> ew E' (K_CM + i) = getr regs rg).
{ intros i rg Hi <-. subst E'. unfold E_CM. rewrite (ew_havoc_new E K_CM _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < K_CM)%nat -> ew E' j = ew E j) by (intros j Hj; subst E'; unfold E_CM; apply ew_havoc_old; exact Hj).
assert (V79 : bv_unsigned (ew E' 180) = 0).
{ change 180%nat with (K_CM + 0)%nat. rewrite (NEW 0%nat 10%bv) by (cbn; first [lia | reflexivity]). rewrite R10. apply u64_lit. lia. }
split; [| split; [exact V79 | exact Eold]].
pose proof (st_ok_mem_ok tfibsegs E S_XM _ HS) as HM0. cbn [restrict ms_mem] in HM0. rewrite (proj1 (proj2 rsFQ_eq)) in HM0.
assert (HM1 : mem_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) CM_memF).
{ rewrite <- (proj1 (proj2 (proj2 (proj2 rsFQ_eq)))). apply (mem_ok_refine E _ (WIN (-208) :: rsFQ)); [exact HM0 | apply refines_XM_CM |].
rewrite (proj1 (proj2 (proj2 (proj2 rsFQ_eq)))). exact (proj1 CM_memF_wf). }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) CM_memF).
{ apply (mem_ok_agree tfibsegs K_CM E); [| exact (proj1 (proj2 CM_memF_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_CMF. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 calls_pcs))))).
apply (st_ok_reabs tfibsegs LT180 E E' S_XM (restrict (w_H W) ms) CM_regs CM_memF CM_facts HS).
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
Lemma STDOUT_static : forall a, STDOUT_MUT a ->
in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha.
split; [apply in_img_hull; lia|]. split.
- rewrite (ts_owned B HB). intros X. apply Exists_exists in X as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Tfib_owned_static in Hin. cbn in Hin. repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|]). exact Hin.
- rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
Qed.
Lemma in_ro_static : forall a, in_ro_tfa a -> ~ (usp - 65536 <= a < usp + 65536) /\ ~ STDOUT_MUT a.
Proof.
intros a Ha. pose proof (in_ro_range a Ha). pose proof Hsp as (Ulo & _). unfold sp_window_lo in Ulo.
unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI. lia.
Qed.
(* neither the stdout FILE / buffer nor a read-only byte is a G_fr_c byte *)
Lemma not_gf : forall a, STDOUT_MUT a \/ in_ro_tfa a -> ~ Exists (in_zr a) (W_LLVMFuzzerTestOneInput_G.G_fr_c B).
Proof.
intros a Ha X. rewrite (G_fr_c_TfibB B HB) in X. destruct (gf_avoids a X) as (H1 & H2 & _).
destruct Ha as [Ha|Ha]; [exact (H2 Ha) | exact (H1 Ha)].
Qed.
Definition Kstep (pl : list byte) (N j r : nat) (l : lleaf) : TSet :=
match j with
| O => wr ch_stdout line0 (lib_iter pl r (run_tail r) (ll_fs l))
| S _ => lib_iter pl r (run_tail (N - 1)) (ll_fs l)
end.
Lemma loop_tgt_step : forall pl N j r fs, (j + S r = N)%nat -> loop_tgt pl N j (S r) fs = LIBK pl fs (Kstep pl N j r).
Proof. intros pl N [|j] r fs HN; reflexivity. Qed.
Theorem calls_loop : forall (r j : nat) E (W : world tfibsegs) ms md ly S data (buf cap q : Z) (fs : Fs) (N : nat),
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew EL k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = buf ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok tfibsegs E S_LF (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = N)%nat -> (N <= 4)%nat ->
(payload_len data = 0 -> q = 0) ->
fr_heap B j buf cap q (payload_len data) ly S W (ms_mem ms) ->
(0 < payload_len data -> blk (w_H W) (ms_mem ms) q (payload_len data) (payload data)) ->
frames S = [] -> qtight S ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap -> (2 <= length data)%nat ->
NP S -> NS S + (4 - Z.of_nat j) * XNMAX <= NRUN -> fr_LI B (Z.of_nat j) ly S W (ms_mem ms) -> stk_up usp ly W (ms_mem ms) ->
so_state j (w_H W) (ms_mem ms) -> arodata_ok B (aview tfibsegs (w_H W) (ms_mem ms)) ->
FINV ly (w_H W) (ms_mem ms) -> MDI md fs ->
(* field round 3 (Part A): the memory's read-only RELRO bytes, for the call's pre and the frees after the last call *)
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (loop_tgt (payload data) N j r fs).
Proof.
induction r as [|r IH]; [intros; lia|].
intros j E W ms md ly S data buf cap q fs N Hlk Hok HEE HEd E41 E61 E62 E63 E65 HS _ HjrN HN4 HZQ HH HPL Hfr HQT HAI HAR HTOP Hcap HLc Hlen HNP HNS HLI HUP HSO HRO HFI HMD HAD.
assert (Hjr : (j + Datatypes.S r <= 4)%nat) by lia.
pose proof HMD as (Hfdl0 & Hnames0 & Hmfs & Hsorted0).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (config_len_bound data) as Hcl.
assert (Hpl : 0 <= payload_len data < cap) by (unfold payload_len, HDR_MIN in *; lia).
assert (E0 : bv_unsigned (ew E 0) = usp) by (rewrite HEE by (unfold K_M1; lia); reflexivity).
assert (E6 : usp <= bv_unsigned (ew E 6)) by (rewrite HEE by (unfold K_M1; lia); exact EL6).
pose proof calls_pcs as (PCV & PCB & PCL2 & PCF & PCX & PCLR & PCVr & PCFr & RVV & RVL2 & RVF & RVX & RVB & RVL).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E S_LF ms HS RVL) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof S_L_regs as (Q1 & Q2 & Q3 & Q4 & Q8 & Q10 & Q11).
assert (R1 : getr regs 1%bv = w64 RA_LLVMF) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 1%bv HS), Q1; reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -208)) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 2%bv HS), Q2; cbn [sv_denot]; rewrite E0; reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 3%bv HS), Q3; reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 4%bv HS), Q4; reflexivity).
assert (R8 : getr regs 8%bv = w64 (payload_len data)).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 8%bv HS), Q8. cbn [sv_denot]. rewrite Z.add_0_r, <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R10 : getr regs 10%bv = w64 (if payload_len data =? 0 then A_EMPTY_tfa else q)).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 10%bv HS), Q10. cbn [sv_denot]. rewrite Z.add_0_r, <- E62. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R11 : getr regs 11%bv = w64 (payload_len data)).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_LF ms 11%bv HS), Q11. cbn [sv_denot]. rewrite Z.add_0_r, <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hsp' : spZ regs = usp - 208) by (unfold spZ; rewrite R2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (Hra : raZ regs = RA_LLVMF) by (unfold raZ; rewrite R1; apply u64_lit; unfold RA_LLVMF; lia).
assert (Hs0 : s0Z regs = payload_len data) by (unfold s0Z; rewrite R8; apply u64_lit; lia).
pose proof (st_ok_mem_ok tfibsegs E S_LF _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E (w_H W) mem L_memF); [exact HM | left; reflexivity | exact E0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem L_memF); [exact HM | right; left; reflexivity | exact E0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem L_memF); [exact HM | right; right; left; reflexivity | exact E0 | lia | lia | cbn; lia]. }
rewrite Hshape, PCL2 || rewrite Hshape. fold regs mem.
replace (Z_to_bv 64 (ss_pc S_LF)) with (w64 A_LLVMF) by reflexivity.
change (mkCfg (mkst regs (w64 A_LLVMF) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_LLVMF regs mem md).
assert (PRE : lib_pre_cf B ly S W regs mem md).
{ split; [exact HAR|]. split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [exact Hra|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [rewrite Hsp'; replace (usp - 208) with (usp + (-13) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp'; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [exact (proj1 (proj2 HTOP))|]. split; [exact (proj1 (proj2 (proj2 HTOP)))|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold LLVMF_STK in Ha; lia|].
split; [| exact HQT]. rewrite Hs0. lia. }
rewrite (loop_tgt_step (payload data) N j r fs HjrN), <- Hmfs.
apply (LIB ly S W regs mem md (if payload_len data =? 0 then A_EMPTY_tfa else q) (payload_len data) (payload data) (Z.of_nat j) (Kstep (payload data) N j r) PRE R10 R11).
{ destruct (Z.eqb_spec (payload_len data) 0) as [Hz|Hnz].
+ left. split; [exact Hz | reflexivity].
+ right. split; [lia|]. exact (proj2 (H_in B _ _ _ _ _ _ _ _ _ HH) ltac:(lia)). }
{ symmetry. apply payload_length. exact Hok. }
{ destruct (Z.eqb_spec (payload_len data) 0) as [Hz|Hnz].
+ assert (Hpn : payload data = []) by (apply length_zero_iff_nil; pose proof (payload_length data Hok); lia). rewrite Hpn. apply YI00.garr8_nil.
+ apply garr8_of_blk. rewrite (payload_length data Hok). apply HPL. lia. }
{ exact Hfr. }
{ exact (H_live B _ _ _ _ _ _ _ _ _ HH ltac:(lia) Hcap Hpl). }
{ exact HNP. }
{ (* this call is call j < 4, so the room left for the calls to come covers this call's step *)
  assert (X : XNMAX <= (4 - Z.of_nat j) * XNMAX) by nia. lia. }
{ pose proof (proj2 (H_bytes B _ _ _ _ _ _ _ _ _ HH ltac:(lia))) as X. unfold DRV_LIVE. lia. }
{ lia. }
{ exact HLI. }
{ exact (rom_view_of_arodata B HB (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md) LAWSX ly S [] W mem md HAR HRO). }
{ intros a Ha. rewrite Hsp' in Ha. destruct (Z.lt_ge_cases a usp) as [Hlt|Hge].
  - exact (aview_of_present _ _ _ (Hwin a ltac:(lia))).
  - exact (HUP a ltac:(lia)). }
{ exact (H_call B _ _ _ _ _ _ _ _ _ A_EMPTY_tfa HH ltac:(lia)). }
{ exact (H_xcnt B _ _ _ _ _ _ _ _ _ A_EMPTY_tfa HH). }
{ exact (H_capout B _ _ _ _ _ _ _ _ _ HH). }
{ exact HRO. }
{ exact HFI. }
{ exact HAD. }
{
assert (AFX : forall f1 f2, (forall k0, fd_lookup f1 k0 = fd_lookup f2 k0) -> forall fuel c, alloc_fd_aux f1 c fuel = alloc_fd_aux f2 c fuel).
{ intros f1 f2 Hf. induction fuel as [|fuel IHf]; intros c; cbn; [reflexivity|]. rewrite Hf. destruct (fd_lookup f2 c); [apply IHf | reflexivity]. }
unfold alloc_fd. rewrite (AFX _ _ Hfdl0), Hfdl0. vm_compute. reflexivity. }
{ exact Hnames0. }
{ rewrite Hmfs. exact Hsorted0. }
{ exact HAI. }
intros l W' c' _ HAI' (ly' & S' & regs' & mem' & md' & k & -> & HJ & Hlv & HNP' & HP & Ha0' & HSV & HLI' & _ & Hfdl & Hmfs' & Hret & Hout & Hsorted & Hnames' & HFI' & Hplk & HHFP' & HXC' & HCAP' & HNS' & HAD'). cbn [cfg_model] in HAI'.
unfold cfg_at.
pose proof HJ as (HAR' & Hlyle & Hsecs & Hwle & Hos & Hfrs & _ & Hk0 & F1 & F2 & F3 & F4 & Hgone & HpresJ & Hstk & F5 & HQT').
rewrite Hfr in Hfrs. cbn [app] in Hfrs.
assert (HTOP' : top_ok usp ly') by exact (top_ok_le _ _ _ _ Hlyle HTOP).
(* the post's XCNT clause is at the call's input list, which is fr_heap's (the call's p is q when there is a payload) *)
assert (HXC2 : fr_xcnt_ok B ly' S' W' mem' (if payload_len data =? 0 then [] else [(q, payload_len data)]))
  by (revert HXC'; destruct (payload_len data =? 0); intros X; exact X).
pose proof (H_step B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH HSV Hlv HHFP' HCAP' HXC2) as HH'.
assert (HLIc : fr_LI B (Z.of_nat (Datatypes.S j)) ly' S' W' mem') by (rewrite Nat2Z.inj_succ; exact HLI').
destruct (H_in B _ _ _ _ _ _ _ _ _ HH') as [Hinb Hinq'].
assert (HSO' : so_state j (w_H W') mem').
{ apply (so_state_keep j (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. destruct (STDOUT_static a Ha) as (H1 & H2 & H3).
exact (F3 a H1 H2 H3 (not_gf a (or_introl Ha)) (spares_stdout_FP _ a Ha)). }
assert (HRO' : arodata_ok B (aview tfibsegs (w_H W') mem')).
{ apply (arodata_keep (w_H W) (w_H W') mem mem'); [| exact HRO]. intros a H1 H2 H3.
apply F3; [| exact H2 | exact H3 | exact (not_gf a (or_intror H1)) | exact (spares_ro_FP _ a H1)]. apply in_img_hull. pose proof (in_ro_range a H1). lia. }
assert (HPL' : 0 < payload_len data -> blk (w_H W') mem' q (payload_len data) (payload data)).
{ intros Hp. replace (payload_len data =? 0) with false in Hplk by (symmetry; apply Z.eqb_neq; lia).
assert (Hinq : In (q, payload_len data) (ablocks B ly S)) by exact (proj2 (H_in B _ _ _ _ _ _ _ _ _ HH) Hp).
pose proof (alc_blocks _ _ ARL ly S _ W mem md _ _ HAR Hinq) as (_ & Hq4096 & Hqce & _).
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia). rewrite Hreqq in Hqce.
assert (NIMGQ : forall a, q <= a < q + payload_len data -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : q <= a < q + req_size (payload_len data)) by (rewrite Hreqq; exact Ha).
exact (proj2 (alc_client_img _ _ ARL ly S _ W mem md a HAR (or_introl (ex_intro _ q (ex_intro _ (payload_len data) (conj Hinq Ha')))))). }
apply (blk_copy (w_H W) (w_H W') mem mem' q q (payload_len data) (payload data) Hplk (fun i Hi => NIMGQ (q + i) ltac:(lia)) ltac:(lia) ltac:(lia) (fun i Hi => NIMGQ (q + i) ltac:(lia)) ltac:(lia) ltac:(lia)).
exact (HPL Hp). }
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
pose proof (lib_reseat E W W' regs mem regs' mem' ly S md ly' S' [] md' k _ HS E0 E6 ltac:(rewrite <- Hsp'; exact HJ) (proj2 (proj2 HFI)) (proj2 (proj2 HFI')) HAR HP Ha0' HCT) as HS2.
set (E2 := havoc E K_LR (map (getr regs') CLOB')) in HS2.
assert (E2old : forall i, (i < K_LR)%nat -> ew E2 i = ew E i) by (intros i Hi; subst E2; apply ew_havoc_old; exact Hi).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E6).
assert (ULO : alloc_ceiling <= usp - 65536 - PF_STK - 288) by (unfold PF_STK; lia).
rewrite <- restrict_mkst_fx in HS2.
apply (SRr_srealizes tfibsegs W' _ _ _ (vp_run E2 W' regs' mem' md' HS2) HAI').
intros W1 c1 _ HAI3 (-> & msV & matV & -> & HSV' & HFV & HFrV). cbn [cfg_model] in HAI3.
set (mdV := with_vm_backing (m_vm_lazy md') matV md') in *.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E2 S_VP msV HSV' RVV) as HshapeV.
set (regsV := ms_regs msV) in *. set (memV := ms_mem msV) in *.
pose proof S_VP_regs as (V1 & V2 & V3 & V4 & V10 & V11).
assert (RV1 : getr regsV 1%bv = w64 RA_EMIT) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 1%bv HSV'), V1; reflexivity).
assert (RV2 : getr regsV 2%bv = Z_to_bv 64 (usp + -288)) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 2%bv HSV'), V2; cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (RV3 : getr regsV 3%bv = w64 TFIB_GP) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 3%bv HSV'), V3; reflexivity).
assert (RV4 : getr regsV 4%bv = w64 TFIB_TP) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 4%bv HSV'), V4; reflexivity).
assert (RV10 : getr regsV 10%bv = w64 A_FMT_D) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 10%bv HSV'), V10; reflexivity).
assert (RV11 : getr regsV 11%bv = Z_to_bv 64 (usp + -264)) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 11%bv HSV'), V11; cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (HspV : spZ regsV = usp - 288) by (unfold spZ; rewrite RV2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (HraV : raZ regsV = RA_EMIT) by (unfold raZ; rewrite RV1; apply u64_lit; unfold RA_EMIT; lia).
pose proof (st_ok_mem_ok tfibsegs E2 S_VP _ HSV') as HMV. cbn [restrict ms_mem] in HMV. fold memV in HMV.
assert (HwinV : forall a, usp - 65536 <= a < usp -> apresent (w_H W') memV a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | right; right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
assert (HARV : ARcf tfibsegs B ly' S' [] W' memV mdV).
{ apply (AR_after_run B HB ARL ly' S' _ W' E2 L_memF mem' memV md' matV HAR' (proj2 (proj2 (proj2 L_memF_wf)))); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HFV |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (HwinV a Ha)). }
pose proof calls_gf as (GFL & GFV & _ & WOKL & WFL).
destruct (between_step _ _ _ _ _ _ regs' ly' S' W' mem' md' memV HLIc HH' HAR'
  (lo_kept_frame E2 L_memF W' mem' memV HFrV WOKL GFL WFL ltac:(rewrite E2_0; lia))) as [HLIV HHV].
(* the entry image above the entry sp: kept by the call's journal (high memory off the callee's stack window), then
   by the vprintf frame *)
assert (HUP' : stk_up usp ly' W' mem').
{ apply (stk_up_high usp ly' ly' W W' mem mem'); [| reflexivity | exact Uhi | exact HTOP' | exact (stk_up_lyle usp _ ly ly' W mem Hlyle HUP)].
  intros a Ha. apply F1; [lia | rewrite Hsp'; unfold LLVMF_STK; lia]. }
pose proof (stk_up_frame E2 L_memF ly' W' mem' memV HFrV WOKL E2_0 HTOP' HUP') as HUPV.
assert (HSOV : so_state j (w_H W') memV).
{ exact (so_state_frame j (w_H W') E2 L_memF _ _ HFrV (proj2 (proj2 CM_so_okF)) ltac:(rewrite E2_0; exact Ulo) ltac:(rewrite E2_0; exact E2_6) HSO'). }
assert (HROV : arodata_ok B (aview tfibsegs (w_H W') memV)).
{ exact (arodata_frame (w_H W') E2 L_memF _ _ HFrV (proj2 (proj2 (proj2 L_memF_wf))) ltac:(rewrite E2_0; exact Ulo) HRO'). }
assert (HRD : rdword (aview tfibsegs (w_H W') memV) (spZ regsV + 24) = Some 0) by (rewrite HspV; exact (rdword_vararg E2 (w_H W') memV HMV E2_0)).
assert (PREV : printf_pre B ly' S' [] W' regsV memV mdV).
{ split; [exact HARV|]. split; [exact HraV|].
split; [rewrite HspV; replace (usp - 288) with (usp + (-18) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite HspV; lia|]. split; [rewrite HspV; unfold top_ok in HTOP'; lia|].
split; [rewrite HspV; lia|]. split; [unfold top_ok in HTOP'; tauto|]. split; [unfold top_ok in HTOP'; tauto|]. split; [exact HROV|].
split; [rewrite HspV; intros a Ha; apply HwinV; unfold PF_STK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact RV3|]. split; [rewrite (ts_tp B HB); exact RV4|].
split; [exact RV10|]. split; [rewrite RV11, HspV; unfold w64; f_equal; lia | exact HRD]. }
assert (HfdlV : forall fd, fd_lookup (m_fds mdV) fd = fd_lookup APSG.fds_std fd) by (intros fd; subst mdV; rewrite wvb_fds', Hfdl; apply Hfdl0).
assert (POST : printf_post B xst ly' S' [] W' regsV memV mdV (Datatypes.S j) (lib_iter (payload data) r (run_tail (N - 1)) (ll_fs l))).
2:{ rewrite HshapeV, PCV. fold regsV memV.
change (mkCfg (mkst regsV (Z_to_bv 64 A_icpt_vprintf) memV (seg_rom tfibsegs)) mdV) with (cfg_at tfibsegs A_icpt_vprintf regsV memV mdV).
destruct j as [|j'].
-
cbn [Kstep]. replace (N - 1)%nat with r in POST by lia.
exact (PF1 ly' S' [] W' regsV memV mdV _ PREV ltac:(destruct HSOV as [[_ X]|[X _]]; [exact X | exfalso; lia]) HfdlV HAI3 POST).
-
cbn [Kstep]. exact (PFN ly' S' [] W' regsV memV mdV _ (Datatypes.S j') PREV ltac:(destruct HSOV as [[X _]|[_ X]]; [exfalso; lia | exact X]) ltac:(lia) HfdlV HAI3 POST). }
intros regs4 mem4 md4 HAR4 HP4 Hs4 Ha04 HX4 Hfr4 Hpres4 HAI4. unfold cfg_at. rewrite HraV. rewrite HspV in Hfr4.
pose proof (same_but_materialized_frame _ _ Hs4) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds4 & _ & _ & Hfs4 & _).
destruct (between_step _ _ _ _ _ _ regsV ly' S' W' memV mdV mem4 HLIV HHV HARV
  (lo_kept_printf W' memV mem4 (usp - 288) Hfr4 Hpres4 ltac:(lia))) as [HLI4 HH4].
assert (HUP4 : stk_up usp ly' W' mem4).
{ apply (stk_up_high usp ly' ly' W' W' memV mem4); [| reflexivity | exact Uhi | exact HTOP' | exact HUPV].
  intros a Ha. apply Hfr4; [lia | unfold PF_STK; lia |].
  unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; unfold sp_window_lo in Ulo; lia. }
rewrite HshapeV, restrict_mkst_fx in HSV'. fold regsV memV in HSV'. rewrite PCV in HSV'.
pose proof (vp_reseat E2 W' regsV memV regs4 mem4 HSV' E2_0 E2_6 HP4 Ha04 Hfr4 Hpres4) as HS5.
set (E4 := havoc E2 K_VP (map (getr regs4) CLOB')) in HS5.
assert (E4old : forall i, (i < K_VP)%nat -> ew E4 i = ew E2 i) by (intros i Hi; subst E4; apply ew_havoc_old; exact Hi).
assert (E4_0 : bv_unsigned (ew E4 0) = usp) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); exact E2_0).
assert (E4_6 : usp <= bv_unsigned (ew E4 6)) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); exact E2_6).
assert (E4_65 : bv_unsigned (ew E4 166) = Z.of_nat (Datatypes.S r)) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E65).
assert (HSO4 : so_state (Datatypes.S j) (w_H W') mem4) by (right; split; [lia | exact HX4]).
assert (HRO4 : arodata_ok B (aview tfibsegs (w_H W') mem4)).
{ apply (arodata_keep (w_H W') (w_H W') memV mem4); [| exact HROV]. intros a H1 _ _. destruct (in_ro_static a H1) as [Y1 Y2]. pose proof (in_ro_range a H1).
apply Hfr4; [lia | unfold PF_STK; lia | exact Y2]. }
assert (Hwin4 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem4 a)
by (intros a Ha; apply Hpres4; [unfold sp_window_lo, sp_window_hi in *; lia | unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; unfold sp_window_lo in Ulo; lia | apply HwinV; exact Ha]).
rewrite <- restrict_mkst_fx in HS5.
apply (SRr_srealizes tfibsegs W' _ _ _ (br_run E4 W' regs4 mem4 md4 HS5) HAI4).
intros W2 c2 _ HAI5 (-> & msB & matB & -> & HSB & HFB & HFrB). cbn [cfg_model] in HAI5.
set (mdB := with_vm_backing (m_vm_lazy md4) matB md4) in *.
pose proof (st_ok_mem_ok tfibsegs E4 S_BR _ HSB) as HMB. cbn [restrict ms_mem] in HMB.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))))) in HMB.
assert (HwinB : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem msB) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
pose proof calls_checks as (_ & _ & _ & _ & CKF & WFF & NCF & MAF & KPF & WOKV & SOKV & WOKF & SOKF & WFV & _).
assert (HARB : ARcf tfibsegs B ly' S' [] W' (ms_mem msB) mdB).
{ apply (AR_after_run B HB ARL ly' S' _ W' E4 (ss_mem S_VP) mem4 (ms_mem msB) md4 matB HAR4 WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFB |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinB a Ha)). }
destruct (between_step _ _ _ _ _ _ regs4 ly' S' W' mem4 md4 (ms_mem msB) HLI4 HH4 HAR4
  (lo_kept_frame E4 (ss_mem S_VP) W' mem4 (ms_mem msB) HFrB WOKV GFV WFV ltac:(rewrite E4_0; lia))) as [HLIB HHB].
pose proof (stk_up_frame E4 (ss_mem S_VP) ly' W' mem4 (ms_mem msB) HFrB WOKV E4_0 HTOP' HUP4) as HUPB.
assert (HSOB : so_state (Datatypes.S j) (w_H W') (ms_mem msB)).
{ exact (so_state_frame (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrB SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSO4). }
assert (HROB : arodata_ok B (aview tfibsegs (w_H W') (ms_mem msB))).
{ exact (arodata_frame (w_H W') E4 (ss_mem S_VP) _ _ HFrB WOKV ltac:(rewrite E4_0; exact Ulo) HRO4). }
assert (HfsB : m_fs mdB = ll_fs l) by (subst mdB; rewrite wvb_fs', Hfs4; subst mdV; rewrite wvb_fs'; exact Hmfs').
assert (HfdB : m_fds mdB = m_fds md') by (subst mdB; rewrite wvb_fds', Hfds4; subst mdV; rewrite wvb_fds'; reflexivity).
assert (HFIB : FINV ly' (w_H W') (ms_mem msB)).
{ assert (HFIV : FINV ly' (w_H W') memV) by exact (finv_run B ly' S' _ W' mem' md' (w_H W') E2 L_memF _ _ usp HAR' HFrV (proj2 (proj2 (proj2 L_memF_wf))) E2_0 Ulo Uhi HTOP' HFI').
assert (HFI4 : FINV ly' (w_H W') mem4) by exact (finv_printf B HB ARL ly' S' _ W' memV mdV mem4 usp (usp - 288) HARV HTOP' Ulo Uhi ltac:(lia) Hfr4 HFIV).
exact (finv_run B ly' S' _ W' mem4 md4 (w_H W') E4 (ss_mem S_VP) _ _ usp HAR4 HFrB WOKV E4_0 Ulo Uhi HTOP' HFI4). }
(* field round 3 (Part A): the RELRO bytes after the call: its post (fr_lib_post_drvR's last), the run to vprintf,
   vprintf's view frame, the run past it *)
assert (HADB : arodata_ok_cf tfibsegs B (ms_mem msB)).
{ assert (HADV : arodata_ok_cf tfibsegs B memV)
  by exact (aro_run B W' E2 L_memF mem' memV RO HFrV (proj2 (proj2 (proj2 L_memF_wf))) ltac:(rewrite E2_0; exact Ulo) HAD').
  assert (HAD4 : arodata_ok_cf tfibsegs B mem4) by exact (aro_printf B W' memV mem4 usp (usp - 288) RO Ulo ltac:(lia) Hfr4 HADV).
  exact (aro_run B W' E4 (ss_mem S_VP) mem4 (ms_mem msB) RO HFrB WOKV ltac:(rewrite E4_0; exact Ulo) HAD4). }
assert (HPLB : 0 < payload_len data -> blk (w_H W') (ms_mem msB) q (payload_len data) (payload data)).
{ intros Hp. pose proof (HPL' Hp) as HPLm.
pose proof (Hinq' Hp) as Hinq.
pose proof (alc_blocks _ _ ARL ly' S' _ W' mem' md' _ _ HAR' Hinq) as (_ & Hq4096 & Hqce & _).
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia). rewrite Hreqq in Hqce.
assert (NIMGQ : forall a, q <= a < q + payload_len data -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : q <= a < q + req_size (payload_len data)) by (rewrite Hreqq; exact Ha).
exact (proj2 (alc_client_img _ _ ARL ly' S' _ W' mem' md' a HAR' (or_introl (ex_intro _ q (ex_intro _ (payload_len data) (conj Hinq Ha')))))). }
assert (HPLV : blk (w_H W') memV q (payload_len data) (payload data)).
{ apply (blk_of_frame_r _ E2 L_memF _ _ q (payload_len data) (payload data) usp HFrV (proj2 (proj2 (proj2 L_memF_wf))) E2_0 Ulo NIMGQ); [lia | lia | exact HPLm]. }
assert (HPL4 : blk (w_H W') mem4 q (payload_len data) (payload data)).
{ apply (blk_copy (w_H W') (w_H W') memV mem4 q q (payload_len data) (payload data)); [| exact (fun i Hi => NIMGQ (q + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGQ (q + i) ltac:(lia)) | lia | lia | exact HPLV].
intros i Hi. apply Hfr4; [lia | unfold PF_STK; lia |]. intros X. apply (NIMGQ (q + i) ltac:(lia)). apply in_img_rw. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in X. lia. }
apply (blk_of_frame_r _ E4 (ss_mem S_VP) _ _ q (payload_len data) (payload data) usp HFrB WOKV E4_0 Ulo NIMGQ); [lia | lia | exact HPL4]. }
destruct (Nat.eq_dec r 0) as [Hr0 | Hr1].
-
assert (HSB' : st_ok tfibsegs E4 (add_cond S_BR cond_BRf) (restrict (w_H W') msB)).
{ apply (st_ok_add_cond tfibsegs E4 S_BR _ BC_EQ (SOff 166 (-1)) (SLit 0) HSB). cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite E4_65, Hr0. reflexivity. }
apply (SRr_srealizes tfibsegs W' _ _ _ (fq_run E4 W' msB mdB HSB') HAI5).
intros W3 c3 _ HAI6 (-> & msF & matF & -> & HSF & HFF & HFrF). cbn [cfg_model] in HAI6.
set (mdF := with_vm_backing (m_vm_lazy mdB) matF mdB) in *.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E4 S_FQ msF HSF RVF) as HshapeF.
set (regsF := ms_regs msF) in *. set (memF := ms_mem msF) in *.
pose proof S_FQ_regs as (F1r & F2r & F3r & F4r & F8r & F10r).
assert (RF1 : getr regsF 1%bv = w64 RA_FQ) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 1%bv HSF), F1r; reflexivity).
assert (RF2 : getr regsF 2%bv = Z_to_bv 64 (usp + -208)) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 2%bv HSF), F2r; cbn [sv_denot]; rewrite E4_0; reflexivity).
assert (RF3 : getr regsF 3%bv = w64 TFIB_GP) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 3%bv HSF), F3r; reflexivity).
assert (RF4 : getr regsF 4%bv = w64 TFIB_TP) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 4%bv HSF), F4r; reflexivity).
assert (RF8 : getr regsF 8%bv = w64 (payload_len data)).
{ subst regsF. rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 8%bv HSF), F8r. cbn [sv_denot].
rewrite Z.add_0_r, E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (RF10 : getr regsF 10%bv = w64 q).
{ subst regsF. rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 10%bv HSF), F10r. cbn [sv_denot].
rewrite Z.add_0_r, E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite <- E63. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (HspF : spZ regsF = usp + -208) by (unfold spZ; rewrite RF2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (HraF : raZ regsF = RA_FQ) by (unfold raZ; rewrite RF1; apply u64_lit; unfold RA_FQ; lia).
pose proof (st_ok_mem_ok tfibsegs E4 S_FQ _ HSF) as HMF. cbn [restrict ms_mem] in HMF. fold memF in HMF.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq))))))))) in HMF.
assert (HwinF : forall a, usp - 65536 <= a < usp -> apresent (w_H W') memF a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HARF : ARcf tfibsegs B ly' S' [] W' memF mdF).
{ apply (AR_after_run B HB ARL ly' S' _ W' E4 (ss_mem S_VP) (ms_mem msB) memF mdB matF HARB WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFF |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinF a Ha)). }
assert (HSOF : so_state (Datatypes.S j) (w_H W') memF).
{ exact (so_state_frame (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrF SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSOB). }
assert (HADF : arodata_ok_cf tfibsegs B memF)
by exact (aro_run B W' E4 (ss_mem S_VP) (ms_mem msB) memF RO HFrF WOKV ltac:(rewrite E4_0; exact Ulo) HADB).
assert (HWF' : Wf_cf (as_universe B) S') by exact (amc_wf _ _ _ [] _ (proj1 HARF)).
(* the tail law: the room for both frees after the last call (q here, the buffer in the main tail) *)
pose proof (NPT S' HNP') as HROOM2.
pose proof (RK_room S' 2 HROOM2) as HROOMF.
(* the hull admission after the last call: its step left NS S' <= NS S + XNMAX, inside the room (4 - j) * XNMAX *)
assert (HNSF : NS S' <= NRUN) by (assert (X : XNMAX <= (4 - Z.of_nat j) * XNMAX) by nia; lia).
assert (PREF : drv_pre B ly' S' [] W' regsF memF mdF).
{ split; [exact HARF|]. split; [unfold top_ok in *; tauto|]. split; [exact (conj eq_refl HROOMF)|].
split; [rewrite RF1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite HraF; unfold RA_FQ; lia|].
split; [rewrite HspF; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite HspF; unfold sp_window_lo in *; lia|]. split; [rewrite HspF; unfold top_ok in HTOP'; lia|].
split; [rewrite HspF; intros a Ha; apply HwinF; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact RF3|]. split; [rewrite (ts_tp B HB); exact RF4|].
split; [| exact (conj HQT' (conj (HULL_NS S' HNSF) HADF))]. unfold s0Z. rewrite RF8. unfold w64. rewrite u64_lit by lia. lia. }
assert (Hbuf : 4096 <= buf).
{ pose proof (alc_blocks _ _ ARL ly' S' _ W' memF mdF _ _ HARF Hinb) as (_ & X & _). exact X. }
rewrite HshapeF, PCF. fold regsF memF. replace (Z_to_bv 64 A_wrap_free) with (w64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); reflexivity).
change (mkCfg (mkst regsF (w64 (pc_wrap_free (as_code B))) memF (seg_rom tfibsegs)) mdF) with (cfg_at tfibsegs (pc_wrap_free (as_code B)) regsF memF mdF).
assert (FSITE : exists (pf : sptr) (nf : Z) (Eb : Z -> Prop),
(pf = PNull \/ In (pf, nf) (blocks S')) /\ nf < cap /\ (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) /\ (forall a, Eb a -> ~ STDOUT_MUT a) /\
SRrG tfibsegs R W' (cfg_at tfibsegs (pc_wrap_free (as_code B)) regsF memF mdF)
(fun W'' c'' => exists ly6 S6 regs6 mem6 md6 trc tr,
In trc (as_universe B) /\ apath (free_cf pf trc S') tr (tt, S6) /\
c'' = cfg_at tfibsegs (raZ regsF) regs6 mem6 md6 /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly' S' [] W' regsF memF mdF Eb ly6 S6 W'' regs6 mem6 md6)).
{ destruct (Z.eqb_spec (payload_len data) 0) as [Hz | Hnz].
- exists PNull, 0, (fun _ => False). split; [left; reflexivity|]. split; [lia|]. split; [intros a []|]. split; [intros a []|].
apply (FREEN ly' S' [] W' regsF memF mdF PREF).
+ rewrite RF10, (HZQ Hz). reflexivity.
+ rewrite (ts_code B HB), HraF. apply (ts_universe_drv B HB). cbn. tauto.
+ rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- assert (Hp : 0 < payload_len data) by lia.
pose proof (Hinq' Hp) as Hinq.
pose proof (alc_blocks _ _ ARL ly' S' _ W' memF mdF _ _ HARF Hinq) as (_ & Hq4096 & Hqce & _).
assert (NIMGQ : forall a, q <= a < q + req_size (payload_len data) -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (alc_client_img _ _ ARL ly' S' _ W' memF mdF a HARF (or_introl (ex_intro _ _ (ex_intro _ _ (conj Hinq Ha)))))). }
unfold ablocks in Hinq. apply in_map_iff in Hinq as ([pf nf] & Hpf & Hinbf). cbn [fst snd] in Hpf. injection Hpf as Hq Hn.
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia).
rewrite Hreqq in Hqce, NIMGQ.
exists pf, nf, (fun a => sptr_addr B ly' pf <= a < sptr_addr B ly' pf + req_size nf).
split; [right; exact Hinbf|]. split; [lia|]. split; [intros a Ha; rewrite Hq, Hn, Hreqq in Ha; split; [lia | exact (NIMGQ a Ha)]|].
split; [intros a Ha X; rewrite Hq, Hn, Hreqq in Ha; apply (NIMGQ a Ha); apply in_img_rw; unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in X; lia|].
apply (FREE ly' S' [] W' regsF memF mdF pf nf PREF Hinbf).
+ rewrite RF10, Hq. reflexivity.
+ rewrite (ts_code B HB), HraF. apply (ts_universe_drv B HB). cbn. tauto.
+ rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto. }
destruct FSITE as (pf & nf & Eb & Hpfin & Hnf & HEb & HEbso & FSITE).
eapply (SRrG_srealizes tfibsegs _ W' (cfg_at tfibsegs (pc_wrap_free (as_code B)) regsF memF mdF)); [exact FSITE | exact HAI6 |].
cbv beta. intros W4 c4 Hwle4 HAI7 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6). cbn [cfg_model] in HAI7.
unfold cfg_at. rewrite HraF.
pose proof HPOST6 as (HAR6 & Hlyle6 & Hwle6 & HP6 & Hio6 & Hfr6 & Hsc6).
destruct (atok_cf_apath _ _ _ tr6 _ (mlr_free_cf _ ML S' pf nf trc6 HWF' (proj2 (proj2 HROOMF))
ltac:(destruct Hpfin as [X|X]; [left; exact X | right; exact X]) (admits_fix _ _ _ (ts_universe B HB) Htrc6)) Hpath6) as (ns6 & HFP).
cbn [free_post_ycf snd] in HFP. destruct HFP as (HWF6 & _ & _ & Hfr6' & (l1 & l2 & Hcase & Hbl6) & HQT6). cbn [snd] in HWF6, Hbl6, Hfr6', HQT6.
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
pose proof (alc_layout _ _ ARL ly' S' _ W' memF mdF ly6 HARF Hlyle6) as (Habl6 & _ & _).
assert (EXT6 : forall b n, In (b, n) (blocks S') -> sptr_addr B ly6 b = sptr_addr B ly' b).
{ intros b n Hb. unfold ablocks in Habl6. pose proof (ext_in_map Habl6 (b, n) Hb) as X. cbn [fst snd] in X. injection X as X1. exact X1. }
(* the buffer survives the free of q: its entry is not (pf, nf), since nf < cap *)
assert (HBL6 : exists pb6, In (pb6, cap) (blocks S6) /\ sptr_addr B ly6 pb6 = buf).
{ unfold ablocks in Hinb. apply in_map_iff in Hinb as ([b0 n0] & Eb0 & HinS'). cbn [fst snd] in Eb0. injection Eb0 as Ea En. subst n0.
exists b0. split.
- rewrite Hbl6. destruct Hcase as [[_ E12] | E12].
+ rewrite E12. exact HinS'.
+ rewrite E12 in HinS'. apply in_app_or in HinS' as [X|[X|X]]; apply in_or_app; [left; exact X | | right; exact X].
exfalso. injection X as _ Xn. lia.
- rewrite (EXT6 b0 cap HinS'). exact Ea. }
destruct HBL6 as (pb6 & Hbl6S & Hpb6).
(* one free spent one level of the tail law's headroom *)
pose proof (RK_room S6 1 (room_after_free_cf B tfibsegs ly' S' [] W' memF mdF 1 pf trc6 tr6 S6 HARF HROOM2 Hpath6)) as HROOM6.
rewrite HshapeF, restrict_mkst_fx in HSF. fold regsF memF in HSF. rewrite <- restrict_mkst_fx, <- HshapeF in HSF.
pose proof (drv_after_call B HB ARL K_FQ E4 S_FQ msF ly' S' _ W' mdF Eb ly6 S6 W4 regs6 mem6 md6 rsFQ RA_FQ usp (-208)
HSF RVF CKF WFF NCF MAF submem_FQ F1r HPOST6 HARF HEb KPF E4_0 E4_6 HspF ltac:(lia) Ulo HCT ltac:(intros a Ha; apply HwinF; lia)) as HS7.
rewrite S_FQr_eq in HS7. set (E8 := havoc E4 K_FQ (map (getr regs6) CLOB)) in HS7.
assert (E8old : forall i, (i < K_FQ)%nat -> ew E8 i = ew E4 i) by (intros i Hi; subst E8; apply ew_havoc_old; exact Hi).
assert (E8_0 : bv_unsigned (ew E8 0) = usp) by (rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia); exact E4_0).
assert (E8_6 : usp <= bv_unsigned (ew E8 6)) by (rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia); exact E4_6).
assert (HSO6 : so_state (Datatypes.S j) (w_H W4) mem6).
{ apply (so_state_keep (Datatypes.S j) (w_H W') (w_H W4) memF mem6); [| exact HSOF]. intros a Ha. apply Hfr6.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- exact (so_not_owned ly' S' _ W' memF mdF a HARF Ha).
- exact (so_not_owned ly6 S6 _ W4 mem6 md6 a HAR6 Ha).
- unfold ascratch. rewrite HspF, (ts_errno B HB). unfold TFIB_ERRNO, ASTACK. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold sp_window_lo in Ulo. lia.
- intros X. exact (HEbso a X Ha).
- apply ds_off_low. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia. }
(* the RELRO bytes after the free: its post frame (its freed block lies off the image) *)
assert (HAD6 : arodata_ok_cf tfibsegs B mem6)
by exact (aro_site B HB ASTACK ly' S' [] W' regsF memF mdF Eb ly6 S6 W4 regs6 mem6 md6 usp RO HARF HPOST6
  (fun a Ha => proj2 (HEb a Ha)) HTOP' Ulo Uhi ltac:(rewrite HspF; lia) ltac:(unfold ASTACK; lia) HADF).
apply (SRr_srealizes tfibsegs W4 _ _ _ (xm_run E8 W4 regs6 mem6 md6 HS7) HAI7).
intros W5 c5 _ HAI8 (-> & msX & matX & -> & HSX & HFX & HFrX). cbn [cfg_model] in HAI8.
assert (HADX : arodata_ok_cf tfibsegs B (ms_mem msX))
by exact (aro_run B W4 E8 (WIN (-208) :: rsFQ) mem6 (ms_mem msX) RO HFrX WOKF ltac:(rewrite E8_0; exact Ulo) HAD6).
set (mdX := with_vm_backing (m_vm_lazy md6) matX md6) in *.
pose proof (st_ok_mem_ok tfibsegs E8 S_XM _ HSX) as HMX. cbn [restrict ms_mem] in HMX. rewrite (proj1 (proj2 rsFQ_eq)) in HMX.
assert (HwinX : forall a, usp - 65536 <= a < usp -> apresent (w_H W4) (ms_mem msX) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | left; reflexivity | exact E8_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | right; left; reflexivity | exact E8_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | right; right; left; reflexivity | exact E8_0 | lia | lia | cbn; lia]. }
assert (HARX : ARcf tfibsegs B ly6 S6 [] W4 (ms_mem msX) mdX).
{ apply (AR_after_run B HB ARL ly6 S6 _ W4 E8 (WIN (-208) :: rsFQ) mem6 (ms_mem msX) md6 matX HAR6 WOKF); [rewrite E8_0; exact Ulo | rewrite E8_0; exact HCT | exact HFX |].
rewrite E8_0. intros a Ha. exact (apresent_some' _ _ _ (HwinX a Ha)). }
assert (HSOX : so_state (Datatypes.S j) (w_H W4) (ms_mem msX)).
{ exact (so_state_frame (Datatypes.S j) (w_H W4) E8 (WIN (-208) :: rsFQ) _ _ HFrX SOKF ltac:(rewrite E8_0; exact Ulo) ltac:(rewrite E8_0; exact E8_6) HSO6). }
pose proof (xm_to_CM E8 W4 msX HSX) as (HSCM & V79 & ECold).
set (E9 := E_CM E8 (ms_regs msX)) in *.
rewrite Hr0. cbn [lib_iter]. apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (N - 1))) (ex 0 (ll_fs l)))); [| apply run_tail_eq].
replace (N - 1)%nat with (Datatypes.S j - 1)%nat by lia.
replace (ex 0 (ll_fs l)) with (ex (if count_mode data then 0 else 0) (ll_fs l)) by (destruct (count_mode data); reflexivity).
apply (MAINT E9 W4 msX mdX ly6 S6 data pb6 cap 0 (Datatypes.S j) (ll_fs l)).
+ intros i Hi. rewrite ECold by (unfold K_CM, K_M1 in *; lia). rewrite E8old by (unfold K_FQ, K_M1 in *; lia). rewrite E4old by (unfold K_VP, K_M1 in *; lia).
rewrite E2old by (unfold K_LR, K_M1 in *; lia). apply HEE. exact Hi.
+ change (ed E9 2) with (ed E 2). exact HEd.
+ exact Hlen.
+ rewrite ECold by (unfold K_CM, A_BUF, A_LEN, K_PP; lia). rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite Hpb6. exact E41.
+ exact V79.
+ left. reflexivity.
+ exact HSCM.
+ exact HAI8.
+ exact HARX.
+ exact (top_ok_le _ _ _ _ Hlyle6 HTOP').
+ exact Hbl6S.
+ exact (HQT6 HQT').
+ exact HROOM6.
+ apply HULL_NS. pose proof (YGcfXs.cfx_ipost_apath _ _ tr6 (tt, S6) (nsec_free_cf pf trc6 S') Hpath6) as N6.
cbv beta in N6. cbn [snd] in N6. lia.
+ exact HSOX.
+ intros fd. subst mdX. rewrite wvb_fds', Efds6. subst mdF. rewrite wvb_fds', HfdB, Hfdl. apply Hfdl0.
+ subst mdX. rewrite wvb_fs', Efs6. subst mdF. rewrite wvb_fs'. exact HfsB.
+ exact HADX.
-
assert (HSB' : st_ok tfibsegs E4 (add_cond S_BR cond_BRt) (restrict (w_H W') msB)).
{ apply (st_ok_add_cond tfibsegs E4 S_BR _ BC_NE (SOff 166 (-1)) (SLit 0) HSB). cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite E4_65. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 (Z.of_nat (Datatypes.S r) + -1)) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by lia. lia. }
apply (SRr_srealizes tfibsegs W' _ _ _ (l2_run E4 W' msB mdB HSB') HAI5).
intros W3 c3 _ HAI6 (-> & msL & matL & -> & HSL2 & HFL & HFrL). cbn [cfg_model] in HAI6.
set (mdL := with_vm_backing (m_vm_lazy mdB) matL mdB) in *.
pose proof (st_ok_mem_ok tfibsegs E4 S_L2 _ HSL2) as HML. cbn [restrict ms_mem] in HML.
assert (HwinL : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem msL) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HARL : ARcf tfibsegs B ly' S' [] W' (ms_mem msL) mdL).
{ apply (AR_after_run B HB ARL ly' S' _ W' E4 (ss_mem S_VP) (ms_mem msB) (ms_mem msL) mdB matL HARB WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFL |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinL a Ha)). }
destruct (between_step _ _ _ _ _ _ regs4 ly' S' W' (ms_mem msB) mdB (ms_mem msL) HLIB HHB HARB
  (lo_kept_frame E4 (ss_mem S_VP) W' (ms_mem msB) (ms_mem msL) HFrL WOKV GFV WFV ltac:(rewrite E4_0; lia))) as [HLIL HHL].
pose proof (stk_up_frame E4 (ss_mem S_VP) ly' W' (ms_mem msB) (ms_mem msL) HFrL WOKV E4_0 HTOP' HUPB) as HUPL.
assert (HSOL : so_state (Datatypes.S j) (w_H W') (ms_mem msL)).
{ exact (so_state_frame (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrL SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSOB). }
assert (HROL : arodata_ok B (aview tfibsegs (w_H W') (ms_mem msL))).
{ exact (arodata_frame (w_H W') E4 (ss_mem S_VP) _ _ HFrL WOKV ltac:(rewrite E4_0; exact Ulo) HROB). }
assert (HADL : arodata_ok_cf tfibsegs B (ms_mem msL))
by exact (aro_run B W' E4 (ss_mem S_VP) (ms_mem msB) (ms_mem msL) RO HFrL WOKV ltac:(rewrite E4_0; exact Ulo) HADB).
pose proof (l2_to_L E4 W' msL (Z.of_nat (Datatypes.S r)) HSL2 E4_65 ltac:(lia)) as (HSLn & V65n & ELold).
set (E6n := E_L2 E4 (ms_regs msL)) in *.
apply (IH (Datatypes.S j) E6n W' msL mdL ly' S' data buf cap q (ll_fs l) N Hlk Hok).
+ intros i Hi. rewrite ELold by (unfold K_M1 in Hi; lia). rewrite E4old by (unfold K_VP, K_M1 in *; lia). rewrite E2old by (unfold K_LR, K_M1 in *; lia). apply HEE. exact Hi.
+ change (ed E6n 2) with (ed E 2). exact HEd.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E41.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E61.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E62.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E63.
+ rewrite V65n. lia.
+ exact HSLn.
+ lia.
+ lia.
+ lia.
+ exact HZQ.
+ exact HHL.
+ intros Hp. pose proof (Hinq' Hp) as Hinq.
pose proof (alc_blocks _ _ ARL ly' S' _ W' mem' md' _ _ HAR' Hinq) as (_ & Hq4096 & Hqce & _).
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia). rewrite Hreqq in Hqce.
apply (blk_of_frame_r _ E4 (ss_mem S_VP) _ _ q (payload_len data) (payload data) usp HFrL WOKV E4_0 Ulo); [| lia | lia | exact (HPLB Hp)].
intros a Ha. assert (Ha' : q <= a < q + req_size (payload_len data)) by (rewrite Hreqq; exact Ha).
exact (proj2 (alc_client_img _ _ ARL ly' S' _ W' mem' md' a HAR' (or_introl (ex_intro _ q (ex_intro _ (payload_len data) (conj Hinq Ha')))))).
+ exact Hfrs.
+ exact HQT'.
+ exact HAI6.
+ exact HARL.
+ exact HTOP'.
+ exact Hcap.
+ exact HLc.
+ exact Hlen.
+ exact HNP'.
+ rewrite Nat2Z.inj_succ. lia.
+ exact HLIL.
+ exact HUPL.
+ exact HSOL.
+ exact HROL.
+ exact (finv_run B ly' S' _ W' (ms_mem msB) mdB (w_H W') E4 (ss_mem S_VP) _ _ usp HARB HFrL WOKV E4_0 Ulo Uhi HTOP' HFIB).
+ split; [intros fd; subst mdL; rewrite wvb_fds', HfdB, Hfdl; apply Hfdl0|]. split; [subst mdL; rewrite wvb_fds', HfdB; exact Hnames'|].
split; [subst mdL; rewrite wvb_fs'; exact HfsB | exact Hsorted].
+ exact HADL.
Qed.
(* the loop at its first call, as AD1wcf.loop_L_x states it (j = 0) *)
Theorem tfib_loop_L_at : forall E (W : world tfibsegs) ms md ly S Hp data (pb pq : sptr) (cap q : Z) (j r : nat) (fs : Fs),
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew EL k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
bv_unsigned (ew E 161) = sptr_addr B ly pb + 2 + config_len data ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok tfibsegs E S_LF (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = calls data)%nat -> j = 0%nat ->
((payload_len data = 0 /\ q = 0 /\ blocks S = [(pb, cap)])
\/ (0 < payload_len data /\ blocks S = [(pb, cap); (pq, payload_len data)] /\ sptr_addr B ly pq = q)) ->
(0 < payload_len data -> blk (w_H W) (ms_mem ms) q (payload_len data) (payload data)) ->
frames S = [] -> qtight S ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp W (ms_mem ms) md -> Hp = [] -> top_ok usp ly ->
NP S -> fr_hblks W (ms_mem ms) = [] -> NS S + 4 * XNMAX <= NRUN -> fr_capout_ok W (ms_mem ms) -> fr_LI B 0 ly S W (ms_mem ms) ->
rom_view tfibsegs W (ms_mem ms) ->
stk_up usp ly W (ms_mem ms) ->
65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
((j = 0%nat /\ stdout_img (w_H W) (ms_mem ms)) \/ ((1 <= j)%nat /\ xst j (w_H W) (ms_mem ms))) ->
arodata_ok B (aview tfibsegs (w_H W) (ms_mem ms)) ->
FINV ly (w_H W) (ms_mem ms) -> MDI md fs ->
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (loop_tgt (payload data) (calls data) j r fs).
Proof.
intros E W ms md ly S Hp data pb pq cap q j r fs Hlk Hok HEE HEd E41 E42 E60 E61 E62 E63 E65 HS Hr Hjr Hj0 HBL HPL Hfr HQT HAI HAR HHp HTOP
  HNP Hhb HNS Hcap0 HLI _ HUP Hcap HLc HSO HRO HFI HMD HAD.
subst Hp j. pose proof (calls_bound data) as Hcb. pose proof (config_len_bound data) as Hcl.
apply (calls_loop r 0 E W ms md ly S data (sptr_addr B ly pb) cap q fs (calls data) Hlk Hok HEE HEd E41 E61 E62 E63 E65 HS Hr Hjr ltac:(lia)).
- intros Hz. destruct HBL as [(_ & Hq & _) | (Hp & _)]; [exact Hq | lia].
- apply (H_init B pb pq (sptr_addr B ly pb) cap q (payload_len data) ly S W (ms_mem ms) eq_refl Hhb Hcap0).
  + (* XCNT at the first call: fr_LI names the relay and g_out, and the driver holds buf (and q) only *)
    pose proof (proj2 HLI) as (_ & _ & HRA & HAO & _).
    apply (fr_xcnt_init B ly S W (ms_mem ms) _ HRA HAO).
    destruct HBL as [(_ & _ & Hbl) | (_ & Hbl & _)]; rewrite Hbl; cbn [length]; lia.
  + destruct HBL as [(Hz & Hq & Hbl) | (Hp & Hbl & Hpq)]; [left | right]; repeat split; assumption.
- exact HPL.
- exact Hfr.
- exact HQT.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact Hcap.
- exact HLc.
- unfold dlen in Hok. lia.
- exact HNP.
- lia.
- exact HLI.
- exact HUP.
- exact HSO.
- exact HRO.
- exact HFI.
- exact HMD.
- exact HAD.
Qed.
End g.
Theorem tfib_loop_L (B : asyms) (HB : TfibSyms B) (ARL : AR_laws_cf tfibsegs B) (ML : model_laws_cf (as_universe B))
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (NP : astate -> Prop) (NPT : iface_room_np_tail NP)
(NS : astate -> Z) (NRUN XNMAX : Z) (XNMAX_NN : 0 <= XNMAX) (HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S)
(nsec_free_cf : forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s)) (RO : relro_ok)
(R : world tfibsegs -> world tfibsegs -> Prop)
(LIB : lib_site_cf B NP NS NRUN XNMAX R) (PF1 : printf_first_tfa B xst) (PFN : printf_next_tfa B xst)
(FREE : free_site_tfa B R) (FREEN : free_null_site_tfa B R) (XFR : xst_frame_tfa xst)
(MAINT : forall sp inp xw xd a0 p, valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> main_tail_cf B xst sp inp xw xd a0 p) :
loop_L_x B NP NS NRUN XNMAX xst.
Proof.
intros sp inp xw xd E W ms md ly S Hp a0 p data pb pq cap q j r fs Hargv Hsp Hva Hve Hvfs.
exact (tfib_loop_L_at B HB ARL ML xst NP NPT NS NRUN XNMAX XNMAX_NN HULL_NS nsec_free_cf RO R LIB PF1 PFN FREE FREEN XFR sp inp xw xd a0 p Hsp Hva Hve
  (MAINT sp inp xw xd a0 p Hsp Hva Hve)
  E W ms md ly S Hp data pb pq cap q j r fs).
Qed.
End e.
