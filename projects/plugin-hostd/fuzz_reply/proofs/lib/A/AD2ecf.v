(* copied from cgif_file lib/A/AD2e.v by rules r1,r2,r3,r6,rC, generator ed5c0821ce98f1d99fcd7466c0aa65f7671a8daf838ab8f2b2da9f5038f22ee4 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2e.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: over the cf allocator (ARcf) and tail_at's NP: the payload malloc takes drv_pre's
   ROOM_cf from NP and room_cf from drv_minv (drv_minv_room), its frame names the error-message buffer (A/AD26cf.v
   malloc_E_place); the first call of the loop enters A/AD1wcf.v's loop_L_x on the clipped view (A/AD2e_fp.v pl_to_LF)
   with NP back from the malloc (np_after_malloc_cf), the interface's call-0 invariant (A/AD1w_cf_inv.v
   fr_lib_inv_init_ok from A/AD2e_fp.v PL_gf_start), the read-only view (A/AD1r_fp.v rom_view_of_arodata), no
   harness block yet (A/AFrInit_fp.v fr_hblks_init) and the run count's room for the loop's at most 4 calls
   (KF-COUNT #7: the payload malloc adds at most 1 to the prefix's count, nsec_malloc_cf, and NS_START at init_state
   pays the prefix and the 4 calls). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1vcf AD1ycf AD26cf AD24cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AD2acf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD21 AD25cf AD23cf AD2h AD1wcf AD2f AD2bcf AD2gcf AD1s AD2ccf AD2dcf AD29cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition rsPM : smem := Eval vm_compute in rs_PM true 1.
Lemma rs_PM_eq : forall c0 k, rs_PM c0 k = rsPM.
Proof. intros c0 k. destruct c0; vm_compute; reflexivity. Qed.
Lemma S_PMr_eq : drv_after sPM0 (rs_PM true 1) K_PM RA_PM (-208) = S_PMr0 /\ forall k, drv_after (sPM1 k) (rs_PM false k) K_PM RA_PM (-208) = S_PMr1 k.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Lemma S_PF_eq : run_lp (add_cond S_PMr0 (cNULL A_PBLK)) = S_PF0 /\ forall k, run_lp (add_cond (S_PMr1 k) (cNULL A_PBLK)) = S_PF1 k.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Lemma S_PC_eq : run_lp (add_cond S_PMr0 (cPTR A_PBLK)) = S_PC0 /\ forall k, run_lp (add_cond (S_PMr1 k) (cPTR A_PBLK)) = S_PC1 k.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Lemma mem_PMr : ss_mem S_PMr0 = WIN (-208) :: rsPM /\ (forall k, ss_mem (S_PMr1 k) = WIN (-208) :: rsPM)
/\ ss_mem S_PF0 = WIN (-208) :: rsPM /\ (forall k, ss_mem (S_PF1 k) = WIN (-208) :: rsPM)
/\ ss_mem S_PC0 = WIN (-208) :: rsPM /\ (forall k, ss_mem (S_PC1 k) = WIN (-208) :: rsPM).
Proof. repeat split; intros; vm_compute; reflexivity. Qed.
Definition K_PC : nat := 196.
Definition A_PC_RET : Z := RA_PC.
Definition S_PCr0 : sstate := Eval vm_compute in mkSS A_PC_RET (sr_sets (ss_regs S_PC0) (junk_upd K_PC CLOB)) (ss_mem S_PC0) None (ss_facts S_PC0).
Definition S_PCr1 (k : Z) : sstate := Eval vm_compute in mkSS A_PC_RET (sr_sets (ss_regs (S_PC1 k)) (junk_upd K_PC CLOB)) (ss_mem (S_PC1 k)) None (ss_facts (S_PC1 k)).
Definition S_PL0 : sstate := Eval vm_compute in run_lp S_PCr0.
Definition S_PL1 (k : Z) : sstate := Eval vm_compute in run_lp (S_PCr1 k).
Lemma S_PL_eq : run_lp S_PCr0 = S_PL0 /\ forall k, run_lp (S_PCr1 k) = S_PL1 k.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Definition rsPL : smem := Eval vm_compute in tl (ss_mem S_PL0).
Lemma mem_PL : ss_mem S_PCr0 = WIN (-208) :: rsPM /\ (forall k, ss_mem (S_PCr1 k) = WIN (-208) :: rsPM)
/\ ss_mem S_PL0 = WIN (-208) :: rsPL /\ (forall k, ss_mem (S_PL1 k) = WIN (-208) :: rsPL)
/\ ss_pc S_PL0 = A_LLVMF /\ (forall k, ss_pc (S_PL1 k) = A_LLVMF).
Proof. repeat split; intros; vm_compute; reflexivity. Qed.
Lemma pc_checks : ss_atoms_lt K_PC S_PC0 = true /\ (forall k, ss_atoms_lt K_PC (S_PC1 k) = true)
/\ regions_wf (WIN (-208) :: rsPM) = true /\ mem_atoms_lt K_PC (WIN (-208) :: rsPM) = true /\ mem_atoms_lt K_PM (WIN (-208) :: rsPM) = true
/\ forallb drv_win_ok (WIN (-208) :: rsPM) = true /\ forallb so_win_ok (WIN (-208) :: rsPM) = false.
Proof. vm_compute. repeat split; intros; reflexivity. Qed.
Lemma reabs_chk_PL : reabs_check LT162 S_PL0 L_regs L_facts = true /\ forall k, reabs_check LT162 (S_PL1 k) L_regs L_facts = true.
Proof. split; [| intros k]; vm_compute; reflexivity. Qed.
Lemma S_PL_regs : sr_get (ss_regs S_PL0) 8%bv = sv_pl00 /\ (forall k, sr_get (ss_regs (S_PL1 k)) 8%bv = sv_pl00)
/\ sr_get (ss_regs S_PL0) 9%bv = SOff A_PBLK 0 /\ (forall k, sr_get (ss_regs (S_PL1 k)) 9%bv = SOff A_PBLK 0)
/\ sr_get (ss_regs S_PL0) 10%bv = SOff A_PBLK 0 /\ (forall k, sr_get (ss_regs (S_PL1 k)) 10%bv = SOff A_PBLK 0)
/\ sr_get (ss_regs S_PL0) 11%bv = add0 sv_pl00 /\ (forall k, sr_get (ss_regs (S_PL1 k)) 11%bv = add0 sv_pl00)
/\ sr_get (ss_regs S_PL0) 18%bv = SOff A_PBLK 0 /\ (forall k, sr_get (ss_regs (S_PL1 k)) 18%bv = SOff A_PBLK 0)
/\ sr_get (ss_regs S_PL0) 21%bv = SLit 1 /\ (forall k, sr_get (ss_regs (S_PL1 k)) 21%bv = SLit k)
/\ ss_resv S_PL0 = None /\ (forall k, ss_resv (S_PL1 k) = None).
Proof. repeat split; intros; vm_compute; reflexivity. Qed.
Definition PM_tailL : list smem := Eval vm_compute in firstn 59 (skipn 1 L_piecesC).
Definition PM_tailCM : list smem := Eval vm_compute in (map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_B).
Definition PM_piecesL : list smem := [WIN208] :: [TRF] :: PM_tailL.
Definition PM_piecesCM : list smem := [WIN208] :: [TRF0] :: PM_tailCM.
Lemma PM_pieces_eq : concat PM_piecesL = L_mem /\ concat PM_piecesCM = CM_mem /\ length PM_piecesL = 61%nat /\ length (WIN (-208) :: rsPM) = 61%nat
/\ length PM_piecesCM = 61%nat /\ length (WIN (-208) :: rsPL) = 61%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition TRFc3 : YP09.region := Eval vm_compute in TRF.
Lemma rsPM_split : rsPM = TRFc3 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_B. Proof. vm_compute. reflexivity. Qed.
Lemma rsPL_split : rsPL = TRFc3 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_E. Proof. vm_compute. reflexivity. Qed.
Lemma PM_tailL_unfold : PM_tailL = map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_E.
Proof. vm_compute. reflexivity. Qed.
Lemma PM_tailCM_unfold : PM_tailCM = map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_B.
Proof. vm_compute. reflexivity. Qed.
Lemma PM_if : forall (c0 : bool) k,
ss_pc (if c0 then sPM0 else sPM1 k) = A_wrap_malloc /\ ss_resv (if c0 then sPM0 else sPM1 k) = None /\ ss_atoms_lt K_PM (if c0 then sPM0 else sPM1 k) = true
/\ drv_after (if c0 then sPM0 else sPM1 k) rsPM K_PM RA_PM (-208) = (if c0 then S_PMr0 else S_PMr1 k).
Proof. intros c0 k. destruct c0; vm_compute; repeat split; reflexivity. Qed.
Lemma PMr_if : forall (c0 : bool) k, ss_mem (if c0 then S_PMr0 else S_PMr1 k) = WIN (-208) :: rsPM.
Proof. intros c0 k. destruct c0; vm_compute; reflexivity. Qed.
Lemma PF_if : forall (c0 : bool) k,
ss_mem (if c0 then S_PF0 else S_PF1 k) = WIN (-208) :: rsPM /\ ss_pc (if c0 then S_PF0 else S_PF1 k) = A_CM /\ ss_resv (if c0 then S_PF0 else S_PF1 k) = None
/\ run_lp (add_cond (if c0 then S_PMr0 else S_PMr1 k) (cNULL A_PBLK)) = (if c0 then S_PF0 else S_PF1 k)
/\ reabs_check LT180 (if c0 then S_PF0 else S_PF1 k) CM_regs CM_facts = true.
Proof. intros c0 k. destruct c0; vm_compute; repeat split; reflexivity. Qed.
Lemma PC_if : forall (c0 : bool) k,
ss_mem (if c0 then S_PC0 else S_PC1 k) = WIN (-208) :: rsPM /\ ss_pc (if c0 then S_PC0 else S_PC1 k) = A_icpt_memcpy /\ ss_resv (if c0 then S_PC0 else S_PC1 k) = None
/\ run_lp (add_cond (if c0 then S_PMr0 else S_PMr1 k) (cPTR A_PBLK)) = (if c0 then S_PC0 else S_PC1 k)
/\ ss_atoms_lt K_PC (if c0 then S_PC0 else S_PC1 k) = true
/\ (if c0 then S_PCr0 else S_PCr1 k) = mkSS A_PC_RET (sr_sets (ss_regs (if c0 then S_PC0 else S_PC1 k)) ([] ++ junk_upd K_PC CLOB)) (ss_mem (if c0 then S_PC0 else S_PC1 k)) None (ss_facts (if c0 then S_PC0 else S_PC1 k)).
Proof. intros c0 k. destruct c0; vm_compute; repeat split; reflexivity. Qed.
Lemma PL_if : forall (c0 : bool) k,
ss_mem (if c0 then S_PL0 else S_PL1 k) = WIN (-208) :: rsPL /\ ss_pc (if c0 then S_PL0 else S_PL1 k) = A_LLVMF /\ ss_resv (if c0 then S_PL0 else S_PL1 k) = None
/\ run_lp (if c0 then S_PCr0 else S_PCr1 k) = (if c0 then S_PL0 else S_PL1 k)
/\ reabs_check LT162 (if c0 then S_PL0 else S_PL1 k) L_regs L_facts = true
/\ ss_mem (if c0 then S_PCr0 else S_PCr1 k) = WIN (-208) :: rsPM.
Proof. intros c0 k. destruct c0; vm_compute; repeat split; reflexivity. Qed.
Lemma rsPM_checks : regions_wf (WIN (-208) :: rsPM) = true /\ regions_wf rsPM = true /\ no_cdata rsPM = true
/\ mem_atoms_lt K_PM (WIN (-208) :: rsPM) = true /\ mem_atoms_lt K_PC (WIN (-208) :: rsPM) = true
/\ forallb (drv_keep_ok (-208)) rsPM = true /\ forallb drv_win_ok (WIN (-208) :: rsPM) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rsPL_checks : regions_wf (WIN (-208) :: rsPL) = true /\ mem_atoms_lt K_PC (WIN (-208) :: rsPL) = true /\ forallb drv_win_ok (WIN (-208) :: rsPL) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k AD1ucf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG01cf YG07cf YG0dcf YG0ncf YG0ucf YGcfNames YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre YGcfPath.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1npcf AD2d_fp AD2e_fp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AD1w_cf AFrInit_fp AD1w_cf_inv AD1r_fp W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcallcf.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

#[local] Ltac sub_piece Hr :=
eapply region_ok_sub; [| cbn; lia | exact Hr]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|];
split; [cbn; first [left; lia | right; lia] | intros c Hc; cbn in Hc |- *; tauto].
Lemma refines_PM_tailL : forall E3 (m : word -> option byte), refines E3 m (firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_E) PM_tailL.
Proof.
intros E3 m. rewrite PM_tailL_unfold. apply refines_app; [apply refines_single|].
apply refines_map. intros r Hr. pose proof (proj1 (forallb_forall _ _) IMG_E_lohi r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply flat_map_pieces_ok; [apply clip_out_ok; [unfold STDOUT_LO, STDOUT_HI; lia | exact Hlh] |].
intros q _ Hq. apply clip_out_ok; [unfold SOBUF_LO, SOBUF_HI; lia | exact Hq].
Qed.
Lemma refines_PM_tailCM : forall E3 (m : word -> option byte), refines E3 m (firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_B) PM_tailCM.
Proof.
intros E3 m. rewrite PM_tailCM_unfold. apply refines_app; [apply refines_single|].
apply refines_map. intros r Hr. pose proof (proj1 (forallb_forall _ _) IMG_B_lohi r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply flat_map_pieces_ok; [apply clip_out_ok; [unfold STDOUT_LO, STDOUT_HI; lia | exact Hlh] |].
intros q _ Hq. apply clip_out_ok; [unfold SOBUF_LO, SOBUF_HI; lia | exact Hq].
Qed.
Lemma refines_PM_L : forall E3 (m : word -> option byte), refines E3 m (WIN (-208) :: rsPL) PM_piecesL.
Proof.
intros E3 m. rewrite rsPL_split. unfold PM_piecesL.
apply refines_cons; [intros Hr; constructor; [exact Hr | constructor] | constructor; [apply ext_in_refl | constructor] | cbn; split; exact I |].
apply refines_cons; [intros Hr; constructor; [sub_piece Hr | constructor] | constructor; [unfold ext_in; cbn; repeat split; first [reflexivity | lia] | constructor] | cbn; split; exact I |].
apply refines_PM_tailL.
Qed.
Lemma refines_PM_CM : forall E3 (m : word -> option byte), refines E3 m (WIN (-208) :: rsPM) PM_piecesCM.
Proof.
intros E3 m. rewrite rsPM_split. unfold PM_piecesCM.
apply refines_cons; [intros Hr; constructor; [exact Hr | constructor] | constructor; [apply ext_in_refl | constructor] | cbn; split; exact I |].
apply refines_cons; [intros Hr; constructor; [sub_piece Hr | constructor] | constructor; [unfold ext_in; cbn; repeat split; first [reflexivity | lia] | constructor] | cbn; split; exact I |].
apply refines_PM_tailCM.
Qed.
(* the payload malloc's room: drv_minv leaves every primary class but kBatchClass pristine, and room_at has the
   kBatchClass disjunct (YGcfPath.v) *)
Lemma drv_minv_room : forall U S cap dl n, Wf_cf U S -> drv_minv S cap dl -> 0 <= n < 2 ^ 32 -> room_cf n S.
Proof.
intros U S cap dl n HW (Hcs & _) Hn. pose proof HW as W0. unfold Wf_cf in W0.
destruct (from_primary n) eqn:Fp; [| left; exact Fp].
destruct (Z.eq_dec (chunk_class n) kBatchClass) as [Hb | Hb]; [right; unfold room_at; left; exact Hb|].
pose proof (YG0a.primary_geometry n ltac:(lia) Fp) as (Gc & _).
assert (HPc : pristine_class S (chunk_class n)).
{ destruct Hcs as [[_ HP] | [_ HP]]; apply HP; try lia; [intros [] | intros [H | []]; exact (Hb (eq_sym H))]. }
apply (room_cf_of_fit _ _ _ _ n S W0). destruct HPc as (Hm & _). rewrite Hm. unfold kUserMapSize, kFreeArrayOffset. lia.
Qed.
Section e.
Variable B : asyms.
(* the cf allocator's non-primary room (A/AD1w_cf.v) *)
Variable NP : astate -> Prop.
Hypothesis NPT : AD1w_cf.iface_room_np_tail NP.
Hypothesis NPS : AD1w_cf.iface_room_np_step NP.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.
Hypothesis ML : model_laws_cf (as_universe B).
Hypothesis MSITE : malloc_site_tfa B.
Hypothesis MCPY : memcpy_site_tfa B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis EXITL : exit_leaf_tfa B xst.
Hypothesis XFR : xst_frame_tfa xst.
(* the run count, its run bound and its per-call step bound (A/AD1mcf.v); the payload malloc's step, at the text of
   A/CfRBridgeRules.v nsec_malloc_cf with NS for nsec_cf; and the count's room at the start state init_state for the
   driver's mallocs before the loop's first call and the loop's at most 4 calls (A/AD2dcf.v NS_START, whose comment
   names the mallocs) *)
Variables (NS : astate -> Z) (NRUN XNMAX : Z).
Hypothesis nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)).
Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
(* field round 3: the hull admission at the payload malloc (drv_pre's cf_hull_ok conjunct) from the run count's bound
   (A/AD1pcf.v HULL_NS): the count there is at most ns_pre cap <= 11 above init_state, inside NS_START's room once
   0 <= XNMAX (A/AD1pcf.v has it from XN_BND at n = 0) *)
Hypothesis XNMAX_NN : 0 <= XNMAX.
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
Hypothesis LOOPL : loop_L_x B NP NS NRUN XNMAX xst.
(* field round 3 (Part A): the image fact behind the RELRO bytes' keep (A/AD1vcf.v relro_ok) *)
Hypothesis RO : relro_ok.
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
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YP08.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma PM_img_facts : forall E (H : word -> bool) m,
mem_ok tfibsegs E (mrestrict H m) (WIN (-208) :: rsPM) ->
stdout_img H m /\ arodata_ok B (aview tfibsegs H m).
Proof.
intros E H m HM. apply (img_facts_of B HB IMG_B E H m _ IMG_CELLS_eq HM).
intros r Hr. right. rewrite rsPM_split. right. apply in_app_iff. right. exact Hr.
Qed.
Lemma PL_img_facts : forall E (H : word -> bool) m,
mem_ok tfibsegs E (mrestrict H m) (WIN (-208) :: rsPL) ->
stdout_img H m /\ arodata_ok B (aview tfibsegs H m).
Proof.
intros E H m HM. apply (img_facts_of B HB IMG_E E H m _ IMG_CELLS_eqE HM).
intros r Hr. right. rewrite rsPL_split. right. apply in_app_iff. right. exact Hr.
Qed.
Lemma submem_prefix : forall l1 l2, submem l1 (l1 ++ l2).
Proof. induction l1 as [|r l1 IH]; intros l2; cbn; [constructor|]. apply submem_keep; [repeat split; try lia; auto | apply IH]. Qed.
Lemma rs_PM_sub : forall (c0 : bool) k, submem (rs_PM c0 k) (ss_mem (if c0 then sPM0 else sPM1 k)).
Proof.
intros c0 k. rewrite rs_PM_eq.
pose proof sPM0_facts as (_ & _ & _ & _ & _ & _ & _ & _ & M0). pose proof (sPM1_facts k) as (_ & _ & _ & _ & _ & _ & _ & _ & M1).
assert (HM : ss_mem (if c0 then sPM0 else sPM1 k) = if c0 then ss_mem sB0 else ss_mem sB1) by (destruct c0; [exact M0 | exact M1]).
rewrite HM. destruct c0; (lazymatch goal with |- submem _ ?m => let v := eval vm_compute in m in change m with v end); unfold rsPM;
(lazymatch goal with |- submem (_ :: ?l) (_ :: ?m) => let l2 := eval vm_compute in (skipn 59 m) in change m with (l ++ l2) end);
(apply submem_keep; [| apply submem_prefix]);
(split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|]; split; [cbn; right; lia | intros c Hc; cbn in Hc |- *; tauto]).
Qed.
Lemma pf_run : forall (c0 : bool) k E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E (add_cond (if c0 then S_PMr0 else S_PMr1 k) (cNULL A_PBLK)) (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_PM) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_PM) mem (seg_rom tfibsegs)) md)
(at_st (if c0 then S_PMr0 else S_PMr1 k) (if c0 then S_PF0 else S_PF1 k) E W mem md).
Proof.
intros c0 k E W regs mem md HS. pose proof HWXi as HWX. pose proof S_PF_eq as [Q0 Q1].
destruct c0; [rewrite <- Q0 | rewrite <- (Q1 k)]; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Lemma pc_run : forall (c0 : bool) k E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E (add_cond (if c0 then S_PMr0 else S_PMr1 k) (cPTR A_PBLK)) (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_PM) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_PM) mem (seg_rom tfibsegs)) md)
(at_st (if c0 then S_PMr0 else S_PMr1 k) (if c0 then S_PC0 else S_PC1 k) E W mem md).
Proof.
intros c0 k E W regs mem md HS. pose proof HWXi as HWX. pose proof S_PC_eq as [Q0 Q1].
destruct c0; [rewrite <- Q0 | rewrite <- (Q1 k)]; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Lemma pl_run : forall (c0 : bool) k E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E (if c0 then S_PCr0 else S_PCr1 k) (restrict (w_H W) (mkst regs (Z_to_bv 64 A_PC_RET) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_PC_RET) mem (seg_rom tfibsegs)) md)
(at_st (if c0 then S_PCr0 else S_PCr1 k) (if c0 then S_PL0 else S_PL1 k) E W mem md).
Proof.
intros c0 k E W regs mem md HS. pose proof HWXi as HWX. pose proof S_PL_eq as [Q0 Q1].
destruct c0; [rewrite <- Q0 | rewrite <- (Q1 k)]; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Lemma pf_to_CM : forall (c0 : bool) (k : Z) E2 (W : world tfibsegs) ms,
st_ok tfibsegs E2 (if c0 then S_PF0 else S_PF1 k) (restrict (w_H W) ms) ->
let E' := E_CM E2 (ms_regs ms) in
st_ok tfibsegs E' S_CM (restrict (w_H W) ms) /\ bv_unsigned (ew E' 180) = 2 /\ (forall j, (j < K_CM)%nat -> ew E' j = ew E2 j).
Proof.
intros c0 k E2 W ms HS E'.
set (ss := if c0 then S_PF0 else S_PF1 k) in *. set (regs := ms_regs ms) in *.
pose proof (PF_if c0 k) as (MPF & PCF & RVF & _ & CHK). fold ss in MPF, PCF, RVF, CHK.
assert (R10 : getr regs 10%bv = w64 2).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 ss ms 10%bv HS). subst ss. destruct c0; vm_compute; reflexivity. }
assert (NEW : forall i r, (i < 16)%nat -> nth i CM_srcs 0%bv = r -> ew E' (K_CM + i) = getr regs r).
{ intros i r Hi <-. subst E'. unfold E_CM. rewrite (ew_havoc_new E2 K_CM _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < K_CM)%nat -> ew E' j = ew E2 j) by (intros j Hj; subst E'; unfold E_CM; apply ew_havoc_old; exact Hj).
assert (V79 : bv_unsigned (ew E' 180) = 2).
{ change 180%nat with (K_CM + 0)%nat. rewrite (NEW 0%nat 10%bv) by (cbn; first [lia | reflexivity]). rewrite R10. apply u64_lit. lia. }
split; [| split; [exact V79 | exact Eold]].
pose proof (st_ok_mem_ok tfibsegs E2 ss _ HS) as HM0. cbn [restrict ms_mem] in HM0. rewrite MPF in HM0.
assert (HM1 : mem_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms)) CM_mem).
{ rewrite <- (proj1 (proj2 PM_pieces_eq)). apply (mem_ok_refine E2 _ (WIN (-208) :: rsPM)); [exact HM0 | apply refines_PM_CM |].
rewrite (proj1 (proj2 PM_pieces_eq)). exact (proj1 CM_mem_wf). }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) CM_mem).
{ apply (mem_ok_agree tfibsegs K_CM E2); [| exact (proj1 (proj2 CM_mem_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_CM. rewrite <- PCF.
apply (st_ok_reabs tfibsegs LT180 E2 E' ss (restrict (w_H W) ms) CM_regs CM_mem CM_facts HS).
- split; [| intros d _; subst E'; reflexivity]. intros j Hj. unfold LT180 in Hj. apply Nat.ltb_lt in Hj. exact (Eold j Hj).
- exact CHK.
- cbn [ms_regs restrict]. fold regs.
apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
Ltac oneC NEW i := rewrite <- (NEW i); [apply f_equal; reflexivity | cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ oneC NEW 0%nat | oneC NEW 2%nat | oneC NEW 3%nat | oneC NEW 4%nat | oneC NEW 5%nat | oneC NEW 6%nat | oneC NEW 7%nat
| oneC NEW 8%nat | oneC NEW 9%nat | oneC NEW 10%nat | oneC NEW 11%nat | oneC NEW 12%nat | oneC NEW 13%nat | oneC NEW 14%nat
| oneC NEW 15%nat ] |]).
destruct Hin.
- rewrite CM_fact_obls_eq. constructor; [| constructor].
unfold afact_ok; cbn [af_lo af_hi af_al2 fst snd fact_v]. rewrite V79. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. repeat split; try reflexivity; lia.
- exact HM2.
Qed.
Lemma pc_reseat : forall (c0 : bool) k E2 (W' : world tfibsegs) regs3 (pc3 : word) mem3 regs4 mem4 (nb ncp : Z),
st_ok tfibsegs E2 (if c0 then S_PC0 else S_PC1 k) (mkst regs3 pc3 (mrestrict (w_H W') mem3) (seg_rom tfibsegs)) ->
bv_unsigned (ew E2 0) = usp -> usp <= bv_unsigned (ew E2 6) ->
aregs_preserved regs3 regs4 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (nb <= a < nb + ncp) -> ~ (usp - 208 - ESTACK <= a < usp - 208) -> aview tfibsegs (w_H W') mem4 a = aview tfibsegs (w_H W') mem3 a) ->
(forall a, apresent (w_H W') mem3 a -> apresent (w_H W') mem4 a) ->
(forall a, nb <= a < nb + ncp -> ~ in_img tfibsegs a) -> nb + ncp <= alloc_ceiling -> YM05.ceil_of_top (usp - stack_max_size) ->
(forall a, usp - 65536 <= a < usp - 208 -> apresent (w_H W') mem3 a) ->
st_ok tfibsegs (havoc E2 K_PC (map (getr regs4) CLOB)) (if c0 then S_PCr0 else S_PCr1 k)
(mkst regs4 (Z_to_bv 64 A_PC_RET) (mrestrict (w_H W') mem4) (seg_rom tfibsegs)).
Proof.
intros c0 k E2 W' regs3 pc3 mem3 regs4 mem4 nb ncp HS E2_0 E2_6 HP Hfr Hpres NIMG Hnb HCT Hwin.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (PC_if c0 k) as (MPC & _ & _ & _ & ATC & EQr). pose proof rsPM_checks as (WF1 & WF2 & _ & _ & MAT & KEEP & _).
set (ss := if c0 then S_PC0 else S_PC1 k) in *.
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (nb <= a < nb + ncp) -> ~ (usp - 208 - ESTACK <= a < usp - 208) ->
mbyte tfibsegs (mrestrict (w_H W') mem4) a = mbyte tfibsegs (mrestrict (w_H W') mem3) a).
{ intros a H0 H1 H2. apply (mbyte_of_aview tfibsegs). apply Hfr; assumption. }
pose proof (st_ok_mem_ok tfibsegs E2 ss _ HS) as HM. cbn [ms_mem] in HM. rewrite MPC in HM. destruct HM as (Hwf & Hok & Hpd).
assert (GOAL : mem_ok tfibsegs E2 (mrestrict (w_H W') mem4) (WIN (-208) :: rsPM)).
{ split; [exact Hwf|]. split; [| exact Hpd].
pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
constructor.
+ apply (region_ok_transport_chunks E2 (mrestrict (w_H W') mem3) (mrestrict (w_H W') mem4)); [exact Hr0 | intros c i Hc; destruct Hc |].
cbn [r_wlo r_whi r_base base_val WIN]. rewrite E2_0. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. apply Hwin. lia.
+ assert (HMt : mem_ok tfibsegs E2 (mrestrict (w_H W') mem3) rsPM).
{ split; [exact WF2 |]. split; [exact Hrs0 | exact (proj2 Hpd)]. }
assert (HK : Forall (region_kept tfibsegs E2 (mrestrict (w_H W') mem3) (mrestrict (w_H W') mem4)) rsPM).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) KEEP r Hr) as Hc. unfold AD1y.drv_keep_ok, AD1ycf.drv_keep_ok in Hc.
pose proof (proj1 (Forall_forall _ _) Hrs0 r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E2 (r_base r) + r_lo r <= a < base_val E2 (r_base r) + r_hi r ->
~ (nb <= a < nb + ncp) /\ ~ (usp - 208 - ESTACK <= a < usp - 208)).
{ intros a Ha. destruct (r_base r) as [[|[|[|[|[|[|[|kk]]]]]]]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E2_0 in Ha. unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. pose proof (u64_range (ew E2 6)). unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. split; [| unfold ESTACK, sp_window_lo in *; lia].
intros Hab. apply (NIMG a ltac:(lia)). apply in_img_hull. lia. }
split; intros a Ha; [apply SCR; [lia | apply OFF; exact Ha | apply OFF; exact Ha]|].
intros Hw. exact (wview_grows tfibsegs _ _ _ (mem_grows_of_apresent (w_H W') mem3 mem4 Hpres) Hw). }
exact (proj1 (proj2 (mem_ok_kept tfibsegs E2 _ (mrestrict (w_H W') mem4) rsPM HMt WF2 HK))). }
rewrite EQr.
apply (st_ok_splice_havoc tfibsegs K_PC E2 ss regs3 regs4 pc3 A_PC_RET (mrestrict (w_H W') mem3) (mrestrict (w_H W') mem4) (ss_mem ss) [] CLOB HS).
- exact ATC.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- rewrite MPC. exact MAT.
- cbn [map app]. apply regs_preserved_frame. apply aregs_regs_preserved. exact HP.
- constructor.
- rewrite MPC. exact GOAL.
Qed.
Lemma pl_to_L : forall (c0 : bool) (k : Z) E4 (W : world tfibsegs) ms (n q : Z),
st_ok tfibsegs E4 (if c0 then S_PL0 else S_PL1 k) (restrict (w_H W) ms) ->
U E4 sv_pl00 = n -> 0 <= n <= 2 ^ 26 -> bv_unsigned (ew E4 A_PBLK) = q -> 4096 <= q -> q <= 2 ^ 47 -> 1 <= k <= 4 -> (c0 = true -> k = 1) ->
let E' := E_L E4 (ms_regs ms) in
st_ok tfibsegs E' S_L (restrict (w_H W) ms)
/\ bv_unsigned (ew E' 162) = n /\ bv_unsigned (ew E' 163) = q /\ bv_unsigned (ew E' 164) = q /\ bv_unsigned (ew E' 166) = k
/\ (forall j, (j < K_L)%nat -> ew E' j = ew E4 j).
Proof.
intros c0 k E4 W ms n q HS Hn Hnb Hq Hq1 Hq2 Hk Hc0 E'.
set (ss := if c0 then S_PL0 else S_PL1 k) in *. set (regs := ms_regs ms) in *.
pose proof (PL_if c0 k) as (MPL & PCL & RVL & _ & CHK & _). fold ss in MPL, PCL, RVL, CHK.
pose proof S_PL_regs as (P8a & P8b & P9a & P9b & P10a & P10b & P11a & P11b & P18a & P18b & P20a & P20b & _).
assert (R : forall r v, (sr_get (ss_regs S_PL0) r = v /\ sr_get (ss_regs (S_PL1 k)) r = v) -> getr regs r = sv_denot E4 v).
{ intros r v [H0 H1]. subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E4 ss ms r HS). subst ss. destruct c0; [rewrite H0 | rewrite H1]; reflexivity. }
assert (R8 : getr regs 8%bv = sv_denot E4 sv_pl00) by (apply R; split; [exact P8a | exact (P8b k)]).
assert (R9 : getr regs 9%bv = sv_denot E4 (SOff A_PBLK 0)) by (apply R; split; [exact P9a | exact (P9b k)]).
assert (R10 : getr regs 10%bv = sv_denot E4 (SOff A_PBLK 0)) by (apply R; split; [exact P10a | exact (P10b k)]).
assert (R11 : getr regs 11%bv = sv_denot E4 (add0 sv_pl00)) by (apply R; split; [exact P11a | exact (P11b k)]).
assert (R18 : getr regs 18%bv = sv_denot E4 (SOff A_PBLK 0)) by (apply R; split; [exact P18a | exact (P18b k)]).
assert (R20 : getr regs 21%bv = w64 k).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E4 ss ms 21%bv HS). subst ss. destruct c0; [rewrite (Hc0 eq_refl), P20a | rewrite (P20b k)]; reflexivity. }
assert (R8_11 : getr regs 11%bv = getr regs 8%bv) by (rewrite R8, R11, !denot_lit_U, U_add0; reflexivity).
assert (NEW : forall i r, (i < 18)%nat -> nth i L_srcs 0%bv = r -> ew E' (K_L + i) = getr regs r).
{ intros i r Hi <-. subst E'. unfold E_L. rewrite (ew_havoc_new E4 K_L _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < K_L)%nat -> ew E' j = ew E4 j) by (intros j Hj; subst E'; unfold E_L; apply ew_havoc_old; exact Hj).
assert (Q83 : sv_denot E4 (SOff A_PBLK 0) = w64 q) by (cbn [sv_denot]; rewrite Z.add_0_r, <- Hq; reflexivity).
assert (V61 : bv_unsigned (ew E' 162) = n).
{ change 162%nat with (K_L + 0)%nat. rewrite (NEW 0%nat 8%bv) by (cbn; first [lia | reflexivity]). rewrite R8. rewrite denot_lit_U, Hn. apply u64_lit. lia. }
assert (V62 : bv_unsigned (ew E' 163) = q).
{ change 163%nat with (K_L + 1)%nat. rewrite (NEW 1%nat 9%bv) by (cbn; first [lia | reflexivity]). rewrite R9, Q83. apply u64_lit. lia. }
assert (V63 : bv_unsigned (ew E' 164) = q).
{ change 164%nat with (K_L + 2)%nat. rewrite (NEW 2%nat 18%bv) by (cbn; first [lia | reflexivity]). rewrite R18, Q83. apply u64_lit. lia. }
assert (V65 : bv_unsigned (ew E' 166) = k).
{ change 166%nat with (K_L + 4)%nat. rewrite (NEW 4%nat 21%bv) by (cbn; first [lia | reflexivity]). rewrite R20. apply u64_lit. lia. }
split; [| repeat split; assumption].
pose proof (st_ok_mem_ok tfibsegs E4 ss _ HS) as HM0. cbn [restrict ms_mem] in HM0. rewrite MPL in HM0.
assert (HM1 : mem_ok tfibsegs E4 (mrestrict (w_H W) (ms_mem ms)) L_mem).
{ rewrite <- (proj1 PM_pieces_eq). apply (mem_ok_refine E4 _ (WIN (-208) :: rsPL)); [exact HM0 | apply refines_PM_L |].
rewrite (proj1 PM_pieces_eq). exact (proj1 L_mem_wf). }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) L_mem).
{ apply (mem_ok_agree tfibsegs K_L E4); [| exact (proj1 (proj2 L_mem_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_L. rewrite <- PCL.
apply (st_ok_reabs tfibsegs LT162 E4 E' ss (restrict (w_H W) ms) L_regs L_mem L_facts HS).
- split; [| intros d _; subst E'; reflexivity]. intros j Hj. unfold LT162 in Hj. apply Nat.ltb_lt in Hj. exact (Eold j Hj).
- exact CHK.
- cbn [ms_regs restrict]. fold regs.
apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
Ltac oneP NEW i := rewrite <- (NEW i); [apply f_equal; reflexivity | cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ oneP NEW 0%nat | oneP NEW 1%nat | oneP NEW 2%nat | oneP NEW 3%nat | oneP NEW 4%nat | oneP NEW 5%nat | oneP NEW 6%nat | oneP NEW 7%nat
| oneP NEW 8%nat | oneP NEW 9%nat | oneP NEW 10%nat | oneP NEW 11%nat | oneP NEW 12%nat | oneP NEW 13%nat | oneP NEW 14%nat
| oneP NEW 15%nat | oneP NEW 16%nat | oneP NEW 17%nat
|   transitivity (getr regs 9%bv); [oneP NEW 1%nat | rewrite R9; rewrite <- R10; apply f_equal; apply bv_eq; vm_compute; reflexivity]
|   transitivity (getr regs 8%bv); [oneP NEW 0%nat | rewrite <- R8_11; apply f_equal; apply bv_eq; vm_compute; reflexivity] ] |]).
destruct Hin.
- rewrite L_fact_obls_eq.
constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]];
unfold afact_ok; cbn [af_lo af_hi af_al2 fst snd fact_n fact_p fact_q fact_r]; rewrite ?V61, ?V62, ?V63, ?V65;
change (2 ^ 0) with 1; rewrite ?Z.mod_1_r; repeat split; try reflexivity; lia.
- exact HM2.
Qed.
Theorem tfib_run_QM_at : forall ws (W : world tfibsegs) ms md ly S Hp data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data -> 0 < payload_len data ->
NS S <= NS init_state + ns_pre cap ->
let E3 := E_P (edset (havoc EL K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at B NP (if config_len data =? 0 then sPM0 else sPM1 (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S Hp pb cap ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S Hp data pb cap Hlk Hok Hplpos HNS E3 HT E60.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HHp & HTOP & Hbl & HNP & HXS & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HFI & HU & HAD).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (buf := sptr_addr B ly pb) in *. set (c0 := config_len data =? 0) in *. set (k := Z.of_nat (calls data)) in *.
set (ss := if c0 then sPM0 else sPM1 k) in *.
pose proof (config_len_bound data) as Hcl. pose proof (calls_bound data) as Hcb.
assert (Hpl : payload_len data = dlen data - 6 - config_len data) by reflexivity. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S _ W (ms_mem ms) md _ _ HAR Hin) as (Hbufm & Hb4096 & Hbce & _ & Hpres0 & _).
assert (Hreq1 : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
rewrite Hreq1 in Hbce, Hpres0.
assert (NIMGB : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. rewrite <- Hreq1 in Ha. exact (proj2 (alc_client_img _ _ ARL ly S _ W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha)))))). }
assert (E3old : forall j, (j < K_M1)%nat -> ew E3 j = ew EL j).
{ intros j Hj. subst E3. rewrite E_P_old by (unfold K_M1 in Hj; lia). cbn [ew edset]. apply ew_havoc_old. exact Hj. }
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (rewrite E3old by (unfold K_M1; lia); reflexivity).
assert (E3_6 : usp <= bv_unsigned (ew E3 6)) by (rewrite E3old by (unfold K_M1; lia); exact EL6).
assert (Ed2 : ed E3 2 = data) by (subst E3; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (UPL : U E3 sv_pl00 = payload_len data).
{ apply (U_pl00 E3 data d0 d1 (d2 :: rest) Ed2 Ed); unfold dlen; [exact E42 | lia | lia]. }
assert (Hk : 1 <= k <= 4) by (subst k; lia).
assert (Hk1 : c0 = true -> k = 1). { subst c0 k. intros Hz. unfold calls, cfg_byte. rewrite Hz. reflexivity. }
pose proof (PM_if c0 k) as (Hpc & Hrv & CK1 & Haft). fold ss in Hpc, Hrv, CK1, Haft.
pose proof rsPM_checks as (CK2 & _ & CK3 & CK4 & _ & CK5 & WOK).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 ss ms HS Hrv) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof sPM0_facts as (_ & A10 & A1 & A2 & A8 & _). pose proof (sPM1_facts k) as (_ & B10 & B1 & B2 & B8 & _).
assert (RG : forall r v, sr_get (ss_regs sPM0) r = v -> sr_get (ss_regs (sPM1 k)) r = v -> getr regs r = sv_denot E3 v).
{ intros r v H0 H1. subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 ss ms r HS). subst ss. destruct c0; [rewrite H0 | rewrite H1]; reflexivity. }
assert (R1 : getr regs 1%bv = w64 RA_PM) by (rewrite (RG 1%bv (SLit RA_PM) A1 B1); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -208)) by (rewrite (RG 2%bv (SOff 0 (-208)) A2 B2); cbn [sv_denot]; rewrite E3_0; reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (RG 3%bv (SLit TFIB_GP)) by (vm_compute; reflexivity); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (RG 4%bv (SLit TFIB_TP)) by (vm_compute; reflexivity); reflexivity).
assert (R8 : getr regs 8%bv = w64 (payload_len data)) by (rewrite (RG 8%bv sv_pl00 A8 B8); apply denot_of_U; exact UPL).
assert (R10 : getr regs 10%bv = w64 (payload_len data)) by (rewrite (RG 10%bv (add0 sv_pl00) A10 B10); apply denot_of_U; rewrite U_add0; exact UPL).
assert (Hsp' : spZ regs = usp + -208) by (unfold spZ; rewrite R2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = RA_PM) by (unfold raZ; rewrite R1; apply u64_lit; unfold RA_PM; lia).
pose proof (st_ok_mem_ok tfibsegs E3 ss _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. subst ss. destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem sPM0)); [exact HM | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem sPM0)); [exact HM | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem (sPM1 k))); [exact HM | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem (sPM1 k))); [exact HM | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
assert (HWF : Wf_cf (as_universe B) S) by exact (amc_wf _ _ _ Hp _ (proj1 HAR)).
assert (Hbb : blocks_bytes S = cap) by (rewrite blocks_bytes_blocks, Hbl; cbn; lia).
pose proof (room_of_np NP NPT S HNP) as HROOM. pose proof HROOM as (RM1 & RM2 & RM3). pose proof cf_malloc_max_ge as CMG.
assert (SUB : submem rsPM (ss_mem ss)) by (subst ss; rewrite <- (rs_PM_eq c0 k); exact (rs_PM_sub c0 k)).
rewrite Hshape, Hpc. change (Z_to_bv 64 A_wrap_malloc) with (w64 (pc_wrap_malloc Tfib_code)). rewrite <- (ts_code B HB).
fold regs mem. change (mkCfg (mkst regs (w64 (pc_wrap_malloc (as_code B))) mem (seg_rom tfibsegs)) md)
with (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md).
apply (MSITE ly S Hp W regs mem md (payload_len data) (run_shape (payload data) (calls data) (in_fs inp))).
-
split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [exact (conj HHp HROOM)|].
split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra; unfold RA_PM; lia|].
split; [rewrite Hsp'; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [| exact (conj (drv_minv_qtight _ _ _ Hminv) (conj (HULL_NS S ltac:(pose proof (ns_pre_max cap ltac:(lia)); lia)) HAD))].
unfold s0Z. rewrite R8. unfold w64. rewrite u64_lit by lia. lia.
- exact R10.
- unfold MALLOC_MAX. lia.
- rewrite Hbb. unfold LIVE_MAX. lia.
- exact (drv_minv_room (as_universe B) S cap (dlen data) (payload_len data) HWF Hminv ltac:(unfold payload_len, dlen, HDR_MIN in *; lia)).
- rewrite (ts_code B HB), Hra. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- exact HAI.
-
intros ly' S' W' regs' mem' md2 trc tr p' Hnn' Htrc Hpath HPOST HXP Ha0 Hwle HAI2.
unfold cfg_at. rewrite Hra.
pose proof HPOST as (HAR' & Hlyle & _ & HPres & Hio & Hfr' & Hsc').
destruct (atok_cf_apath _ _ _ tr _ (mlr_malloc_cf _ ML S (payload_len data) trc HWF ltac:(unfold MALLOC_MAX in CMG; lia)
ltac:(rewrite Hbb; unfold LIVE_MAX; lia) (admits_fix _ _ _ (ts_universe B HB) Htrc) RM1 RM2 RM3) Hpath)
as (ns' & HMP). cbn [malloc_post_cf] in HMP. destruct HMP as (HWF' & _ & _ & HfrM & Hbl' & HQT').
assert (HNP' : NP S') by exact (np_after_malloc_cf B NP NPS tfibsegs ly S Hp W mem md (payload_len data) trc tr p' S' HAR
(drv_minv_qtight _ _ _ Hminv) HNP ltac:(rewrite Hbl; cbn; unfold AD1w_cf.NP_LIVE; lia) Hpath).
assert (Hblocks : blocks S' = [(pb, cap); (p', payload_len data)] /\ ~ In p' [pb]).
{ rewrite Hbl in Hbl'. destruct p'; [exfalso; exact (Hnn' eq_refl) | exact Hbl' | exact Hbl' | exact Hbl']. }
destruct Hblocks as [Hblocks Hp'].
(* KF-COUNT #7: the payload malloc is the prefix's last; the count is at most NS init_state + 12 at the loop's entry *)
assert (HNS' : NS S' <= NS S + 1).
{ pose proof (YGcfXs.cfx_ipost_apath _ _ tr (p', S') (nsec_malloc_cf (payload_len data) trc S) Hpath) as N.
  cbv beta in N. cbn [snd] in N. destruct (from_primary (payload_len data)); lia. }
set (nb := sptr_addr B ly' p') in *.
assert (Etop : ly_top ly' = ly_top ly) by (destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
pose proof (alc_layout _ _ ARL ly S _ W mem md ly' HAR Hlyle) as (Habl & _ & _).
assert (Hpb' : sptr_addr B ly' pb = buf).
{ unfold ablocks in Habl. rewrite Hbl in Habl. cbn in Habl. injection Habl as Habl. rewrite Habl. reflexivity. }
assert (Hin1 : In (buf, cap) (ablocks B ly' S')) by (unfold ablocks; rewrite Hblocks; cbn; left; rewrite Hpb'; reflexivity).
assert (Hin2 : In (nb, payload_len data) (ablocks B ly' S')) by (unfold ablocks; rewrite Hblocks; cbn; right; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly' S' _ W' mem' md2 _ _ HAR' Hin2) as (Hnb16 & Hnb4096 & Hnbce & _ & HpresN & _).
pose proof (alc_blocks _ _ ARL ly' S' _ W' mem' md2 _ _ HAR' Hin1) as (_ & _ & _ & _ & HpresB & _).
assert (Hreq2 : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia).
rewrite Hreq2 in Hnbce, HpresN. rewrite Hreq1 in HpresB.
assert (NIMGN : forall a, nb <= a < nb + payload_len data -> ~ in_img tfibsegs a).
{ intros a Ha. rewrite <- Hreq2 in Ha. exact (proj2 (alc_client_img _ _ ARL ly' S' _ W' mem' md2 a HAR' (or_introl (ex_intro _ _ (ex_intro _ (payload_len data) (conj Hin2 Ha)))))). }
assert (Hsep : nb + payload_len data <= buf \/ buf + cap <= nb).
{ pose proof (sep_blocks_cf B ARL ly' S' Hp W' mem' md2 buf cap nb (payload_len data) HAR' Hin1 Hin2 ltac:(intros X; injection X; lia)) as X.
unfold zdisjoint in X. cbn [fst snd] in X. rewrite Hreq1, Hreq2 in X. lia. }
pose proof (malloc_E_place B ARL ly S Hp W mem md ly' S' W' mem' md2 nb (payload_len data) HAR HXS HAR' HXP Hlyle Hin2) as HEP.
pose proof (drv_after_call B HB ARL K_PM E3 ss ms ly S _ W md _ ly' S' W' regs' mem' md2 rsPM
RA_PM usp (-208) HS Hrv CK1 CK2 CK3 CK4 SUB ltac:(subst ss; destruct c0; [exact A1 | exact B1]) (YGcfRehidePost.acall_post_cf_rh_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) HAR
(fun a Ha => conj (proj1 (HEP a Ha)) (proj1 (proj2 (HEP a Ha))))
CK5 E3_0 E3_6 Hsp' ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin; lia)) as HS2.
rewrite Haft in HS2.
set (E2 := havoc E3 K_PM (map (getr regs') CLOB)) in HS2.
assert (A83 : ew E2 A_PBLK = w64 nb).
{ subst E2. unfold A_PBLK. change 184%nat with (K_PM + 4)%nat. rewrite (ew_havoc_new E3 K_PM _ 4 (w64 0)) by (cbn; lia). cbn. exact Ha0. }
assert (U83 : bv_unsigned (ew E2 A_PBLK) = nb) by (rewrite A83; apply u64_lit; lia).
assert (E2old : forall j, (j < K_PM)%nat -> ew E2 j = ew E3 j) by (intros j Hj; subst E2; apply ew_havoc_old; exact Hj).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia); exact E3_0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia); exact E3_6).
assert (Ed22 : ed E2 2 = data) by (change (ed E2 2) with (ed E3 2); exact Ed2).
assert (UPL2 : U E2 sv_pl00 = payload_len data).
{ apply (U_pl00 E2 data d0 d1 (d2 :: rest) Ed22 Ed); unfold dlen; [rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia); exact E42 | lia | lia]. }
apply (st_ok_add_cond tfibsegs _ _ _ Instr.BC_NE (SOff A_PBLK 0) (SLit 0)) in HS2.
2:{ cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken]. rewrite Z.add_0_r, U83. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 nb) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by lia. lia. }
destruct (same_io_fs_fds _ _ Hio) as [Efs Efds].
apply (SRr_srealizes tfibsegs W' _ _ _ (pc_run c0 k E2 W' regs' mem' md2 HS2) HAI2).
intros W1 c1 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3.
rewrite (PMr_if c0 k) in HF3, HFr3.
pose proof (PC_if c0 k) as (MPC & PCC & RVC & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E2 (if c0 then S_PC0 else S_PC1 k) ms3 HS3 RVC) as Hshape3.
set (regs3 := ms_regs ms3) in *. set (mem3 := ms_mem ms3) in *.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
assert (RG3 : forall r v, sr_get (ss_regs S_PC0) r = v -> sr_get (ss_regs (S_PC1 k)) r = v -> getr regs3 r = sv_denot E2 v).
{ intros r v H0 H1. subst regs3. rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 (if c0 then S_PC0 else S_PC1 k) ms3 r HS3). destruct c0; [rewrite H0 | rewrite H1]; reflexivity. }
assert (R1' : getr regs3 1%bv = w64 A_PC_RET) by (rewrite (RG3 1%bv (SLit A_PC_RET)) by (vm_compute; reflexivity); reflexivity).
assert (R2' : getr regs3 2%bv = Z_to_bv 64 (usp + -208)) by (rewrite (RG3 2%bv (SOff 0 (-208))) by (vm_compute; reflexivity); cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (R3' : getr regs3 3%bv = w64 TFIB_GP) by (rewrite (RG3 3%bv (SLit TFIB_GP)) by (vm_compute; reflexivity); reflexivity).
assert (R4' : getr regs3 4%bv = w64 TFIB_TP) by (rewrite (RG3 4%bv (SLit TFIB_TP)) by (vm_compute; reflexivity); reflexivity).
assert (R10' : getr regs3 10%bv = w64 nb) by (rewrite (RG3 10%bv (SOff A_PBLK 0)) by (vm_compute; reflexivity); cbn [sv_denot]; rewrite Z.add_0_r, U83; reflexivity).
assert (R11' : getr regs3 11%bv = w64 (buf + 6 + config_len data)).
{ rewrite (RG3 11%bv (SOff 161 4)) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia). change 161%nat with K_PP. rewrite E60. unfold w64. f_equal. lia. }
assert (R12' : getr regs3 12%bv = w64 (payload_len data)) by (rewrite (RG3 12%bv (add0 sv_pl00)) by (vm_compute; reflexivity); apply denot_of_U; rewrite U_add0; exact UPL2).
assert (Hsp3 : spZ regs3 = usp - 208) by (unfold spZ; rewrite R2'; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (Hra3 : raZ regs3 = A_PC_RET) by (unfold raZ; rewrite R1'; apply u64_lit; unfold A_PC_RET, RA_PC; lia).
pose proof (st_ok_mem_ok tfibsegs E2 _ _ HS3) as HM3. cbn [restrict ms_mem] in HM3. fold mem3 in HM3. rewrite MPC in HM3.
assert (Hwin3 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem3 a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E2 (w_H W') mem3 (WIN (-208) :: rsPM)); [exact HM3 | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') mem3 (WIN (-208) :: rsPM)); [exact HM3 | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') mem3 (WIN (-208) :: rsPM)); [exact HM3 | right; right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
assert (HAR3 : ARcf tfibsegs B ly' S' Hp W' mem3 md3).
{ apply (AR_after_run B HB ARL ly' S' _ W' E2 (WIN (-208) :: rsPM) mem' mem3 md2 mat3 HAR' WOK); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HF3 |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin3 a Ha)). }
pose proof (alc_blocks _ _ ARL ly' S' _ W' mem3 md3 _ _ HAR3 Hin2) as (_ & _ & _ & _ & HpresN3 & _). rewrite Hreq2 in HpresN3.
pose proof (alc_blocks _ _ ARL ly' S' _ W' mem3 md3 _ _ HAR3 Hin1) as (_ & _ & _ & _ & HpresB3 & _). rewrite Hreq1 in HpresB3.
rewrite Hshape3, PCC. change (Z_to_bv 64 A_icpt_memcpy) with (w64 (pc_wrap_memcpy Tfib_code)). rewrite <- (ts_code B HB).
fold regs3 mem3. change (mkCfg (mkst regs3 (w64 (pc_wrap_memcpy (as_code B))) mem3 (seg_rom tfibsegs)) md3)
with (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs3 mem3 md3).
eapply (SRr_srealizes tfibsegs W' (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs3 mem3 md3)); [| exact HAI3 |].
{ apply (MCPY ly' S' Hp W' regs3 mem3 md3 nb (buf + 6 + config_len data) (payload_len data)).
- split; [exact HAR3|]. split; [pose proof (top_ok_le _ _ _ _ Hlyle HTOP) as (_ & TK2 & TK3 & _); exact (conj TK2 TK3)|]. split; [rewrite R1'; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Hsp3; replace (usp - 208) with (usp + (-13) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp3; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp3, Etop; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp3; intros a Ha; apply Hwin3; unfold ESTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3' | rewrite (ts_tp B HB); exact R4'].
- exact R10'.
- exact R11'.
- exact R12'.
- lia.
- lia.
- lia.
- intros a Ha. split; [apply (apresent_writable tfibsegs); exact (proj1 (HpresN3 a ltac:(lia)))|]. split; [exact (proj2 (HpresN3 a ltac:(lia)))|].
rewrite Hsp3. unfold sp_window_lo, ESTACK in *. lia.
- apply (amem_range_of_block_cf B ARL ly' S' Hp W' mem3 md3 nb (payload_len data) nb (payload_len data) HAR3 Hin2); [lia | rewrite Hreq2; lia].
- apply (range_addressable_of_block' B ARL ly' S' Hp W' mem3 md3 nb (payload_len data) nb (payload_len data) HAR3 HHp Hin2); [lia | rewrite Hreq2; lia].
- intros Hn0. apply (shadow_hull_vis_of_block' B ARL ly' S' _ W' mem3 md3 nb (payload_len data) nb (payload_len data) HAR3 Hin2); [lia | rewrite Hreq2; lia | lia].
- lia.
- lia.
- intros a Ha. split; [apply (aview_some_of_apresent tfibsegs); exact (proj1 (HpresB3 a ltac:(lia)))|].
rewrite Hsp3. unfold sp_window_lo, ESTACK in *. lia.
- lia.
- apply (amem_range_of_block_cf B ARL ly' S' Hp W' mem3 md3 buf cap (buf + 6 + config_len data) (payload_len data) HAR3 Hin1); [lia | rewrite Hreq1; lia].
- apply (range_addressable_of_block' B ARL ly' S' Hp W' mem3 md3 buf cap (buf + 6 + config_len data) (payload_len data) HAR3 HHp Hin1); [lia | rewrite Hreq1; lia].
- intros Hn0. apply (shadow_hull_vis_of_block' B ARL ly' S' _ W' mem3 md3 buf cap (buf + 6 + config_len data) (payload_len data) HAR3 Hin1); [lia | rewrite Hreq1; lia | lia]. }
cbv beta. intros W2 c2 _ HAI4 (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hs4 & Ha04 & Hcpy & Hfr4 & Hpres4). cbn [cfg_model] in HAI4.
unfold cfg_at. rewrite Hra3. rewrite Hsp3 in Hfr4.
rewrite Hshape3, restrict_mkst_fx in HS3. fold regs3 mem3 in HS3.
pose proof (pc_reseat c0 k E2 W' regs3 _ mem3 regs4 mem4 nb (payload_len data) HS3 E2_0 E2_6 HP4 Hfr4 Hpres4 NIMGN ltac:(lia) HCT
ltac:(intros a Ha; apply Hwin3; lia)) as HS5.
set (E4 := havoc E2 K_PC (map (getr regs4) CLOB)) in HS5.
assert (E4old : forall j, (j < K_PC)%nat -> ew E4 j = ew E2 j) by (intros j Hj; subst E4; apply ew_havoc_old; exact Hj).
assert (E4_0 : bv_unsigned (ew E4 0) = usp) by (rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia); exact E2_0).
assert (E4_6 : usp <= bv_unsigned (ew E4 6)) by (rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia); exact E2_6).
assert (U83_4 : bv_unsigned (ew E4 A_PBLK) = nb) by (rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia); exact U83).
assert (Ed42 : ed E4 2 = data) by (change (ed E4 2) with (ed E3 2); exact Ed2).
assert (UPL4 : U E4 sv_pl00 = payload_len data).
{ apply (U_pl00 E4 data d0 d1 (d2 :: rest) Ed42 Ed); unfold dlen; [rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia); rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia); exact E42 | lia | lia]. }
pose proof (same_but_materialized_frame _ _ Hs4) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds4 & _ & _ & Hfs4 & _).
assert (Hwin4 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem4 a) by (intros a Ha; apply Hpres4; apply Hwin3; exact Ha).
rewrite <- restrict_mkst_fx in HS5.
apply (SRr_srealizes tfibsegs W' _ _ _ (pl_run c0 k E4 W' regs4 mem4 md4 HS5) HAI4).
intros W3 c3 _ HAI5 (-> & ms5 & mat5 & -> & HS6 & HF5 & HFr5). cbn [cfg_model] in HAI5.
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4) in *.
pose proof (PL_if c0 k) as (MPL & _ & _ & _ & _ & MPCr). rewrite MPCr in HF5, HFr5.
pose proof (st_ok_mem_ok tfibsegs E4 _ _ HS6) as HM5. cbn [restrict ms_mem] in HM5.
(* the first call's interface facts: every program-object byte reads its start-up value and is writable *)
pose proof (PL_gf_start c0 k E4 W' (ms_mem ms5) HM5) as HGF.
assert (GOBJ : W_LLVMFuzzerTestOneInput_G.G_fr_obj = GF_OBJ) by (rewrite GF_OBJ_val; reflexivity).
rewrite MPL in HM5.
assert (Hwin5 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem ms5) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem ms5) (WIN (-208) :: rsPL)); [exact HM5 | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem ms5) (WIN (-208) :: rsPL)); [exact HM5 | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem ms5) (WIN (-208) :: rsPL)); [exact HM5 | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HAR5 : ARcf tfibsegs B ly' S' Hp W' (ms_mem ms5) md5).
{ apply (AR_after_run B HB ARL ly' S' _ W' E4 (WIN (-208) :: rsPM) mem4 (ms_mem ms5) md4 mat5 HAR4 WOK); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HF5 |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin5 a Ha)). }
destruct (PL_img_facts E4 (w_H W') (ms_mem ms5) HM5) as [HIMG5 HRO5].
pose proof (pl_to_LF c0 k E4 W' ms5 (payload_len data) nb HS6 UPL4 ltac:(lia) U83_4 Hnb4096 ltac:(lia) Hk Hk1) as (HSL & V61 & V62 & V63 & V65 & ELold).
set (E6 := E_L E4 (ms_regs ms5)) in *.
assert (HBLK' : blk (w_H W') mem' buf (Z.of_nat (length data)) data).
{ apply (blk_copy (w_H W) (w_H W') mem mem' buf buf (Z.of_nat (length data)) data); [| exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact HBLK].
intros i Hi. apply Hfr'.
- lia.
- exact (proj2 (Hpres0 (buf + i) ltac:(lia))).
- exact (proj2 (HpresB (buf + i) ltac:(lia))).
- apply (not_ascratch B HB ASTACK regs (buf + i) (usp + -208) Hsp'); [apply NIMGB; lia | lia | unfold ASTACK; lia].
- intros [[X1 X2] | X]; [rewrite Hreq2 in X2; lia|].
exact (xs_pair_not_block B ly S Hp W mem md ly' S' Hp W' mem' md2 (buf + i) buf cap HAR HXS HAR' HXP Hin Hin1 ltac:(rewrite Hreq1; lia) X). }
assert (HBLK3 : blk (w_H W') mem3 buf (Z.of_nat (length data)) data).
{ apply (blk_of_frame_r _ E2 (WIN (-208) :: rsPM) _ _ buf (Z.of_nat (length data)) data usp HFr3 WOK E2_0 Ulo); [intros a Ha; apply NIMGB; lia | lia | lia | exact HBLK']. }
assert (HPL4 : blk (w_H W') mem4 nb (payload_len data) (payload data)).
{ apply (blk_copy (w_H W') (w_H W') mem3 mem4 (buf + 6 + config_len data) nb (payload_len data) (payload data) Hcpy);
[exact (fun i Hi => NIMGB (buf + 6 + config_len data + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGN (nb + i) ltac:(lia)) | lia | lia |].
change (payload data) with (skipn (Z.to_nat (6 + config_len data)) data).
replace (buf + 6 + config_len data) with (buf + (6 + config_len data)) by lia. rewrite Hpl.
replace (Z.of_nat (length data) - 6 - config_len data) with (Z.of_nat (length data) - (6 + config_len data)) by lia.
apply (blk_shift (w_H W') mem3 buf (Z.of_nat (length data)) data (6 + config_len data) HBLK3). lia. }
assert (HPL5 : blk (w_H W') (ms_mem ms5) nb (payload_len data) (payload data)).
{ apply (blk_of_frame_r _ E4 (WIN (-208) :: rsPM) _ _ nb (payload_len data) (payload data) usp HFr5 WOK E4_0 Ulo); [intros a Ha; apply NIMGN; lia | lia | lia | exact HPL4]. }
pose proof (top_ok_le _ _ _ _ Hlyle HTOP) as HTOP'.
(* the entry image above the entry sp: through the payload malloc (stk_up_acall), the copy-call run, the memcpy site
   (it writes the new block and its scratch) and the run to the loop *)
assert (HU5 : stk_up usp ly' W' (ms_mem ms5)).
{ assert (HU' : stk_up usp ly' W' mem').
{ apply (stk_up_acall B HB ARL _ ly S Hp W regs mem md _ ly' S' W' regs' mem' md2 usp HAR HPOST); [| rewrite Hsp'; lia | exact (conj Ulo Uhi) | exact HTOP | exact HU].
intros a Ea. pose proof (proj1 (HEP a Ea)). lia. }
pose proof (AD2acf.stk_up_drv E2 _ W' mem' mem3 usp ly' HFr3 WOK E2_0 (conj Ulo Uhi) HTOP' HU') as HU3.
assert (HU4 : stk_up usp ly' W' mem4).
{ apply (stk_up_high usp ly' ly' W' W' mem3 mem4); [| reflexivity | exact Uhi | exact HTOP' | exact HU3]. intros a Ha. apply Hfr4; unfold ESTACK in *; lia. }
exact (AD2acf.stk_up_drv E4 _ W' mem4 (ms_mem ms5) usp ly' HFr5 WOK E4_0 (conj Ulo Uhi) HTOP' HU4). }
assert (HFI5 : FINV ly' (w_H W') (ms_mem ms5)).
{ assert (HFIm : FINV ly' (w_H W') mem').
{ apply (finv_site_x B HB ARL ASTACK ly S _ W regs mem md _ ly' S' W' regs' mem' md2 usp HAR HPOST); [| exact HTOP | exact Ulo | exact Uhi | rewrite Hsp'; lia | unfold ASTACK; lia | exact HFI].
intros a Ha. exact (proj2 (HEP a Ha)). }
assert (HFI3 : FINV ly' (w_H W') mem3) by exact (finv_run B ly' S' _ W' mem' md2 (w_H W') E2 (WIN (-208) :: rsPM) _ _ usp HAR' HFr3 WOK E2_0 Ulo Uhi HTOP' HFIm).
assert (HFI4 : FINV ly' (w_H W') mem4).
{ apply (finv_icpt B HB ARL ly' S' _ W' mem3 md3 mem4 (fun a => nb <= a < nb + payload_len data) (usp - 208 - ESTACK) (usp - 208) usp HAR3 HTOP' Ulo Uhi Hfr4); [unfold ESTACK; lia | lia | | exact HFI3].
intros a Ha. exists nb, (payload_len data). split; [exact Hin2 | rewrite Hreq2; lia]. }
exact (finv_run B ly' S' _ W' mem4 md4 (w_H W') E4 (WIN (-208) :: rsPM) _ _ usp HAR4 HFr5 WOK E4_0 Ulo Uhi HTOP' HFI4). }
(* field round 3 (Part A): the RELRO bytes at the loop's entry: the payload malloc's post frame, the copy-call run,
   memcpy's view frame, the run to the loop *)
assert (HAD5 : arodata_ok_cf tfibsegs B (ms_mem ms5)).
{ assert (HADm : arodata_ok_cf tfibsegs B mem').
  { apply (aro_site_x B HB ASTACK ly S _ W regs mem md _ ly' S' W' regs' mem' md2 usp RO HAR HPOST);
    [| exact HTOP | exact Ulo | exact Uhi | rewrite Hsp'; lia | unfold ASTACK; lia | exact HAD].
    intros a Ha. exact (proj1 (proj2 (HEP a Ha))). }
  assert (HAD3 : arodata_ok_cf tfibsegs B mem3)
  by exact (aro_run B W' E2 (WIN (-208) :: rsPM) mem' mem3 RO HFr3 WOK ltac:(rewrite E2_0; exact Ulo) HADm).
  assert (HAD4 : arodata_ok_cf tfibsegs B mem4).
  { apply (aro_icpt B ARL ly' S' _ W' mem3 md3 mem4 (fun a => nb <= a < nb + payload_len data) (usp - 208 - ESTACK) (usp - 208) usp RO HAR3 Ulo Hfr4);
    [unfold ESTACK; lia | | exact HAD3].
    intros a Ha. exists nb, (payload_len data). split; [exact Hin2 | rewrite Hreq2; lia]. }
  exact (aro_run B W' E4 (WIN (-208) :: rsPM) mem4 (ms_mem ms5) RO HFr5 WOK ltac:(rewrite E4_0; exact Ulo) HAD4). }
assert (Hfds5 : m_fds md5 = APSG.fds_std) by (subst md5; rewrite wvb_fds', Hfds4; subst md3; rewrite wvb_fds', Efds; exact Hfds).
assert (Hfs5 : m_fs md5 = in_fs inp) by (subst md5; rewrite wvb_fs', Hfs4; subst md3; rewrite wvb_fs', Efs; exact Hfs).
change (run_shape (payload data) (calls data) (in_fs inp)) with (loop_tgt (payload data) (calls data) 0%nat (calls data) (in_fs inp)).
apply (LOOPL sp inp xw xd E6 W' ms5 md5 ly' S' Hp a0 p data pb p' cap nb 0%nat (calls data) (in_fs inp) Hargv Hsp Hva Hve Hvfs Hlk ltac:(unfold dlen; lia)).
+ intros j Hj. rewrite ELold by (unfold K_L, K_M1 in *; lia). rewrite E4old by (unfold K_PC, K_M1 in *; lia). rewrite E2old by (unfold K_PM, K_M1 in *; lia). apply E3old. exact Hj.
+ change (ed E6 2) with (ed E3 2). exact Ed2.
+ rewrite ELold by (unfold K_L, A_BUF, A_LEN, K_PP, A_PBLK; lia). rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia). rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia). rewrite Hpb'. exact E41.
+ rewrite ELold by (unfold K_L, A_BUF, A_LEN, K_PP, A_PBLK; lia). rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia). rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia). unfold dlen. exact E42.
+ rewrite ELold by (unfold K_L, A_BUF, A_LEN, K_PP, A_PBLK; lia). rewrite E4old by (unfold K_PC, A_BUF, A_LEN, K_PP, A_PBLK; lia). rewrite E2old by (unfold K_PM, A_BUF, A_LEN, K_PP; lia). rewrite Hpb'. exact E60.
+ exact V61.
+ rewrite V62. replace (payload_len data =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
+ exact V63.
+ rewrite V65. subst k. reflexivity.
+ exact HSL.
+ lia.
+ lia.
+ reflexivity.
+ right. split; [lia|]. split; [exact Hblocks | reflexivity].
+ intros _. exact HPL5.
+ rewrite HfrM. exact (drv_minv_frames _ _ _ Hminv).
+ exact (HQT' (drv_minv_qtight _ _ _ Hminv)).
+ exact HAI5.
+ exact HAR5.
+ exact HHp.
+ exact (top_ok_le _ _ _ _ Hlyle HTOP).
+ exact HNP'.
+ exact (AFrInit_fp.fr_hblks_init W' (ms_mem ms5) (fun a Ha => proj1 (HGF a Ha))).
+ pose proof (ns_pre_max cap ltac:(lia)) as NM. lia.
+ exact (AFrInit_fp.fr_capout_init W' (ms_mem ms5) (fun a Ha => proj1 (HGF a Ha))).
+ apply (AD1w_cf_inv.fr_lib_inv_init_ok B ltac:(rewrite (ts_errno B HB); reflexivity) ly' S' W' (ms_mem ms5) gf_init).
* intros a Ha. rewrite GOBJ in Ha. exact (HGF a Ha).
* intros a _. exact (gf_init_rom a).
+ exact (AD1r_fp.rom_view_of_arodata B HB _ (YGcallcf.AR_laws_x_cf tfibsegs B ARL) ly' S' Hp W' (ms_mem ms5) _ HAR5 HRO5).
+ exact HU5.
+ exact Hcap.
+ unfold dlen. lia.
+ left. split; [reflexivity | exact HIMG5].
+ exact HRO5.
+ exact HFI5.
+ split; [intros k0; rewrite Hfds5; reflexivity|]. split; [rewrite Hfds5; reflexivity|]. split; [exact Hfs5 | exact (proj1 Hvfs)].
+ exact HAD5.
Qed.
End e.
Theorem tfib_run_QM (B : asyms) (NP : astate -> Prop) (NPT : AD1w_cf.iface_room_np_tail NP) (NPS : AD1w_cf.iface_room_np_step NP)
(HB : TfibSyms B) (ARL : AR_laws_cf tfibsegs B) (ML : model_laws_cf (as_universe B))
(MSITE : malloc_site_tfa B) (MCPY : memcpy_site_tfa B)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop)
(EXITL : exit_leaf_tfa B xst) (XFR : xst_frame_tfa xst) (NS : astate -> Z) (NRUN XNMAX : Z)
(nsec_malloc_cf : forall n tr s,
  YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1)))
(NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN) (XNMAX_NN : 0 <= XNMAX) (HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S)
(LOOPL : loop_L_x B NP NS NRUN XNMAX xst) (RO : relro_ok) : run_QM_tfa B NP NS.
Proof.
intros sp inp xw xd ws W ms md ly S Hp a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hok Hpl HNS E3 HT E60.
exact (tfib_run_QM_at B NP NPT NPS HB ARL ML MSITE MCPY xst NS NRUN XNMAX nsec_malloc_cf NS_START XNMAX_NN HULL_NS LOOPL RO sp inp xw xd a0 p
Hargv Hsp Hva Hve Hvfs ws W ms md ly S Hp data pb cap Hlk Hok Hpl HNS HT E60).
Qed.
End b.
