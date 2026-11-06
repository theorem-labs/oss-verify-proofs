(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file holding text copied from A/AD2f.v (lines 147-286) with renamed
   definitions: the driver's call-site view (IMG_LCF, L_memF, S_LF, L_piecesF) and after-call views (IMG_LF, CM_memF and
   the free / exit states built on it) of fuzz_reply.asan, with fuzz_reply's program globals G_fr_c TfibB CLIPPED OUT
   (GF_RANGES below; W_LLVMFuzzerTestOneInput_G.v G_fr_obj ++ [(TFIB_ERRNO_A, 4)]), because the cf program contract lets
   LLVMFuzzerTestOneInput write them on every call (its journal's PST, A/AD1w_cf.v:163).  A/AD2f.v keeps the donor's
   views for the donor contract.  Form of omx-clap-core/fuzz_state's clipL (a working branch 86d3792c013,
   a Theorem Labs lane's c3a3d1e1d86 + 2d1ebd16550), with FS_PSTAT_FP replaced by GF_IVS.  Counts read by vm_compute on
   a build machine: IMG_LF / IMG_LCF 41 regions (IMG_L / IMG_LC 59): eighteen of G_fr's objects are whole regions of
   AD2j.v and go, g_thread (0x5d8740, 8) cuts the tail of R_A5a_1 and g_wake (0xa1fa0, 8) the tail of R_A3_1; errno
   (0x5d93cc) lies in no image region. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09 YL02 YL04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1y AD24 AD2h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Export ACeg ACfl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the clip ---- *)
(* G_fr_c TfibB as (address, size): W_LLVMFuzzerTestOneInput_G.v G_fr_obj (the 20 program objects) ++ [(errno, 4)];
   A/AD1r_fp.v proves G_fr_c TfibB = GF_RANGES where both are in scope. *)
Definition GF_RANGES : list (Z * Z) :=
  [ (0x5d88e0, 384); (0x5d8820, 4); (0x5d8b40, 8); (0x5d88c0, 8); (0x5d8b20, 8); (0x5d8840, 8);
    (0x5d88a0, 1); (0x5d8880, 1); (0x5d8860, 1); (0x5d8ac0, 40); (0x5d8740, 8); (0x5d8760, 1);
    (0x5d8780, 4); (0xa1fc0, 4); (0xa1fe0, 4); (0x5d87e0, 1); (0xa1fa0, 8); (0x5d87c0, 8);
    (0x5d87a0, 4); (0x5d8800, 4); (0x5d93cc, 4) ].
Definition GF_IVS : list (Z * Z) := map (fun r => (fst r, fst r + snd r)) GF_RANGES.
Definition clip_ivs (ivs : list (Z * Z)) (r : YP09.region) : list YP09.region :=
  fold_right (fun iv rs => flat_map (clip_out (fst iv) (snd iv)) rs) [r] ivs.
Definition clipLF (r : YP09.region) : list YP09.region :=
  flat_map (clip_ivs GF_IVS) (flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)).

(* ---- the after-call and call-site views (AD2f.v:153-154) ---- *)
Definition IMG_LF : smem := Eval vm_compute in flat_map clipLF IMG_B.
Definition IMG_LCF : smem := Eval vm_compute in flat_map clipLF IMG_E.
(* the call site (AD2f.v:166-170) *)
Definition L_memF : smem := Eval vm_compute in ([WIN208; TRF] ++ firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_LCF).
Definition S_LF : sstate := mkSS A_LLVMF L_regs L_memF None L_facts.
Lemma L_memF_wf : regions_wf L_memF = true /\ mem_atoms_lt K_L L_memF = true /\ length IMG_LF = 41%nat /\ forallb drv_win_ok L_memF = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma IMG_LCF_len : length IMG_LCF = 41%nat /\ length L_memF = 45%nat. Proof. vm_compute. split; reflexivity. Qed.
(* AD2f.v:178-184 *)
Definition L_piecesF : list smem :=
[ [WIN208; TRF] ] ++ map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map clipLF IMG_E ++ [ []; []; []; []; [] ].
Lemma L_piecesF_eq : concat L_piecesF = L_memF /\ length L_piecesF = length (ss_mem sPE0) /\ forall k, length L_piecesF = length (ss_mem (sPE1 k)).
Proof. repeat split; intros; vm_compute; reflexivity. Qed.
Definition L_piecesCF : list smem := Eval vm_compute in L_piecesF.
Lemma L_piecesCF_eq : L_piecesCF = L_piecesF /\ concat L_piecesCF = L_memF. Proof. vm_compute. split; reflexivity. Qed.
Lemma S_LF_eq : ss_mem S_LF = L_memF /\ ss_pc S_LF = A_LLVMF /\ ss_regs S_LF = L_regs /\ ss_facts S_LF = L_facts /\ ss_resv S_LF = None.
Proof. repeat split; reflexivity. Qed.

(* ---- target_run's tail after the loop, on the clipped view (AD2f.v:238-286) ---- *)
Definition CM_memF : smem := Eval vm_compute in (WIN208 :: TRF0 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_LF).
Definition S_CMF : sstate := mkSS A_CM CM_regs CM_memF None CM_facts.
Definition S_FBtF : sstate := Eval vm_compute in run_lp (add_cond S_CMF cond_CMt).
Definition S_FBfF : sstate := Eval vm_compute in run_lp (add_cond S_CMF cond_CMf).
Definition rs_FBF : smem := Eval vm_compute in List.filter gkeep (ss_mem S_FBtF).
Definition S_FBrtF : sstate := Eval vm_compute in drv_after S_FBtF rs_FBF K_FB RA_FB (-128).
Definition S_FBrfF : sstate := Eval vm_compute in drv_after S_FBfF rs_FBF K_FB RA_FB (-128).
Definition S_XTtF : sstate := Eval vm_compute in run_lp S_FBrtF.
Definition S_XTfF : sstate := Eval vm_compute in run_lp S_FBrfF.
Lemma CM_memF_wf : regions_wf CM_memF = true /\ mem_atoms_lt K_CM CM_memF = true /\ forallb drv_win_ok CM_memF = true /\ skipn 4 CM_memF = IMG_LF /\ firstn 2 (skipn 2 CM_memF) = firstn 2 (skipn 2 L_memF).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_FBF_facts : ss_pc S_FBtF = A_wrap_free /\ ss_pc S_FBfF = A_wrap_free /\ sr_get (ss_regs S_FBtF) 1%bv = SLit RA_FB /\ sr_get (ss_regs S_FBfF) 1%bv = SLit RA_FB
/\ sr_get (ss_regs S_FBtF) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_FBfF) 2%bv = SOff 0 (-128)
/\ sr_get (ss_regs S_FBtF) 8%bv = SLit 0 /\ sr_get (ss_regs S_FBfF) 8%bv = SOff 180 0 /\ sr_get (ss_regs S_FBtF) 10%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_FBfF) 10%bv = SOff A_BUF 0
/\ ss_resv S_FBtF = None /\ ss_resv S_FBfF = None /\ ss_mem S_FBtF = CM_memF /\ ss_mem S_FBfF = CM_memF.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma fb_checksF : ss_atoms_lt K_FB S_FBtF = true /\ ss_atoms_lt K_FB S_FBfF = true /\ regions_wf (WIN (-128) :: rs_FBF) = true /\ no_cdata rs_FBF = true
/\ mem_atoms_lt K_FB (WIN (-128) :: rs_FBF) = true /\ forallb (drv_keep_ok (-128)) rs_FBF = true /\ rs_FBF = List.filter gkeep CM_memF /\ skipn 2 rs_FBF = IMG_LF.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_XTF_facts : ss_pc S_XTtF = A_XT /\ ss_pc S_XTfF = A_XT /\ sr_get (ss_regs S_XTtF) 10%bv = SLit 0 /\ sr_get (ss_regs S_XTfF) 10%bv = SOff 180 0
/\ sr_get (ss_regs S_XTtF) 2%bv = SOff 0 (-48) /\ sr_get (ss_regs S_XTfF) 2%bv = SOff 0 (-48)
/\ ss_mem S_XTtF = WIN (-128) :: rs_FBF /\ ss_mem S_XTfF = WIN (-128) :: rs_FBF /\ ss_resv S_XTtF = None /\ ss_resv S_XTfF = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma wbs_FBF : wr_below_sp (ss_facts S_FBtF) CM_memF = true /\ wr_below_sp (ss_facts S_FBfF) CM_memF = true
/\ wr_below_sp (ss_facts S_XTtF) (WIN (-128) :: rs_FBF) = true /\ wr_below_sp (ss_facts S_XTfF) (WIN (-128) :: rs_FBF) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_FBrF_win_ok : forallb drv_win_ok (WIN (-128) :: rs_FBF) = true. Proof. vm_compute. reflexivity. Qed.
Lemma S_FBrF_eq : drv_after S_FBtF rs_FBF K_FB RA_FB (-128) = S_FBrtF /\ drv_after S_FBfF rs_FBF K_FB RA_FB (-128) = S_FBrfF.
Proof. vm_compute. split; reflexivity. Qed.
Lemma S_XTF_regs : sr_get (ss_regs S_XTtF) 3%bv = SLit 67584 /\ sr_get (ss_regs S_XTfF) 3%bv = SLit 67584
/\ sr_get (ss_regs S_XTtF) 4%bv = SLit 6132848 /\ sr_get (ss_regs S_XTfF) 4%bv = SLit 6132848.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma CM_so_okF : forallb so_win_ok CM_memF = true /\ forallb so_win_ok (WIN (-128) :: rs_FBF) = true /\ forallb so_win_ok L_memF = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma IMG_LF_wf : regions_wf IMG_LF = true. Proof. vm_compute. reflexivity. Qed.

(* ---- what the clip leaves out, and nothing more ---- *)
Definition gf_avoid (lo hi : Z) : bool := forallb (fun iv => (hi <=? fst iv) || (snd iv <=? lo)) GF_IVS.
Definition region_gf_ok (r : YP09.region) : bool :=
  ((r_hi r <=? r_lo r) || match r_base r with None => gf_avoid (r_lo r) (r_hi r) | Some _ => true end)%bool.
(* no absolute region of either view reaches a byte of G_fr_c *)
Lemma views_gf_ok : forallb region_gf_ok IMG_LF = true /\ forallb region_gf_ok IMG_LCF = true /\ forallb region_gf_ok L_memF = true /\ forallb region_gf_ok CM_memF = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma gf_avoid_sound : forall lo hi a, gf_avoid lo hi = true -> lo <= a < hi -> ~ Exists (YG0n.in_zr a) GF_RANGES.
Proof.
intros lo hi a H Ha Hx. apply Exists_exists in Hx as (r & Hr & Hz). unfold gf_avoid in H. rewrite forallb_forall in H.
specialize (H (fst r, fst r + snd r) ltac:(apply in_map_iff; exists r; split; [reflexivity | exact Hr])).
cbn [fst snd] in H. unfold YG0n.in_zr in Hz. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
