(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the PROOF of runqm_cf_B (lib/AU/PresetD2eB.v, lane CwRunqm's RUNQM for the asan-ubsan image:
   the driver's arm from the payload malloc to the loop head). Nothing in this file is a proof of a function (rule 24:
   the composition / driver layer of a port).
   This file is section 3 of lib/AU/PresetD2eB.v (lines 183-633 at a working branch a4c03c09af1), MOVED BYTE
   FOR BYTE, with no proof change (a Theorem Labs lane, the parent's order 2026-10-29): PresetD2eB.v keeps the header,
   sections 0-2 (the P8 driver leaf iface_room_at_driver, the leaf type run_QM_tfa_cf and the statement runqm_cf_B),
   so that the driver composition (lib/AU/PresetD1pBPf.v) can cite the statement without this proof. The import block
   below is PresetD2eB.v's own (its lines 34-68), then PresetD2eB itself and its local CfParams instance (its :168).
   It is the twin of lib/A/PresetD2eAPf.v (the same split of the internal file a2b.py twin files).
   memnorm (a Theorem Labs lane MnPrefix, 2026-10-29): CwSites' tail_at_pinv_B ends with memnorm of the full overlay, and the
   loop body PresetD1rB.loop_L_cf_B takes `YAkMemnorm.memnorm tfibsegs (ms_mem ms)` at the loop head. The proof
   carries it: the payload malloc keeps it (malloc_leaf_cf's last conjunct), pc_run / pl_run are re-run by their
   memnorm twins (lib/Reusable/YD2mnSeg.v pc_run_mn / pl_run_mn at P := YAkMemnorm.memnorm tfibsegs, laws
   YSRrMemnorm.srr_inv_laws_memnorm_k), the memcpy site keeps it (memcpy_site_tfa_cf's last conjunct), and the hand
   steps (drv_after_call_w, st_ok_add_cond, pc_reseat, pl_to_L) do not change the memory. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1v YD1y YD26 YD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD21 YD25 YD23 YD2h YD1w YD2f YD2b YD2g YD1s YD2c YD2d YD29.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfRoomPre YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YGcfPath YGcfXs YG0lawscf YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2mnSeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetStkUpB.
(* The run-level room is a Theorem Labs lane's P8 (a working branch 4ec915e66b6, lib/Spec/PresetP8.v): the state
   predicate room_at, not a sum over calls. a8's view of an astate (room_of_cf, q_fifo) is YGcfRoom.v, its free
   coupling YGcfFrees.v (a working branch 5d91379f2041); the model's run (hruns, hlive, hfrees) is
   lib/Spec. Names used qualified. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfFrees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetRun PresetReqAt.
From Stdlib Require Import Sorting.Permutation.
(* The owners' statements and lemmas (a Theorem Labs lane's one-writer table). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB PresetD1rBx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1rB PresetPinvB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetDrvHull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetDrvAroB.
(* Required, not imported: PresetCfnB defines A_LLVMF / RA_LLVMF / A_EMPTY / LIVE_LIB / LLVMF_STK at preset's values,
   which would shadow the driver's names; its names are written qualified. *)
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the statement file (sections 0-2 of the former PresetD2eB.v) and its local CfParams instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD2eB.
#[local] Existing Instance CfParamsPreset.CfParams_preset.

(* ---------------------------------------------------------------------- *)
(* 3. The proof.                                                           *)

(* Every class-full arm of a pristine primary class has room: the refill target max_cached c / 2 entries of class c
   fit in the class's user map. *)
Lemma pristine_fits : forall c, 1 <= c <= 30 ->
round_up (YGcfPath.cf_need init_state c * class_size c) kUserMapSize <= kFreeArrayOffset.
Proof.
intros c Hc. assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
repeat (destruct H as [-> | H]; [apply Z.leb_le; vm_compute; reflexivity |]).
subst c. apply Z.leb_le. vm_compute. reflexivity.
Qed.

(* Before the first harness call every primary class but the batch class is pristine (tail_at's drv_minv_cf), so a
   malloc_cf of any size has room (YGcfPath.v room_cf). *)
Lemma room_cf_of_pristine : forall n S, prim_pristine_except S [kBatchClass] -> YGcfPath.room_cf n S.
Proof.
intros n S HP. unfold YGcfPath.room_cf. destruct (from_primary n) eqn:Fp; [right | left; reflexivity].
pose proof (YGcfPath.chunk_class_ok n Fp) as Hc. unfold YGcfPath.room_at.
destruct (Z.eq_dec (chunk_class n) kBatchClass) as [E|E]; [left; exact E|]. right; right; right.
destruct (HP (chunk_class n) ltac:(lia) ltac:(cbn [In]; intros [X|[]]; apply E; symmetry; exact X)) as (M & A & F & _).
destruct (pristine_init (chunk_class n) ltac:(lia) ltac:(intros [])) as (_ & _ & F0 & _).
assert (Ecn : YGcfPath.cf_need S (chunk_class n) = YGcfPath.cf_need init_state (chunk_class n))
by (unfold YGcfPath.cf_need; rewrite F, F0; reflexivity).
unfold YGcfPath.arm_fits. rewrite M, A, Ecn. right. rewrite !Z.add_0_l, Z.sub_0_r.
exact (pristine_fits _ Hc).
Qed.

Section e.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg}.
Variable B : asyms.
Variable NP : astate -> Prop.
Variable NR : ProcInput -> Prop.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
(* the harness model's size map, as the interface and the loop take it *)
Variable sm : list Z -> Z * Z.
Hypothesis HFRM : YK0o.frm_zero (@YK11.fp_csr fx).
Hypothesis HB : TfibSyms B.
Hypothesis MSITE : malloc_site_tfa_cf B NP.
Hypothesis MCPY : memcpy_site_tfa_cf B.
Hypothesis LOOPL : PresetD1rB.loop_L_cf_B (LS := LS) B xst NR sm NP.
(* the wild room of the instance's universe covers the loop's four calls (YL04.calls_bound): true by conversion at
   TfibB (u_wmax Tfib_universe, IfaceReview 00:5xZ) *)
Hypothesis HWMAX : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat.
(* The interface's own two laws for the non-primary room (lib/AU/PresetCfnB.v section 3b). P8's side is NOT a
   hypothesis: iface_room_at_driver above proves it at this layer's states. *)
Hypothesis HNPT : PCB.iface_room_np_tail NP.
Hypothesis HNPS : PCB.iface_room_np_step NP.
(* Lane CwPinvB's PINV frame results, by statement (lib/AU/PresetPinvB.v). *)
Hypothesis PRUN : PresetPinvB.finv_run_pinv_B.
Hypothesis PSITE : PresetPinvB.finv_site_pinv_B.
Hypothesis PICPT : PresetPinvB.finv_icpt_pinv_B.

(* The error buffer's extent, placed, is below the ceiling and off the image: it misses ly_img (a static extent),
   which covers every segment (ALedger_cf's alc_img). *)
Lemma xs_cf_off_img : forall ly S Hp (W : world tfibsegs) mem md a,
ARcf tfibsegs B ly S Hp W mem md -> xs_placed_cf ly S -> Exists (in_zr a) (xs_cf ly S) ->
a < alloc_ceiling /\ ~ YG0d.in_img tfibsegs a.
Proof.
intros ly S Hp W mem md a HAR HX Ha.
destruct (YGcfXs.cfx_pick ly S a HX Ha) as (e & He & _ & Hce & Hdj).
unfold in_zr in He. split; [lia|].
intros (sg & Hsg & Hb).
pose proof (proj1 (proj2 HAR)) as LG.
assert (I : fst (ly_img ly) <= Z.of_N (seg_base sg) /\
Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly)) by (eapply alc_img; eassumption).
assert (Hz : In (ly_img ly) (sec_extents ly S ++ static_extents ly ++ ly_extra ly)).
{ apply List.in_or_app. right. apply List.in_or_app. left. unfold static_extents.
apply List.in_or_app. right. right. left. reflexivity. }
pose proof (Hdj _ Hz) as D. unfold zdisjoint in D. lia.
Qed.

(* Lane CwLoopB's lemmas over ARcf (lib/AU/PresetD1rBx.v, YD1y.v:101 / :309, YCe5.v:322 / :1518, YD25.v:685 / :694),
   at this image, with a8's AR_laws_ok_cf. *)
Lemma AR_after_run_w : forall ly S Hp (W : world tfibsegs) E rs (mem mem' : word -> option byte) md mat,
ARcf tfibsegs B ly S Hp W mem md ->
forallb drv_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) -> YM05.ceil_of_top (bv_unsigned (ew E 0) - stack_max_size) ->
frame_of E rs mem mem' ->
(forall a, bv_unsigned (ew E 0) - 65536 <= a < bv_unsigned (ew E 0) -> mem' (Z_to_bv 64 a) <> None) ->
ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros. pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL. eapply AR_after_run_cf; eassumption. Qed.

Lemma drv_after_call_w : forall k E ss ms ly S Hp (W : world tfibsegs) md (Eb : Z -> Prop) ly' S' W' regs' mem' md' rs retpc usp spo,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (WIN spo :: rs) = true -> no_cdata rs = true -> mem_atoms_lt k (WIN spo :: rs) = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc ->
acall_post_cf tfibsegs B ASTACK ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W (ms_mem ms) md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ (ms_regs ms) = usp + spo -> -4096 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
(forall a, usp - 65536 <= a < usp + spo -> apresent (w_H W) (ms_mem ms) a) ->
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (drv_after ss rs k retpc spo)
(restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))).
Proof. intros. pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL. eapply drv_after_call_cf; eassumption. Qed.

Lemma sep_blocks_w : forall ly S Hp (W : world tfibsegs) mem md b m p n,
ARcf tfibsegs B ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
zdisjoint (b, req_size m) (p, req_size n).
Proof. intros. pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL. eapply sep_blocks_cf; eassumption. Qed.

Lemma amem_range_of_block_w : forall ly S Hp (W : world tfibsegs) mem md p m a n,
ARcf tfibsegs B ly S Hp W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> amem_range a n.
Proof. intros. pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL. eapply amem_range_of_block_cf; eassumption. Qed.

Lemma range_addressable_of_block'_w : forall ly S (W : world tfibsegs) mem md q m a n,
ARcf tfibsegs B ly S [] W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> a + n <= q + req_size m ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n.
Proof. intros. pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL. eapply range_addressable_of_block'_cf; eassumption. Qed.

Lemma shadow_hull_vis_of_block'_w : forall ly S Hp (W : world tfibsegs) mem md q m d n,
ARcf tfibsegs B ly S Hp W mem md -> In (q, m) (ablocks B ly S) -> q <= d -> d + n <= q + req_size m -> 0 < n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Proof. intros. pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL. eapply shadow_hull_vis_of_block'_cf; eassumption. Qed.

Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).

Theorem runqm_at : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
NR inp ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data -> 0 < payload_len data ->
let E3 := E_P (edset (havoc EL K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at_pinv_B B NP (if config_len data =? 0 then sPM0 else sPM1 (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap HNRi Hlk Hok Hplpos E3 HT HUP0 E60.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HNP & HTOP & Hbl & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HFI & HXS & HMN0).
pose proof (YG0lawscf.AR_laws_ok_cf tfibsegs B) as ARL.
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
(* the instance's one-call ROOM_cf S, drawn from the interface's non-primary room; a8's success lemma for the
   payload malloc below takes its three parts *)
pose proof (YGcfRoomKeep.RK_room S 2 (HNPT S HNP)) as HROOM.
pose proof Hminv as HMV.
(* the hull at the payload malloc's entry (A18's base: drv_secs_cf in drv_minv_cf at 65536 <= cap <= 2 ^ 26), for
   drv_pre_cf's hull conjunct *)
pose proof (proj1 (PresetDrvHull.drv_cf_hull_ok_drv_preset S cap (proj2 (proj2 (proj2 (proj2 (proj2 Hminv))))) Hcap))
  as HHO.
destruct Hminv as (_ & HPRI & HfrS & HqtS & HDF & _).
pose proof (room_cf_of_pristine (payload_len data) S HPRI) as HRC.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof cf_malloc_max_ge as HMM. unfold MALLOC_MAX in HMM.
set (buf := sptr_addr B ly pb) in *. set (c0 := config_len data =? 0) in *. set (k := Z.of_nat (calls data)) in *.
set (ss := if c0 then sPM0 else sPM1 k) in *.
pose proof (config_len_bound data) as Hcl. pose proof (calls_bound data) as Hcb.
assert (Hpl : payload_len data = dlen data - 6 - config_len data) by reflexivity. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md _ _ HAR Hin) as (Hbufm & Hb4096 & Hbce & _ & Hpres0 & _).
assert (Hreq1 : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
rewrite Hreq1 in Hbce, Hpres0.
assert (NIMGB : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. rewrite <- Hreq1 in Ha. exact (proj2 (alc_client_img _ _ ARL ly S [] W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha)))))). }
assert (EL6' : usp <= bv_unsigned (ew EL 6)).
{ change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YP08.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz.
unfold z_rand in *. rewrite u64_lit by lia. lia. }
assert (E3old : forall j, (j < K_M1)%nat -> ew E3 j = ew EL j).
{ intros j Hj. subst E3. rewrite E_P_old by (unfold K_M1 in Hj; lia). cbn [ew edset]. apply ew_havoc_old. exact Hj. }
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (rewrite E3old by (unfold K_M1; lia); reflexivity).
assert (E3_6 : usp <= bv_unsigned (ew E3 6)) by (rewrite E3old by (unfold K_M1; lia); exact EL6').
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
assert (HWF : Wf_cf (as_universe B) S) by exact (amc_wf _ _ _ _ _ (proj1 HAR)).
assert (HWFP : WfP_cf (as_universe B) 0 0 0 S) by exact HWF.
assert (HUNI : universe_ok (as_universe B)) by exact (amc_universe _ _ _ _ _ (proj1 HAR)).
assert (Hbb : blocks_bytes S = cap) by (rewrite blocks_bytes_blocks, Hbl; cbn; lia).
assert (SUB : submem rsPM (ss_mem ss)) by (subst ss; rewrite <- (rs_PM_eq c0 k); exact (rs_PM_sub c0 k)).
rewrite Hshape, Hpc. change (Z_to_bv 64 A_wrap_malloc) with (w64 (pc_wrap_malloc Tfib_code)). rewrite <- (ts_code B HB).
fold regs mem. change (mkCfg (mkst regs (w64 (pc_wrap_malloc (as_code B))) mem (seg_rom tfibsegs)) md)
with (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md).
apply (MSITE ly S W regs mem md (payload_len data) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp))).
-
split; [exact HAR|]. split; [unfold top_ok in *; tauto|].
split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra; unfold RA_PM; lia|].
split; [rewrite Hsp'; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [unfold s0Z; rewrite R8; unfold w64; rewrite u64_lit by lia; lia|]. split; [exact HqtS|]. split; [exact HNP|].
(* field round 3's three call facts: the hull (HHO), the tail's memnorm (the state is the tail's), the read-only
   bytes off rsPM's image cells *)
split; [exact HXS|]. split; [exact HHO|]. split; [exact HMN0|].
exact (PresetDrvAroB.drv_arodata_mem B HB rsPM E3 (w_H W) mem ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  (mem_ok_sub tfibsegs E3 _ _ rsPM SUB ltac:(vm_compute; reflexivity) HM)).
- exact R10.
- lia.
- rewrite Hbb. unfold LIVE_MAX. lia.
- rewrite (ts_code B HB), Hra. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- exact HAI.
-
intros [p' S'] trc tr W' c' Htrc Hpath Hg HLEAF Hwle HAI2.
assert (Hnn' : p' <> PNull)
by exact (YGcfPath.malloc_cf_success_of_room (payload_len data) trc S tr (p', S') (YGcfPath.shape_cf_of_WfP_cf _ _ _ _ _ HWFP) Hpath Hg HRC).
destruct HLEAF as ((ly' & regs' & mem' & md2 & Hc' & HPOST & Ha0 & _ & _ & HXS' & _ & _) & HMNK). subst c'.
cbn [fst snd] in HPOST, Ha0, HXS'. cbn [cfg_model cfg_at] in HAI2.
(* the payload malloc keeps memnorm (the keep leaf's conjunct, YGcfMallocComposeKeep.malloc_leaf_cf_keep) *)
pose proof (HMNK (raZ regs) regs' mem' md2 eq_refl HMN0) as HMN1. clear HMNK.
unfold cfg_at. rewrite Hra.
pose proof HPOST as (HAR' & Hlyle & _ & HPres & Hio & Hfr' & Hsc').
destruct HROOM as (HR1 & HR2 & HR3).
destruct (malloc_cf_apath_success (as_universe B) S (payload_len data) trc tr p' S' HUNI HWF ltac:(lia)
ltac:(rewrite Hbb; unfold LIVE_MAX; lia) (YG01.admits_fix _ _ S HUNI Htrc) HR1 HR2 HR3 Hpath Hnn')
as (HWF' & Hnev' & _ & HfrM & Hbl' & Hfresh & HQT').
assert (XS : forall a, Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' S') -> a < alloc_ceiling /\ ~ YG0d.in_img tfibsegs a).
{ intros a Ha. apply Exists_exists in Ha as (e & He & Hz). apply in_app_or in He as [He|He].
- apply (xs_cf_off_img ly S [] W mem md a HAR HXS). apply Exists_exists. exists e. exact (conj He Hz).
- apply (xs_cf_off_img ly' S' [] W' mem' md2 a HAR' HXS'). apply Exists_exists. exists e. exact (conj He Hz). }
assert (Hblocks : blocks S' = [(pb, cap); (p', payload_len data)] /\ ~ In p' [pb]).
{ rewrite Hbl in Hbl', Hfresh. split; [exact Hbl' | exact Hfresh]. }
destruct Hblocks as [Hblocks Hp'].
(* The room the loop takes at S', in the state form: the interface's non-primary room, stepped across the payload
   malloc by the interface's iface_room_np_step, and P8's premise, which iface_room_at_driver reads off this leaf.
   The free history at S' is the quarantine itself: RUNQM frees nothing, so H0 is its own requests and the model's
   part is empty. No headroom is counted: the malloc site took its one-call ROOM_cf from NP S itself. *)
assert (Hbl3 : (length (blocks S') <= 3)%nat) by (rewrite Hblocks; cbn [length]; lia).
assert (HNP' : NP S') by exact (proj1 HNPS (as_universe B) S (payload_len data) trc tr p' S' HWF HqtS HNP
ltac:(rewrite Hbl; cbn [length]; lia) Hpath).
assert (HRAT' : exists os H0 hist, length os = 0%nat /\
PCB.iface_room_at sm (map (fun b : byte => bv_unsigned b) (payload data)) os H0 hist S')
by exact (iface_room_at_driver sm _ (as_universe B) S' HWF' (HQT' HqtS) Hbl3
(* A18: the driver's base after the payload malloc (a request below cap <= 2 ^ 26), from drv_minv_cf's count *)
(proj2 (drv_rp_base_B B S cap _ HMV Hcap) (payload_len data) trc tr p' S' ltac:(lia) Hpath)).
set (nb := sptr_addr B ly' p') in *.
assert (Etop : ly_top ly' = ly_top ly) by (destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
pose proof (alc_layout _ _ ARL ly S [] W mem md ly' HAR Hlyle) as (Habl & _ & _).
assert (Hpb' : sptr_addr B ly' pb = buf).
{ unfold ablocks in Habl. rewrite Hbl in Habl. cbn in Habl. injection Habl as Habl. rewrite Habl. reflexivity. }
assert (Hin1 : In (buf, cap) (ablocks B ly' S')) by (unfold ablocks; rewrite Hblocks; cbn; left; rewrite Hpb'; reflexivity).
assert (Hin2 : In (nb, payload_len data) (ablocks B ly' S')) by (unfold ablocks; rewrite Hblocks; cbn; right; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem' md2 _ _ HAR' Hin2) as (Hnb16 & Hnb4096 & Hnbce & _ & HpresN & _).
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem' md2 _ _ HAR' Hin1) as (_ & _ & _ & _ & HpresB & _).
assert (Hreq2 : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia).
rewrite Hreq2 in Hnbce, HpresN. rewrite Hreq1 in HpresB.
assert (NIMGN : forall a, nb <= a < nb + payload_len data -> ~ in_img tfibsegs a).
{ intros a Ha. rewrite <- Hreq2 in Ha. exact (proj2 (alc_client_img _ _ ARL ly' S' [] W' mem' md2 a HAR' (or_introl (ex_intro _ _ (ex_intro _ (payload_len data) (conj Hin2 Ha)))))). }
assert (Hsep : nb + payload_len data <= buf \/ buf + cap <= nb).
{ pose proof (sep_blocks_w ly' S' [] W' mem' md2 buf cap nb (payload_len data) HAR' Hin1 Hin2 ltac:(intros X; injection X; lia)) as X.
unfold zdisjoint in X. cbn [fst snd] in X. rewrite Hreq1, Hreq2 in X. lia. }
(* #102 (lane StackDrv): the live stack above usp across the payload malloc *)
assert (HUP1 : YGcallStackUp.astack_up_x tfibsegs ly' W' usp mem')
by exact (PresetStkUpB.stk_up_acall B ASTACK ly S [] W regs mem md _ ly' S' W' regs' mem' md2 usp HB ARL HPOST HAR
  ltac:(intros a [[_ Ha] | Ha]; [rewrite Hreq2 in Ha; lia | exact (proj1 (XS a Ha))]) ltac:(lia) HTOP HUP0).
pose proof (drv_after_call_w K_PM E3 ss ms ly S [] W md _ ly' S' W' regs' mem' md2 rsPM
RA_PM usp (-208) HS Hrv CK1 CK2 CK3 CK4 SUB ltac:(subst ss; destruct c0; [exact A1 | exact B1]) HPOST HAR
ltac:(intros a [[_ Ha] | Ha]; [rewrite Hreq2 in Ha; split; [lia | exact (NIMGN a Ha)] | exact (XS a Ha)])
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
(* pc_run, with memnorm on both ends (YD2mnSeg.pc_run_mn) *)
apply (SRr_srealizes tfibsegs W' _ _ _ (YD2mnSeg.pc_run_mn _ PLAW c0 k E2 W' regs' mem' md2 HS2 HMN1) HAI2).
intros W1 c1 _ HAI3 [HAT3 (msM3 & mdM3 & Ec3 & HMN3)]. destruct HAT3 as (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3.
injection Ec3 as <- <-.
rewrite (PMr_if c0 k) in HF3, HFr3.
(* #102: the live stack across pc_run (its frame is below usp) *)
assert (HUP3 : YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem ms3))
by exact (PresetStkUpB.stk_up_frame E2 (WIN (-208) :: rsPM) ly' W' mem' (ms_mem ms3) usp WOK E2_0 ltac:(lia)
  (top_ok_le _ _ _ _ Hlyle HTOP) HF3 HUP1).
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
assert (HAR3 : ARcf tfibsegs B ly' S' [] W' mem3 md3).
{ apply (AR_after_run_w ly' S' [] W' E2 (WIN (-208) :: rsPM) mem' mem3 md2 mat3 HAR' WOK); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HF3 |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin3 a Ha)). }
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem3 md3 _ _ HAR3 Hin2) as (_ & _ & _ & _ & HpresN3 & _). rewrite Hreq2 in HpresN3.
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem3 md3 _ _ HAR3 Hin1) as (_ & _ & _ & _ & HpresB3 & _). rewrite Hreq1 in HpresB3.
rewrite Hshape3, PCC. change (Z_to_bv 64 A_icpt_memcpy) with (w64 (pc_wrap_memcpy Tfib_code)). rewrite <- (ts_code B HB).
fold regs3 mem3. change (mkCfg (mkst regs3 (w64 (pc_wrap_memcpy (as_code B))) mem3 (seg_rom tfibsegs)) md3)
with (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs3 mem3 md3).
eapply (SRr_srealizes tfibsegs W' (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs3 mem3 md3)); [| exact HAI3 |].
{ apply (MCPY ly' S' W' regs3 mem3 md3 nb (buf + 6 + config_len data) (payload_len data)).
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
- apply (amem_range_of_block_w ly' S' [] W' mem3 md3 nb (payload_len data) nb (payload_len data) HAR3 Hin2); [lia | rewrite Hreq2; lia].
- apply (range_addressable_of_block'_w ly' S' W' mem3 md3 nb (payload_len data) nb (payload_len data) HAR3 Hin2); [lia | rewrite Hreq2; lia].
- intros Hn0. apply (shadow_hull_vis_of_block'_w ly' S' [] W' mem3 md3 nb (payload_len data) nb (payload_len data) HAR3 Hin2); [lia | rewrite Hreq2; lia | lia].
- lia.
- lia.
- intros a Ha. split; [apply (aview_some_of_apresent tfibsegs); exact (proj1 (HpresB3 a ltac:(lia)))|].
rewrite Hsp3. unfold sp_window_lo, ESTACK in *. lia.
- lia.
- apply (amem_range_of_block_w ly' S' [] W' mem3 md3 buf cap (buf + 6 + config_len data) (payload_len data) HAR3 Hin1); [lia | rewrite Hreq1; lia].
- apply (range_addressable_of_block'_w ly' S' W' mem3 md3 buf cap (buf + 6 + config_len data) (payload_len data) HAR3 Hin1); [lia | rewrite Hreq1; lia].
- intros Hn0. apply (shadow_hull_vis_of_block'_w ly' S' [] W' mem3 md3 buf cap (buf + 6 + config_len data) (payload_len data) HAR3 Hin1); [lia | rewrite Hreq1; lia | lia]. }
cbv beta. intros W2 c2 _ HAI4 (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hs4 & Ha04 & Hcpy & Hfr4 & Hpres4 & HMK4). cbn [cfg_model] in HAI4.
(* the memcpy site keeps memnorm (memcpy_site_tfa_cf's last conjunct) *)
pose proof (HMK4 HMN3) as HMN4. clear HMK4.
unfold cfg_at. rewrite Hra3. rewrite Hsp3 in Hfr4.
rewrite Hshape3, restrict_mkst_fx in HS3. fold regs3 mem3 in HS3.
assert (HNBC : nb + payload_len data <= alloc_ceiling) by lia.
pose proof (pc_reseat sp Hsp c0 k E2 W' regs3 _ mem3 regs4 mem4 nb (payload_len data) HS3 E2_0 E2_6 HP4 Hfr4 Hpres4 NIMGN HNBC HCT
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
(* #102: the live stack across the memcpy (its presence keep) *)
assert (HUP4 : YGcallStackUp.astack_up_x tfibsegs ly' W' usp mem4)
by exact (PresetStkUpB.stk_up_keep ly' ly' W' W' mem3 mem4 usp eq_refl (fun a _ => Hpres4 a) HUP3).
rewrite <- restrict_mkst_fx in HS5.
(* pl_run, with memnorm on both ends (YD2mnSeg.pl_run_mn); pc_reseat kept the memory mem4 *)
apply (SRr_srealizes tfibsegs W' _ _ _ (YD2mnSeg.pl_run_mn _ PLAW c0 k E4 W' regs4 mem4 md4 HS5 HMN4) HAI4).
intros W3 c3 _ HAI5 [HAT5 (msM5 & mdM5 & Ec5 & HMN5)]. destruct HAT5 as (-> & ms5 & mat5 & -> & HS6 & HF5 & HFr5). cbn [cfg_model] in HAI5.
injection Ec5 as <- <-.
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4) in *.
pose proof (PL_if c0 k) as (MPL & _ & _ & _ & _ & MPCr). rewrite MPCr in HF5, HFr5.
(* #102: the live stack across pl_run (its frame is below usp) *)
assert (HUP5 : YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem ms5))
by exact (PresetStkUpB.stk_up_frame E4 (WIN (-208) :: rsPM) ly' W' mem4 (ms_mem ms5) usp WOK E4_0 ltac:(lia)
  (top_ok_le _ _ _ _ Hlyle HTOP) HF5 HUP4).
pose proof (st_ok_mem_ok tfibsegs E4 _ _ HS6) as HM5. cbn [restrict ms_mem] in HM5. rewrite MPL in HM5.
assert (Hwin5 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem ms5) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem ms5) (WIN (-208) :: rsPL)); [exact HM5 | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem ms5) (WIN (-208) :: rsPL)); [exact HM5 | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem ms5) (WIN (-208) :: rsPL)); [exact HM5 | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HAR5 : ARcf tfibsegs B ly' S' [] W' (ms_mem ms5) md5).
{ apply (AR_after_run_w ly' S' [] W' E4 (WIN (-208) :: rsPM) mem4 (ms_mem ms5) md4 mat5 HAR4 WOK); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HF5 |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin5 a Ha)). }
destruct (PL_img_facts B HB E4 (w_H W') (ms_mem ms5) HM5) as [HIMG5 HRO5].
pose proof (pl_to_L c0 k E4 W' ms5 (payload_len data) nb HS6 UPL4 ltac:(lia) U83_4 Hnb4096 ltac:(lia) Hk Hk1) as (HSL & V61 & V62 & V63 & V65 & ELold).
set (E6 := E_L E4 (ms_regs ms5)) in *.
assert (HBLK' : blk (w_H W') mem' buf (Z.of_nat (length data)) data).
{ apply (blk_copy (w_H W) (w_H W') mem mem' buf buf (Z.of_nat (length data)) data); [| exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact HBLK].
intros i Hi. apply Hfr'.
- lia.
- exact (proj2 (Hpres0 (buf + i) ltac:(lia))).
- exact (proj2 (HpresB (buf + i) ltac:(lia))).
- apply (not_ascratch B HB ASTACK regs (buf + i) (usp + -208) Hsp'); [apply NIMGB; lia | lia | unfold ASTACK; lia].
(* the malloc's frame exceptions: the new block (disjoint from the read buffer) and the error buffer's extents,
   which no block meets (a8's block_not_xs_cf, lib/Reusable/YGcfXs.v, at S and at S') *)
- intros [[_ X2] | X].
  + rewrite Hreq2 in X2. lia.
  + apply Exists_app in X as [X|X].
    * exact (YGcfXs.block_not_xs_cf tfibsegs B ly S [] W mem md buf cap (buf + i) HAR HXS Hin
        ltac:(rewrite Hreq1; lia) X).
    * exact (YGcfXs.block_not_xs_cf tfibsegs B ly' S' [] W' mem' md2 buf cap (buf + i) HAR' HXS' Hin1
        ltac:(rewrite Hreq1; lia) X). }
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
assert (HFI5 : PCB.PINV (aview tfibsegs (w_H W') (ms_mem ms5)) 0 0).
{ assert (HFIm : PCB.PINV (aview tfibsegs (w_H W') mem') 0 0).
{ apply (PSITE fx rc ci CfParamsPreset.CfParams_preset B HB ARL ASTACK ly S [] W regs mem md _ ly' S' W' regs' mem' md2 usp 0 0 HAR HPOST);
[| exact HTOP | exact Ulo | exact Uhi | rewrite Hsp'; lia | unfold ASTACK; lia | exact HFI].
intros a [[_ Ha] | Ha]; [right; left; exists nb, (payload_len data); exact (conj Hin2 Ha) | right; right; exact (proj2 (XS a Ha))]. }
assert (HFI3 : PCB.PINV (aview tfibsegs (w_H W') mem3) 0 0)
by exact (PRUN (w_H W') E2 (WIN (-208) :: rsPM) _ _ usp 0 0 HFr3 WOK E2_0 Ulo HFIm).
assert (HFI4 : PCB.PINV (aview tfibsegs (w_H W') mem4) 0 0).
{ apply (PICPT fx rc ci CfParamsPreset.CfParams_preset B HB ARL ly' S' [] W' mem3 md3 mem4 (fun a => nb <= a < nb + payload_len data) (usp - 208 - ESTACK) (usp - 208) usp 0 0 HAR3 HTOP' Ulo Uhi Hfr4); [unfold ESTACK; lia | lia | | exact HFI3].
intros a Ha. exists nb, (payload_len data). split; [exact Hin2 | rewrite Hreq2; lia]. }
exact (PRUN (w_H W') E4 (WIN (-208) :: rsPM) _ _ usp 0 0 HFr5 WOK E4_0 Ulo HFI4). }
assert (Hfds5 : m_fds md5 = APSG.fds_std) by (subst md5; rewrite wvb_fds', Hfds4; subst md3; rewrite wvb_fds', Efds; exact Hfds).
assert (Hfs5 : m_fs md5 = in_fs inp) by (subst md5; rewrite wvb_fs', Hfs4; subst md3; rewrite wvb_fs', Efs; exact Hfs).
change (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)) with (loop_tgt (LS := LS) (payload data) (calls data) 0%nat (calls data) (in_fs inp)).
apply (LOOPL fx HFRM sp inp xw xd E6 W' ms5 md5 ly' S' a0 p data pb p' cap nb 0%nat (calls data) (in_fs inp) 0 0 Hargv Hsp Hva Hve Hvfs HNRi Hlk ltac:(unfold dlen; lia)).
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
+ right. split; [lia|]. split; [exact Hblocks | reflexivity].
+ intros _. exact HPL5.
+ rewrite HfrM. exact HfrS.
+ exact (HQT' HqtS).
(* the loop's room, in the state form: a8's non-primary room and P8's room_at, no headroom number *)
+ exact HNP'.
(* the loop entry's wild room: the payload malloc's trace is fixed, so the depot stays fixed (YGcfDepotStep.v) *)
+ apply (drv_wild_room_entry B S'); [exact (drv_depot_fixed_malloc B (payload_len data) trc S tr p' S' HDF Htrc Hpath) |
  apply (Nat.le_trans _ (4 * YCbqGwild.K_LLVMF)); [apply Nat.mul_le_mono_r; pose proof (calls_bound data); lia | exact HWMAX]].
+ exact HRAT'.
+ exact HXS'.
+ exact HAI5.
+ exact HAR5.
+ exact HTOP'.
+ unfold PCB.LCNT, PCB.SIZE_MAX. lia.
+ exact Hcap.
+ unfold dlen. lia.
+ left. split; [reflexivity | exact HIMG5].
+ exact HRO5.
+ exact HFI5.
(* the loop head's memnorm (PresetD1rB.v:142), from pl_run_mn's post *)
+ exact HMN5.
(* #102: the loop's stack invariant, carried from the tail *)
+ exact HUP5.
+ split; [intros k0; rewrite Hfds5; reflexivity|]. split; [exact Hfs5 | exact (proj1 Hvfs)].
Qed.

End e.

Theorem runqm_cf_B_holds : runqm_cf_B.
Proof.
intros fx rc LS ci B NR xst NP sm HNPT HNPS PRUN PSITE PICPT HFRM HB MSITE MCPY LOOPL HWMAX.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs HNRi Hlk Hok Hpl E3 HT HUP0 E60.
exact (runqm_at B NP NR xst sm HFRM HB MSITE MCPY LOOPL HWMAX HNPT HNPS PRUN PSITE PICPT
sp inp xw xd a0 p Hargv Hsp Hva Hve Hvfs ws W ms md ly S data pb cap HNRi Hlk Hok Hpl HT HUP0 E60).
Qed.

Print Assumptions runqm_cf_B_holds.
