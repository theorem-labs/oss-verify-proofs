(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK14 YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YD2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1v AD1y AD2a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Lemma ss_m1_win_ok : forallb drv_win_ok (ss_mem ss_m1) = true. Proof. reflexivity. Qed.
Lemma ss_m1r_win_ok : forallb drv_win_ok (ss_mem ss_m1r) = true. Proof. reflexivity. Qed.
Lemma wbs_m1c : wr_below_sp (ss_facts ss_m1c) (ss_mem ss_m1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wbs_oom1 : wr_below_sp (ss_facts ss_oom1) (ss_mem ss_m1r) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wbs_rd0 : wr_below_sp (ss_facts ss_rd0) (ss_mem ss_m1r) = true. Proof. vm_compute. reflexivity. Qed.
Lemma m1_checks : ss_atoms_lt K_M1 ss_m1c = true /\ regions_wf (WIN (-128) :: rs_m1) = true /\ no_cdata rs_m1 = true
/\ mem_atoms_lt K_M1 (WIN (-128) :: rs_m1) = true /\ forallb (drv_keep_ok (-128)) rs_m1 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma ss_m1r_eq : drv_after ss_m1c rs_m1 K_M1 0x80044 (-128) = ss_m1r. Proof. vm_compute. reflexivity. Qed.
Lemma img_regions_wf : regions_wf IMG_REGIONS = true. Proof. reflexivity. Qed.
Lemma submem_refl : forall rs, submem rs rs.
Proof. induction rs as [|r rs IH]; [constructor|]. apply submem_keep; [|exact IH]. repeat split; try lia. auto. Qed.
Lemma submem_filter : forall (f : YP09.region -> bool) rs, submem (List.filter f rs) rs.
Proof.
induction rs as [|r rs IH]; cbn; [constructor|].
destruct (f r); [apply submem_keep; [repeat split; try lia; auto | exact IH] | apply submem_drop; exact IH].
Qed.
Lemma keep_drv_submem : forall cut r rs, submem (keep_drv cut (r :: rs)) (r :: rs).
Proof. intros cut r rs. cbn. apply submem_keep; [apply subregion_trim_lo | apply submem_filter]. Qed.
Lemma rs_m1_sub : submem rs_m1 (ss_mem ss_m1c).
Proof.
change rs_m1 with (keep_drv (-128) (ss_mem ss_m1c)).
lazymatch goal with |- submem _ (?r :: ?rs) => exact (keep_drv_submem (-128) r rs) | |- submem _ ?m =>
let v := eval hnf in m in change m with v; lazymatch v with ?r :: ?rs => exact (keep_drv_submem (-128) r rs) end end.
Qed.
Lemma img_sub_oom1 : submem IMG_REGIONS (ss_mem ss_oom1).
Proof. change (ss_mem ss_oom1) with ([WIN (-128)] ++ (firstn 2 rs_m1) ++ IMG_REGIONS). do 3 apply submem_drop. apply submem_refl. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section M1.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MSITE : malloc_site_tfa B.
Hypothesis RDF : rd0_file_tfa B.
Hypothesis RDD : rd0_dir_tfa B.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp [a0; p] (in_envp inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma EL0 : bv_unsigned (ew EL 0) = usp. Proof. reflexivity. Qed.
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YP08.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma usp_facts : sp_window_lo <= usp <= sp_window_hi /\ usp mod 16 = 0.
Proof. destruct Hsp as (A & B0 & C). auto. Qed.
Lemma win_present : forall E (H : word -> bool) mem rs lo hi wlo whi cs,
mem_ok tfibsegs E (mrestrict H mem) rs -> In (YP09.mkRegion (Some 0%nat) lo hi wlo whi cs) rs -> bv_unsigned (ew E 0) = usp ->
-65536 <= wlo -> whi <= 65536 ->
forall a, usp + wlo <= a < usp + whi -> apresent H mem a.
Proof.
intros E H mem rs lo hi wlo whi cs (_ & HR & _) Hin E0' Hwlo Hwhi a Ha. pose proof usp_facts as [[_ U] _]. unfold sp_window_hi in U.
pose proof (proj1 (Forall_forall _ _) HR _ Hin) as (_ & _ & Wr & _). cbn [r_base r_wlo r_whi base_val] in Wr. rewrite E0' in Wr.
pose proof usp_facts as [[L _] _]. unfold sp_window_lo in L. pose proof (u64_range sp).
apply apresent_of_writable; [lia|]. replace a with (usp + (a - usp)) by lia. apply Wr. lia.
Qed.
Lemma apresent_some : forall (H : word -> bool) mem a, apresent H mem a -> mem (Z_to_bv 64 a) <> None.
Proof. intros H mem a [_ [b Hb]]. rewrite Hb. discriminate. Qed.
Definition at_m1c (W : world tfibsegs) (ms : machine_state) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs EL ss_m1c (restrict (w_H W) ms')
/\ frame_of EL (ss_mem ss_m1) (ms_mem ms) (ms_mem ms')
/\ frame_of EL (ss_mem ss_m1) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')).
Lemma m1c_run : forall (W : world tfibsegs) ms md,
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) -> SRr tfibsegs W (mkCfg ms md) (at_m1c W ms md).
Proof.
intros W ms md HS. pose proof HWXi as HWX.
srr_run_with tfibtbl_drv_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma m1_refuse : forall trc, refusal_offered (malloc 65536 trc init_state).
Proof.
intros trc. unfold refusal_offered. eexists. eexists. eexists. split; [cbn; reflexivity|].
split; [reflexivity|]. split; [cbn; left; reflexivity|].
lazymatch goal with |- exists S', ?lhs = _ =>
let v := eval lazy in lhs in lazymatch v with IRet (PNull, ?S1) => exists S1; lazy; reflexivity end end.
Qed.
Definition at_after (ss ss' : sstate) (E2 : YP0m.env) (W : world tfibsegs) (mem : word -> option byte) (md : Model)
: world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs E2 ss' (restrict (w_H W) ms')
/\ frame_of E2 (ss_mem ss) mem (ms_mem ms')
/\ frame_of E2 (ss_mem ss) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms')).
Lemma oom1_run : forall E2 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E2 (add_cond ss_m1r (mkAC Instr.BC_EQ (SOff A_BUF 0) (SLit 0))) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80044) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x80044) mem (seg_rom tfibsegs)) md)
(at_after (add_cond ss_m1r (mkAC Instr.BC_EQ (SOff A_BUF 0) (SLit 0))) ss_oom1 E2 W mem md).
Proof.
intros E2 W regs mem md HS. pose proof HWXi as HWX.
srr_run_with tfibtbl_drv_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma rd0_run : forall E2 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E2 (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80044) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x80044) mem (seg_rom tfibsegs)) md)
(at_after (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))) ss_rd0 E2 W mem md).
Proof.
intros E2 W regs mem md HS. pose proof HWXi as HWX.
srr_run_to_with tfibtbl_drv_ok HS A_RD.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Section d.
Variables (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (e : FdEntry).
Hypothesis HS1 : st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms).
Hypothesis HR1 : runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp).
Hypothesis HAI1 : AI tfibsegs (w_H W) (w_A W) md.
Hypothesis HAR1 : AR tfibsegs B ly init_state W (ms_mem ms) md.
Hypothesis HTOP1 : top_ok usp ly.
Hypothesis HFI1 : FINV ly (w_H W) (ms_mem ms).
Hypothesis Hfs1 : m_fs md = in_fs inp.
Hypothesis Hfds1 : m_fds md = APSG.fds3 e.
Lemma same_io_fs_fds : forall m m', same_io m m' -> m_fs m' = m_fs m /\ m_fds m' = m_fds m.
Proof. intros m m' (H1 & _ & H3 & _). unfold m_fs, m_fds. rewrite H1, H3. split; reflexivity. Qed.
Lemma wvb_fs' : forall l mat (m : Model), m_fs (with_vm_backing l mat m) = m_fs m.
Proof. intros l mat m. destruct m; reflexivity. Qed.
Lemma wvb_fds' : forall l mat (m : Model), m_fds (with_vm_backing l mat m) = m_fds m.
Proof. intros l mat m. destruct m; reflexivity. Qed.
Theorem m1_common : forall KB : TSet,
(forall ws (W' : world tfibsegs) ms1 md1 ly' S' (pb : sptr),
st_ok tfibsegs (havoc EL K_M1 ws) ss_rd0 (restrict (w_H W') ms1) ->
runs_at usp (mrestrict (w_H W') (ms_mem ms1)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W') (w_A W') md1 -> AR tfibsegs B ly' S' W' (ms_mem ms1) md1 -> top_ok usp ly' ->
blocks S' = [(pb, 65536)] -> pb <> PNull -> sptr_addr B ly' pb = bv_unsigned (ew (havoc EL K_M1 ws) A_BUF) -> st_nev S' <= 1 ->
prim_pristine_except S' [] -> quar_bytes S' = 0 -> frames S' = [] -> qtight S' ->
FINV ly' (w_H W') (ms_mem ms1) ->
m_fs md1 = in_fs inp -> m_fds md1 = APSG.fds3 e ->
srealizes tfibsegs (mkCfg ms1 md1) KB) ->
srealizes tfibsegs (mkCfg ms md) KB.
Proof.
intros KB CONT.
pose proof usp_facts as [[Ulo Uhi] U16]. pose proof (u64_range sp) as Usp. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof m1_checks as (CK1 & CK2 & CK3 & CK4 & CK5). pose proof (top_ok_ceil _ _ HTOP1) as HCT.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) (at_m1c W ms md) _ (m1c_run W ms md HS1) HAI1).
intros W0 c' _ HAI' (-> & ms' & mat & -> & HS & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EL ss_m1c ms' HS eq_refl) as Hshape.
set (regs := ms_regs ms') in *. set (mem := ms_mem ms') in *.
set (md' := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (R1 : getr regs 1%bv = w64 0x80044) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 1%bv HS); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 2%bv HS). eval_sr_get. cbn [sv_denot]. rewrite EL0. reflexivity. }
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 3%bv HS); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 4%bv HS); reflexivity).
assert (R8 : getr regs 8%bv = w64 2) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 8%bv HS); reflexivity).
assert (R10 : getr regs 10%bv = w64 65536) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 10%bv HS); reflexivity).
assert (Hsp' : spZ regs = usp + -128) by (unfold spZ; rewrite R2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = 0x80044) by (unfold raZ; rewrite R1; apply u64_lit; lia).
pose proof (st_ok_mem_ok tfibsegs EL ss_m1c _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. eapply (win_present EL (w_H W) mem (ss_mem ss_m1c)); [exact HM | left; reflexivity | exact EL0 | lia | lia | cbn; lia]. }
assert (HR : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame EL (ss_facts ss_m1c) (ss_mem ss_m1)); [exact (st_ok_facts_ok tfibsegs EL ss_m1c _ HS) | exact wbs_m1c | exact HFr | rewrite EL0; lia | exact HR1]. }
assert (HAR : AR tfibsegs B ly init_state W mem md').
{ apply (AR_after_run B HB ARL ly init_state W EL (ss_mem ss_m1) (ms_mem ms) mem md mat HAR1 ss_m1_win_ok); [rewrite EL0; exact Ulo | rewrite EL0; exact HCT | exact HF |].
rewrite EL0. intros a Ha. exact (apresent_some _ _ _ (Hwin a Ha)). }
rewrite Hshape. change (Z_to_bv 64 (ss_pc ss_m1c)) with (w64 (pc_wrap_malloc Tfib_code)). rewrite <- (ts_code B HB).
fold regs mem. change (mkCfg (mkst regs (w64 (pc_wrap_malloc (as_code B))) mem (seg_rom tfibsegs)) md')
with (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md').
apply (MSITE ly init_state W regs mem md' 65536 KB).
-
split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [cbn; unfold EV_MAX; lia|].
split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp'; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP1; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [| exact qtight_init]. unfold s0Z. rewrite R8. unfold w64. rewrite u64_lit by lia. lia.
- exact R10.
- unfold MALLOC_MAX. lia.
- change (blocks_bytes init_state) with 0. unfold LIVE_MAX. lia.
- rewrite (ts_code B HB), Hra. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- exact HAI'.
-
intros ly' S' W' regs' mem' md2 trc tr pb Hnn Htrc Hpath HPOST Ha0 Hwle HAI2.
unfold cfg_at. rewrite Hra.
pose proof HPOST as (HAR' & Hlyle & _ & HPres & Hio & _).
destruct (atok_apath _ _ _ tr _ (ml_malloc _ ML init_state 65536 trc (wf_init _) ltac:(cbn; unfold EV_MAX; lia)
ltac:(unfold MALLOC_MAX; lia) ltac:(change (blocks_bytes init_state) with 0; unfold LIVE_MAX; lia) Htrc) Hpath)
as (ns' & HMP). cbn [malloc_post] in HMP. destruct HMP as (HWF' & Hnev' & _ & Hfr0 & Hbl' & HQT').
assert (Hblocks : blocks S' = [(pb, 65536)]).
{ destruct pb; [exfalso; exact (Hnn eq_refl) | exact (proj1 Hbl') | exact (proj1 Hbl') | exact (proj1 Hbl')]. }
assert (Hin : In (sptr_addr B ly' pb, 65536) (ablocks B ly' S')).
{ unfold ablocks. rewrite Hblocks. left. reflexivity. }
pose proof (al_blocks _ _ ARL ly' S' W' mem' md2 _ _ HAR' Hin) as (_ & Hp4096 & Hpce & Hhigh & _).
pose proof (drv_after_call B HB ARL K_M1 EL ss_m1c ms' ly init_state W md' _ ly' S' W' regs' mem' md2 rs_m1
0x80044 usp (-128) HS eq_refl CK1 CK2 CK3 CK4 rs_m1_sub eq_refl HPOST HAR
ltac:(intros a Ha; split; [unfold req_size in Ha, Hpce; cbn in Ha, Hpce; lia
| exact (proj2 (al_client_img _ _ ARL ly' S' W' mem' md2 a HAR' (or_introl (ex_intro _ (sptr_addr B ly' pb) (ex_intro _ 65536 (conj Hin Ha))))))])
CK5 EL0 EL6 Hsp' ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin; lia)) as HS2.
rewrite ss_m1r_eq in HS2.
set (E2 := havoc EL K_M1 (map (getr regs') CLOB)) in HS2.
assert (A45 : ew E2 A_BUF = w64 (sptr_addr B ly' pb)).
{ subst E2. change A_BUF with (K_M1 + 4)%nat. rewrite (ew_havoc_new EL K_M1 _ 4 (w64 0)) by (cbn; lia). cbn. exact Ha0. }
assert (U45 : bv_unsigned (ew E2 A_BUF) = sptr_addr B ly' pb) by (rewrite A45; apply u64_lit; unfold req_size in Hpce; cbn in Hpce; lia).
apply (st_ok_add_cond tfibsegs _ _ _ Instr.BC_NE (SOff A_BUF 0) (SLit 0)) in HS2.
2:{ cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken]. rewrite Z.add_0_r, U45. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 (sptr_addr B ly' pb)) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by (unfold req_size in Hpce; cbn in Hpce; lia). lia. }
apply (SRr_srealizes tfibsegs W' _ _ _ (rd0_run E2 W' regs' mem' md2 HS2) HAI2).
intros W1 c1 _ HAI3 (-> & ms3 & mat3 & -> & HS4 & HF3 & HFr3). cbn [cfg_model] in HAI3.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite ew_havoc_old by (unfold K_M1; lia); exact EL0).
pose proof (st_ok_mem_ok tfibsegs E2 ss_rd0 _ HS4) as HM3. cbn [restrict ms_mem] in HM3.
destruct (same_io_fs_fds _ _ Hio) as [Efs Efds].
subst E2. apply (CONT (map (getr regs') CLOB) W' ms3 _ ly' S' pb HS4).
+
eapply (runs_at_frame _ (ss_facts ss_rd0) (ss_mem ss_m1r));
[exact (st_ok_facts_ok tfibsegs _ ss_rd0 _ HS4) | exact wbs_rd0 | exact HFr3 | rewrite E2_0; lia |].
unfold runs_at in HR |- *. apply Forall_forall. intros [a bs] Hab. pose proof (proj1 (Forall_forall _ _) HR _ Hab) as (Q1 & Q2 & Q3).
cbn [fst snd] in *. split; [exact Q1|]. split; [exact Q2|].
intros j Hj. rewrite <- (Q3 j Hj). unfold mrestrict.
pose proof HPOST as (_ & _ & _ & _ & _ & Hfr & _).
assert (Hav : aview tfibsegs (w_H W') mem' (a + Z.of_nat j) = aview tfibsegs (w_H W) mem (a + Z.of_nat j)).
{ apply Hfr.
- unfold sp_window_lo in Ulo. lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR X). pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR' X). pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. lia.
- unfold ascratch. rewrite Hsp', (ts_errno B HB). unfold TFIB_ERRNO. unfold sp_window_lo in Ulo. lia.
- intros [H1 H2]. pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. unfold req_size in H2, Hpce; cbn in H2, Hpce. lia. }
pose proof (mbyte_of_aview tfibsegs _ _ _ _ _ Hav) as Hmb. unfold mbyte, mrestrict in Hmb.
pose proof (Q3 j Hj) as Q. unfold mrestrict in Q.
destruct (w_H W (Z_to_bv 64 (a + Z.of_nat j))) eqn:Hh.
{ exfalso. destruct (nth_error bs j) eqn:En; [discriminate Q | apply nth_error_None in En; lia]. }
assert (Hh' : w_H W' (Z_to_bv 64 (a + Z.of_nat j)) = false).
{ destruct (w_H W' (Z_to_bv 64 (a + Z.of_nat j))) eqn:E'; [| reflexivity]. pose proof (Hwle _ E') as X. rewrite Hh in X. discriminate X. }
rewrite Hh' in Hmb |- *. rewrite Q in Hmb.
destruct (mem' (Z_to_bv 64 (a + Z.of_nat j))) as [b'|] eqn:Em'.
* destruct (nth_error bs j) as [b|] eqn:En; [cbn in Hmb; congruence | apply nth_error_None in En; lia].
* exfalso. destruct (nth_error bs j) as [b|] eqn:En; [| apply nth_error_None in En; lia].
rewrite (seg_rom_none tfibsegs) in Hmb; [discriminate Hmb | lia | apply not_in_img_high; unfold sp_window_lo in Ulo; lia].
+ exact HAI3.
+ apply (AR_after_run B HB ARL ly' S' W' (havoc EL K_M1 (map (getr regs') CLOB)) (ss_mem ss_m1r) mem' (ms_mem ms3) md2 mat3 HAR' ss_m1r_win_ok);
[rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HF3 |].
rewrite E2_0. intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
* apply (apresent_some (w_H W')). eapply (win_present _ (w_H W') (ms_mem ms3) (ss_mem ss_rd0)); [exact HM3 | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
* apply (apresent_some (w_H W')). eapply (win_present _ (w_H W') (ms_mem ms3) (ss_mem ss_rd0)); [exact HM3 | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
+ exact (top_ok_le _ _ _ _ Hlyle HTOP1).
+ exact Hblocks.
+ exact Hnn.
+ symmetry. exact U45.
+ rewrite Hnev'. cbn. lia.
+ exact (proj1 (pristine_malloc_sec 65536 trc init_state tr pb S' [] eq_refl Hpath pristine_init)).
+ rewrite (proj2 (pristine_malloc_sec 65536 trc init_state tr pb S' [] eq_refl Hpath pristine_init)). exact quar_bytes_init.
+ rewrite Hfr0. reflexivity.
+ exact (HQT' qtight_init).
+
assert (HFIc : FINV ly (w_H W) mem) by exact (finv_run B ly init_state W (ms_mem ms) md (w_H W) EL (ss_mem ss_m1) _ _ usp HAR1 HFr ss_m1_win_ok EL0 Ulo Uhi HTOP1 HFI1).
assert (HFIp : FINV ly' (w_H W') mem').
{ apply (finv_site B HB ARL ASTACK ly init_state W regs mem md' _ ly' S' W' regs' mem' md2 usp HAR HPOST); [| exact HTOP1 | exact Ulo | exact Uhi | rewrite Hsp'; lia | unfold ASTACK; lia | exact HFIc].
intros a Ha. right. exists (sptr_addr B ly' pb), 65536. exact (conj Hin Ha). }
exact (finv_run B ly' S' W' mem' md2 (w_H W') _ (ss_mem ss_m1r) _ _ usp HAR' HFr3 ss_m1r_win_ok E2_0 Ulo Uhi (top_ok_le _ _ _ _ Hlyle HTOP1) HFIp).
+ rewrite wvb_fs', Efs. subst md'. rewrite wvb_fs', Hfs1. reflexivity.
+ rewrite wvb_fds', Efds. subst md'. rewrite wvb_fds', Hfds1. reflexivity.
Qed.
End d.
Theorem tfib_file_arm_at : forall (W : world tfibsegs) ms md ly data,
valid_fs (in_fs inp) -> (length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md -> top_ok usp ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_loaded data (in_fs inp)).
Proof.
intros W ms md ly data Hvfs Hlen Hne Hnd Hlk HS HR HAI HAR HTOP HFI Hfs Hfds.
unfold CLOSEDX_loaded. apply (m1_common W ms md ly _ HS HR HAI HAR HTOP HFI Hfs Hfds).
intros ws W' ms1 md1 ly' S' pb HS1 HR1 HAI1 HAR1 HTOP1 Hbl Hnn Hpb Hnev HP1 HQ1 HF1 HT1 HFI1 Hfs1 Hfds1.
exact (RDF sp inp xw xd ws W' ms1 md1 ly' S' a0 p data pb Hargv Hsp Hva Hve Hvfs Hlen Hne Hnd Hlk HS1 HR1 HAI1 HAR1 HTOP1 Hbl Hnn Hpb Hnev HP1 HQ1 HF1 HT1 HFI1 Hfs1 Hfds1).
Qed.
Theorem tfib_dir_arm_at : forall (W : world tfibsegs) ms md ly,
p = dot_path ->
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md -> top_ok usp ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_dir p (in_fs inp)).
Proof.
intros W ms md ly Hdot HS HR HAI HAR HTOP HFI Hfs Hfds. unfold CLOSEDX_dir.
apply (m1_common W ms md ly _ HS HR HAI HAR HTOP HFI Hfs Hfds).
intros ws W' ms1 md1 ly' S' pb HS1 HR1 HAI1 HAR1 HTOP1 Hbl Hnn Hpb Hnev _ _ _ _ _ Hfs1 Hfds1.
exact (RDD sp inp xw xd ws W' ms1 md1 ly' S' a0 p pb Hargv Hsp Hva Hve Hfit Hdot HS1 HR1 HAI1 HAR1 HTOP1 Hbl Hpb Hnev Hfs1 Hfds1).
Qed.
End M1.
Theorem tfib_file_arm (B : asyms) (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) (ML : model_laws (as_universe B))
(MSITE : malloc_site_tfa B) (RDF : rd0_file_tfa B) : file_arm_tfa B.
Proof.
intros sp inp xw xd W ms md ly a0 p data Hargv Hsp Hva Hve Hvfs Hlen Hne Hnd Hlk HS HR HAI HAR HTOP HFI Hfs Hfds.
exact (tfib_file_arm_at B HB ARL ML MSITE RDF sp inp xw xd a0 p Hargv Hsp Hva Hve W ms md ly data Hvfs Hlen Hne Hnd Hlk HS HR HAI HAR HTOP HFI Hfs Hfds).
Qed.
Theorem tfib_dir_arm (B : asyms) (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) (ML : model_laws (as_universe B))
(MSITE : malloc_site_tfa B) (RDD : rd0_dir_tfa B) : dir_arm_tfa B.
Proof.
intros sp inp xw xd W ms md ly a0 p Hargv Hsp Hva Hve Hfit Hdot HS HR HAI HAR HTOP HFI Hfs Hfds.
exact (tfib_dir_arm_at B HB ARL ML MSITE RDD sp inp xw xd a0 p Hargv Hsp Hva Hve Hfit W ms md ly Hdot HS HR HAI HAR HTOP HFI Hfs Hfds).
Qed.
End c.
