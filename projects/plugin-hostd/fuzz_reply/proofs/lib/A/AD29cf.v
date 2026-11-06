(* copied from cgif_file lib/A/AD29.v by rules r1,r2,r3,r6,r9,rC, generator ed5c0821ce98f1d99fcd7466c0aa65f7671a8daf838ab8f2b2da9f5038f22ee4 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD29.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: over the cf allocator (ARcf); target_run's tail after the loop on A/AD2f_fp.v's clipped
   view (S_CMF and its run S_FBtF / S_FBfF / rs_FBF / S_XTtF / S_XTfF, which keep no byte of G_fr_c), the free's room
   ROOM_cf S and the hull admission cf_hull_ok S from the caller (the cf loop's tail-law accounting and run count),
   and Hp = [] for drv_pre. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1vcf AD1ycf AD26cf AD24cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD21 AD25cf AD2h AD1wcf AD2f AD1s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2f_fp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k AD1ucf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG01cf YG03dcf YG0dcf YG0ncf YG0ucf YGcfNames YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.
Hypothesis ML : model_laws_cf (as_universe B).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
(* route R: the world relation of the free step (A/AD1vcf.v free_site_tfa); the tail reads the free's post frame *)
Variable R : world tfibsegs -> world tfibsegs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle tfibsegs W W' -> R W W'.
Hypothesis FREE : free_site_tfa B R.
Hypothesis EXITL : exit_leaf_tfa B xst.
Hypothesis XFR : xst_frame_tfa xst.
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
(* field round 3 (Part A): the image fact behind the RELRO bytes' keep (A/AD1vcf.v relro_ok) *)
Hypothesis RO : relro_ok.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
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
Definition at_rs (rs : smem) (ss' : sstate) (E : YP0m.env) (W : world tfibsegs) (mem0 : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs E ss' (restrict (w_H W) ms')
/\ frame_of E rs mem0 (ms_mem ms')
/\ frame_of E rs (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms')).
Lemma fb_run : forall (cm : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_CMF (if cm then cond_CMt else cond_CMf)) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs CM_memF (if cm then S_FBtF else S_FBfF) E W (ms_mem ms) md).
Proof.
intros cm E W ms md HS. pose proof HWXi as HWX. destruct cm; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Lemma xt_run : forall (cm : bool) E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E (if cm then S_FBrtF else S_FBrfF) (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_FB) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_FB) mem (seg_rom tfibsegs)) md) (at_rs (WIN (-128) :: rs_FBF) (if cm then S_XTtF else S_XTfF) E W mem md).
Proof.
intros cm E W regs mem md HS. pose proof HWXi as HWX. destruct cm; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Theorem tfib_main_tail : forall E (W : world tfibsegs) ms md ly S Hp data (pb : sptr) cap (v : Z) (k : nat) (fs : Fs),
(forall j, (j < K_M1)%nat -> ew E j = ew EL j) -> ed E 2 = data -> (2 <= length data)%nat ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E 180) = v -> (v = 0 \/ v = 2) ->
st_ok tfibsegs E S_CMF (restrict (w_H W) ms) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp W (ms_mem ms) md -> Hp = [] -> top_ok usp ly ->
In (pb, cap) (blocks S) -> qtight S -> ROOM_cf S ->
(* field round 3: the free's hull admission (drv_pre's cf_hull_ok conjunct), from the caller's run count *)
cf_hull_ok S ->
so_state k (w_H W) (ms_mem ms) ->
(forall fd, fd_lookup (m_fds md) fd = fd_lookup APSG.fds_std fd) -> m_fs md = fs ->
(* field round 3 (Part A): the RELRO bytes, kept to the free's drv_pre by the driver's run *)
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex (if count_mode data then 0 else v) fs)).
Proof.
intros E W ms md ly S Hp data pb cap v k fs HEE HEd Hlen E41 E79 Hv HS HAI HAR HHp HTOP Hbl HQT HROOM HHU HSO Hfds Hfs HAD.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (buf := sptr_addr B ly pb) in *.
assert (E0' : bv_unsigned (ew E 0) = usp) by (rewrite HEE by (unfold K_M1; lia); reflexivity).
assert (E6' : usp <= bv_unsigned (ew E 6)) by (rewrite HEE by (unfold K_M1; lia); exact EL6).
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; apply in_map_iff; exists (pb, cap); split; [reflexivity | exact Hbl]).
pose proof (alc_blocks _ _ ARL ly S _ W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + req_size cap -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (alc_client_img _ _ ARL ly S _ W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha)))))). }
set (cm := count_mode data) in *.
assert (HS1 : st_ok tfibsegs E (add_cond S_CMF (if cm then cond_CMt else cond_CMf)) (restrict (w_H W) ms)).
{ pose proof (bltz_b1s E data HEd Hlen) as Hb. subst cm. destruct (count_mode data) eqn:Hcm.
- apply (st_ok_add_cond tfibsegs E S_CMF _ BC_LT sv_b1s (SLit 0) HS). exact Hb.
- apply (st_ok_add_cond tfibsegs E S_CMF _ BC_GE sv_b1s (SLit 0) HS). cbn [ac_c ac_a ac_b Sem.branch_taken].
cbn [Sem.branch_taken] in Hb. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). rewrite Hb. reflexivity. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (fb_run cm E W ms md HS1) HAI).
intros W0 c' _ HAI1 (-> & ms1 & mat1 & -> & HS2 & HF1 & HFr1). cbn [cfg_model] in HAI1.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
pose proof S_FBF_facts as (Pt & Pf & R1t & R1f & R2t & R2f & R8t & R8f & R10t & R10f & Rvt & Rvf & Mt & Mf).
assert (ss1 := if cm then S_FBtF else S_FBfF).
assert (Q : forall r vt vf, sr_get (ss_regs S_FBtF) r = vt -> sr_get (ss_regs S_FBfF) r = vf ->
getr (ms_regs ms1) r = sv_denot E (if cm then vt else vf)).
{ intros r vt vf Ht Hf. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E (if cm then S_FBtF else S_FBfF) ms1 r HS2). destruct cm; [rewrite Ht | rewrite Hf]; reflexivity. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E (if cm then S_FBtF else S_FBfF) ms1 HS2 ltac:(destruct cm; [exact Rvt | exact Rvf])) as Hshape.
set (regs := ms_regs ms1) in *. set (mem := ms_mem ms1) in *.
assert (R1 : getr regs 1%bv = w64 RA_FB) by (rewrite (Q 1%bv _ _ R1t R1f); destruct cm; reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -128)) by (rewrite (Q 2%bv _ _ R2t R2f); destruct cm; cbn [sv_denot]; rewrite E0'; reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E (if cm then S_FBtF else S_FBfF) ms1 3%bv HS2). destruct cm; reflexivity. }
assert (R4 : getr regs 4%bv = w64 TFIB_TP).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E (if cm then S_FBtF else S_FBfF) ms1 4%bv HS2). destruct cm; reflexivity. }
assert (R10 : getr regs 10%bv = w64 buf) by (rewrite (Q 10%bv _ _ R10t R10f); destruct cm; cbn [sv_denot]; rewrite Z.add_0_r, E41; reflexivity).
set (s0v := if cm then 0 else v).
assert (R8 : getr regs 8%bv = w64 s0v).
{ rewrite (Q 8%bv _ _ R8t R8f). subst s0v. destruct cm; cbn [sv_denot]; [reflexivity|]. unfold w64. rewrite Z.add_0_r, <- E79. reflexivity. }
assert (Hsp' : spZ regs = usp + -128) by (unfold spZ; rewrite R2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = RA_FB) by (unfold raZ; rewrite R1; apply u64_lit; unfold RA_FB; lia).
pose proof (st_ok_mem_ok tfibsegs E _ _ HS2) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (HMc : mem_ok tfibsegs E (mrestrict (w_H W) mem) CM_memF) by (destruct cm; [rewrite <- Mt | rewrite <- Mf]; exact HM).
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E (w_H W) mem CM_memF); [exact HMc | left; reflexivity | exact E0' | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem CM_memF); [exact HMc | right; left; reflexivity | exact E0' | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem CM_memF); [exact HMc | right; right; left; reflexivity | exact E0' | lia | lia | cbn; lia]. }
assert (HAR1 : ARcf tfibsegs B ly S Hp W mem md1).
{ apply (AR_after_run B HB ARL ly S _ W E CM_memF (ms_mem ms) mem md mat1 HAR (proj1 (proj2 (proj2 CM_memF_wf)))); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
assert (HSO1 : so_state k (w_H W) mem) by (exact (so_state_frame k (w_H W) E CM_memF _ _ HFr1 (proj1 CM_so_okF) ltac:(rewrite E0'; exact Ulo) ltac:(rewrite E0'; exact E6') HSO)).
assert (HAD1 : arodata_ok_cf tfibsegs B mem)
by exact (aro_run B W E CM_memF (ms_mem ms) mem RO HFr1 (proj1 (proj2 (proj2 CM_memF_wf))) ltac:(rewrite E0'; exact Ulo) HAD).
rewrite Hshape. fold regs mem.
replace (Z_to_bv 64 (ss_pc (if cm then S_FBtF else S_FBfF))) with (w64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); destruct cm; reflexivity).
change (mkCfg (mkst regs (w64 (pc_wrap_free (as_code B))) mem (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md1).
eapply (SRrG_srealizes tfibsegs _ W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md1)); [| exact HAI1 |].
{ apply (FREE ly S Hp W regs mem md1 pb cap).
- split; [exact HAR1|]. split; [unfold top_ok in *; tauto|]. split; [exact (conj HHp HROOM)|].
split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra; unfold RA_FB; lia|].
split; [rewrite Hsp'; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [| exact (conj HQT (conj HHU HAD1))]. unfold s0Z. rewrite R8. unfold w64. rewrite u64_lit by (subst s0v; destruct cm; lia). subst s0v; destruct cm; lia.
- exact Hbl.
- exact R10.
- rewrite (ts_code B HB), Hra. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto. }
cbv beta. intros W2 c2 Hwle2 HAI2 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6). cbn [cfg_model] in HAI2.
unfold cfg_at. rewrite Hra.
pose proof HPOST6 as (HAR6 & Hlyle6 & _ & HP6 & Hio6 & Hfr6 & Hsc6).
assert (Etop6 : ly_top ly6 = ly_top ly) by (destruct Hlyle6 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
pose proof fb_checksF as (FK1t & FK1f & FK2 & FK3 & FK4 & FK5 & FKeq & FKimg).
rewrite Hshape, restrict_mkst_fx in HS2. fold regs mem in HS2.
assert (SUB : submem rs_FBF (ss_mem (if cm then S_FBtF else S_FBfF))).
{ rewrite FKeq. destruct cm; [rewrite Mt | rewrite Mf]; apply submem_filter. }
rewrite <- restrict_mkst_fx, <- Hshape in HS2.
assert (HEb : forall a, buf <= a < buf + req_size cap -> a < alloc_ceiling /\ ~ in_img tfibsegs a).
{ intros a Ha. split; [lia | exact (NIMG a Ha)]. }
pose proof (drv_after_call B HB ARL K_FB E (if cm then S_FBtF else S_FBfF) ms1 ly S _ W md1 (fun a => buf <= a < buf + req_size cap)
ly6 S6 W2 regs6 mem6 md6 rs_FBF RA_FB usp (-128) HS2 ltac:(destruct cm; [exact Rvt | exact Rvf]) ltac:(destruct cm; [exact FK1t | exact FK1f])
FK2 FK3 FK4 SUB ltac:(destruct cm; [exact R1t | exact R1f]) HPOST6 HAR1 HEb
FK5 E0' E6' Hsp' ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin; lia)) as HS7.
assert (HS7' : st_ok tfibsegs (havoc E K_FB (map (getr regs6) CLOB)) (if cm then S_FBrtF else S_FBrfF) (restrict (w_H W2) (mkst regs6 (Z_to_bv 64 RA_FB) mem6 (seg_rom tfibsegs)))).
{ pose proof S_FBrF_eq as [Qt Qf]. destruct cm; [rewrite <- Qt | rewrite <- Qf]; exact HS7. }
clear HS7. set (E6 := havoc E K_FB (map (getr regs6) CLOB)) in *.
assert (E6old : forall j, (j < K_FB)%nat -> ew E6 j = ew E j) by (intros j Hj; subst E6; apply ew_havoc_old; exact Hj).
assert (E6_0 : bv_unsigned (ew E6 0) = usp) by (rewrite E6old by (unfold K_FB; lia); exact E0').
assert (HSO6 : so_state k (w_H W2) mem6).
{ apply (so_state_keep k (w_H W) (w_H W2) mem mem6); [| exact HSO1]. intros a Ha. apply Hfr6.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- exact (so_not_owned ly S _ W mem md1 a HAR1 Ha).
- exact (so_not_owned ly6 S6 _ W2 mem6 md6 a HAR6 Ha).
- unfold ascratch. rewrite Hsp', (ts_errno B HB). unfold TFIB_ERRNO, ASTACK. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold sp_window_lo in Ulo. lia.
- intros X. apply (NIMG a X). apply in_img_rw. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- apply ds_off_low. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia. }
apply (SRr_srealizes tfibsegs W2 _ _ _ (xt_run cm E6 W2 regs6 mem6 md6 HS7') HAI2).
intros W3 c3 _ HAI3 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI3.
pose proof S_XTF_facts as (Xt & Xf & A0t & A0f & SPt & SPf & XMt & XMf & XRt & XRf). pose proof S_XTF_regs as (G3t & G3f & G4t & G4f).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E6 (if cm then S_XTtF else S_XTfF) ms8 HS8 ltac:(destruct cm; [exact XRt | exact XRf])) as Hshape8.
rewrite Hshape8. replace (Z_to_bv 64 (ss_pc (if cm then S_XTtF else S_XTfF))) with (w64 A_EXIT) by (destruct cm; reflexivity).
pose proof (st_ok_mem_ok tfibsegs E6 _ _ HS8) as HM8. cbn [restrict ms_mem] in HM8.
assert (HM8' : mem_ok tfibsegs E6 (mrestrict (w_H W2) (ms_mem ms8)) (WIN (-128) :: rs_FBF)) by (destruct cm; [rewrite <- XMt | rewrite <- XMf]; exact HM8).
assert (Hwin8 : forall a, usp - 65536 <= a < usp -> apresent (w_H W2) (ms_mem ms8) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E6 (w_H W2) (ms_mem ms8) (WIN (-128) :: rs_FBF)); [exact HM8' | left; reflexivity | exact E6_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E6 (w_H W2) (ms_mem ms8) (WIN (-128) :: rs_FBF)); [exact HM8' | right; left; reflexivity | exact E6_0 | lia | lia | cbn; lia]. }
apply (EXITL E6 W2 (ms_regs ms8) (ms_mem ms8) _ ly6 S6 Hp usp fs (if cm then 0 else v) k).
- exact E6_0.
- lia.
- exact U16.
- exact (tid_of_st_ok E6 (if cm then S_XTtF else S_XTfF) _ HS8 ltac:(destruct cm; vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E6 (if cm then S_XTtF else S_XTfF) ms8 10%bv HS8). destruct cm; [rewrite A0t; reflexivity | rewrite A0f].
cbn [sv_denot]. rewrite Z.add_0_r, E6old by (unfold K_FB; lia). unfold w64. rewrite <- E79. reflexivity.
- destruct cm; [left; reflexivity | exact Hv].
- unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E6 (if cm then S_XTtF else S_XTfF) ms8 2%bv HS8). destruct cm; [rewrite SPt | rewrite SPf];
cbn [sv_denot]; rewrite E6_0; apply u64_lit; unfold sp_window_lo in Ulo; lia.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E6 (if cm then S_XTtF else S_XTfF) ms8 3%bv HS8). destruct cm; [rewrite G3t | rewrite G3f]; reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E6 (if cm then S_XTtF else S_XTfF) ms8 4%bv HS8). destruct cm; [rewrite G4t | rewrite G4f]; reflexivity.
- rewrite <- FKimg. apply (mem_ok_sub tfibsegs E6 _ (WIN (-128) :: rs_FBF)); [| rewrite FKimg; exact IMG_LF_wf | exact HM8'].
do 3 apply submem_drop. apply submem_refl.
- exact Hwin8.
- exact HAI3.
- apply (AR_after_run B HB ARL ly6 S6 _ W2 E6 (WIN (-128) :: rs_FBF) mem6 (ms_mem ms8) md6 mat8 HAR6 S_FBrF_win_ok); [rewrite E6_0; exact Ulo | rewrite E6_0; exact HCT | exact HF8 |].
rewrite E6_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin8 a Ha)).
- exact (top_ok_le _ _ _ _ Hlyle6 HTOP).
- apply (so_state_frame k (w_H W2) E6 (WIN (-128) :: rs_FBF) _ _ HFr8 (proj1 (proj2 CM_so_okF))); [rewrite E6_0; exact Ulo | rewrite E6_0, E6old by (unfold K_FB; lia); exact E6' | exact HSO6].
- intros fd. rewrite wvb_fds', Efds6. subst md1. rewrite wvb_fds'. apply Hfds.
- rewrite wvb_fs', Efs6. subst md1. rewrite wvb_fs'. exact Hfs.
Qed.
End c.
End b.
