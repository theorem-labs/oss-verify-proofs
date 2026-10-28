(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD1y AD20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YD2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1v AD26 AD24 AD21 AD25.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma S_G_shape : ss_mem S_G = ss_mem S_CPp /\ ss_resv S_G = None /\ sr_get (ss_regs S_G) 10%bv = sv_big
/\ ss_mem S_RF = ss_mem S_CPp /\ ss_resv S_RF = None /\ ss_mem S_MG = ss_mem S_CPp /\ ss_resv S_MG = None
/\ ss_mem S_OOM2 = ss_mem S_MGp /\ ss_resv S_OOM2 = None /\ ss_mem S_MC = ss_mem S_MGp /\ ss_resv S_MC = None
/\ ss_mem S_FR = ss_mem S_MCp /\ ss_resv S_FR = None /\ sr_get (ss_regs S_RF) 10%bv = SLit 0xa2578 /\ sr_get (ss_regs S_RF) 2%bv = SOff 0 (-128).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma skipn3_img : skipn 3 (ss_mem S_RF) = IMG_REGIONS /\ skipn 3 (ss_mem S_OOM2) = IMG_REGIONS /\ skipn 3 (ss_mem S_CPp) = IMG_REGIONS
/\ skipn 3 (ss_mem S_MGp) = IMG_REGIONS /\ skipn 3 (ss_mem S_MCp) = IMG_REGIONS /\ skipn 3 (ss_mem S_RD') = IMG_REGIONS.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma img_regions_wf' : regions_wf IMG_REGIONS = true. Proof. reflexivity. Qed.
Lemma win_ok_gr : forallb drv_win_ok (ss_mem S_MGp) = true /\ forallb drv_win_ok (ss_mem S_MCp) = true /\ forallb drv_win_ok (ss_mem S_RD') = true.
Proof. repeat split; reflexivity. Qed.
Lemma wbs_gr : wr_below_sp (ss_facts S_RF) (ss_mem S_CPp) = true /\ wr_below_sp (ss_facts S_MG) (ss_mem S_CPp) = true
/\ wr_below_sp (ss_facts S_OOM2) (ss_mem S_MGp) = true /\ wr_below_sp (ss_facts S_MC) (ss_mem S_MGp) = true
/\ wr_below_sp (ss_facts S_FR) (ss_mem S_MCp) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rs_sub : submem rs_MG (ss_mem S_MG) /\ submem rs_FR (ss_mem S_FR) /\ submem rs_MC (ss_mem S_MC).
Proof.
pose proof mg_checks as (_ & _ & _ & _ & _ & E1). pose proof fr_checks as (_ & _ & _ & _ & _ & E2). pose proof mc_checks as (_ & _ & _ & _ & _ & E3).
rewrite E1, E2, E3. repeat split;
(lazymatch goal with |- submem _ (ss_mem ?s) => change (ss_mem s) with (hd R_errno (ss_mem s) :: tl (ss_mem s)) end; apply submem_drop; apply submem_filter).
Qed.
Lemma submem_skipn : forall n rs, submem (skipn n rs) rs.
Proof.
induction n as [|n IH]; intros rs.
- apply submem_refl.
- destruct rs as [|r rs]; cbn; [constructor|]. apply submem_drop. apply IH.
Qed.
Lemma blocks_bytes_blocks : forall s, blocks_bytes s = fold_right (fun b acc => snd b + acc) 0 (blocks s).
Proof.
intros s. unfold blocks_bytes, blocks. induction (st_chunks s) as [|k ks IH]; cbn; [reflexivity|].
destruct (is_alloc k); cbn; rewrite IH; reflexivity.
Qed.
Lemma blocks_after_free : forall (pb p' : sptr) (cap n2 : Z) l1 l2,
[(pb, cap); (p', n2)] = l1 ++ (pb, cap) :: l2 -> ~ In p' [pb] -> l1 = [] /\ l2 = [(p', n2)].
Proof.
intros pb p' cap n2 [|x l1] l2 H Hni; cbn in H.
- injection H as <-. auto.
- injection H as <- H. exfalso. destruct l1 as [|y l1]; cbn in H.
+ injection H as -> _. apply Hni. left. reflexivity.
+ injection H as _ H. destruct l1; discriminate H.
Qed.
Lemma pow2_double_le : forall cap e, 0 <= e -> cap = 2 ^ e -> cap < 2 ^ 26 -> 2 * cap <= 2 ^ 26.
Proof.
intros cap e He -> Hlt. assert (e < 26) by (apply (Z.pow_lt_mono_r_iff 2); lia).
replace (2 * 2 ^ e) with (2 ^ (e + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia.
Qed.
Lemma denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma runs_at_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) usp R,
(forall a, usp <= a < 2 ^ 64 -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> sp_window_lo <= usp ->
runs_at usp (mrestrict H m) R -> runs_at usp (mrestrict H' m') R.
Proof.
intros H H' m m' usp R HA Husp HR. unfold sp_window_lo in Husp. unfold runs_at in HR |- *. apply Forall_forall. intros [a bs] Hab.
pose proof (proj1 (Forall_forall _ _) HR _ Hab) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
split; [exact Q1|]. split; [exact Q2|]. intros j Hj. pose proof (Q3 j Hj) as Q.
pose proof (mbyte_of_aview tfibsegs _ _ _ _ _ (HA (a + Z.of_nat j) ltac:(lia))) as X. unfold mbyte in X.
rewrite (seg_rom_none tfibsegs (a + Z.of_nat j)) in X by first [lia | apply not_in_img_high; lia].
rewrite Q in X. destruct (nth_error bs j) as [b|] eqn:En; [| apply nth_error_None in En; lia].
destruct (mrestrict H' m' (Z_to_bv 64 (a + Z.of_nat j))); congruence.
Qed.
Lemma blk_copy : forall (H H' : word -> bool) (m m' : word -> option byte) x d len data,
(forall i, 0 <= i < len -> aview tfibsegs H' m' (d + i) = aview tfibsegs H m (x + i)) ->
(forall i, 0 <= i < len -> ~ in_img tfibsegs (x + i)) -> 0 <= x -> x + len <= 2 ^ 64 ->
(forall i, 0 <= i < len -> ~ in_img tfibsegs (d + i)) -> 0 <= d -> d + len <= 2 ^ 64 ->
blk H m x len data -> blk H' m' d len data.
Proof.
intros H H' m m' x d len data HA Hx Hx0 Hxh Hd Hd0 Hdh HB i Hi. rewrite <- (HB i Hi).
pose proof (HA i Hi) as X. unfold aview, mbyte in X.
rewrite (seg_rom_none tfibsegs (d + i)) in X by first [lia | apply Hd; lia].
rewrite (seg_rom_none tfibsegs (x + i)) in X by first [lia | apply Hx; lia].
destruct (mrestrict H' m' (Z_to_bv 64 (d + i))) as [b'|], (mrestrict H m (Z_to_bv 64 (x + i))) as [b|]; cbn in X;
try discriminate X; [| reflexivity]. injection X as X. f_equal. apply bv_eq. exact X.
Qed.
Lemma blk_of_frame_r : forall H E rs (m m' : word -> option byte) buf len data usp,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
sp_window_lo <= usp -> (forall a, buf <= a < buf + len -> ~ in_img tfibsegs a) -> 0 <= buf -> buf + len <= usp - 65536 ->
blk H m buf len data -> blk H m' buf len data.
Proof.
intros H E rs m m' buf len data usp HF Hok E0 Husp Hni Hb0 Hhi HB i Hi. pose proof (u64_range (ew E 0)) as R0. rewrite E0 in R0.
rewrite <- (HB i Hi). apply HF. intros Hw. apply (in_wrange_drv E rs _ Hok) in Hw. rewrite u64_lit in Hw by (unfold sp_window_lo in Husp; lia).
destruct Hw as [Hw|Hw]; [unfold sp_window_lo in Husp; lia |]. apply DRVW_rw in Hw. apply (Hni (buf + i) ltac:(lia)). apply in_img_rw. lia.
Qed.
Section Gr.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MSITE : malloc_site_tfa B.
Hypothesis MCPY : memcpy_site_tfa B.
Hypothesis FREE : free_site_tfa B.
Hypothesis REFUSED : refused_leaf_tfa B.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
#[local] Notation eagree := (AD25.eagree sp inp xw xd a0 p).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma not_ascratch : forall stk regs a spv,
spZ regs = spv -> ~ in_img tfibsegs a -> a < alloc_ceiling -> alloc_ceiling <= spv - stk -> ~ ascratch B stk regs a.
Proof.
intros stk regs a spv Hspv Hni Hce Hle [X|X]; [lia|]. rewrite (ts_errno B HB) in X. unfold TFIB_ERRNO in X.
apply Hni. apply in_img_rw. lia.
Qed.
Definition gvals (E : YP0m.env) (buf cap : Z) : Prop :=
bv_unsigned (ew E A_BUF) = buf /\ bv_unsigned (ew E A_CAP) = cap /\ 0 <= bv_unsigned (ew E A_LEN) /\ 1 <= bv_unsigned (ew E A_N)
/\ bv_unsigned (ew E A_LEN) + bv_unsigned (ew E A_N) = cap /\ 65536 <= cap <= 2 ^ 26.
Lemma G_len1 : forall E buf cap, gvals E buf cap -> U E sv_len1 = cap.
Proof.
intros E buf cap (V46 & V59 & V58 & V78 & Vs & Hc). unfold sv_len1. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !Z.add_0_r.
rewrite (zcanon_id (bv_unsigned (ew E A_LEN))), (zcanon_id (bv_unsigned (ew E A_N))) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). exact Vs.
Qed.
Lemma G_big : forall E buf cap, gvals E buf cap -> U E sv_big = cap / 2 ^ 26.
Proof.
intros E buf cap G. unfold sv_big. rewrite U_SAlu. cbn [zalu_raw]. rewrite (G_len1 E buf cap G), U_SLit.
change (Z.land (zcanon 26) 63) with 26. rewrite Z.shiftr_div_pow2 by lia. destruct G as (_ & _ & _ & _ & _ & Hc).
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Definition sv_dbl : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1)).
Lemma G_dbl : forall E buf cap, gvals E buf cap -> U E sv_dbl = 2 * cap.
Proof.
intros E buf cap G. pose proof G as (V46 & V59 & V58 & V78 & Vs & Hc). unfold sv_dbl.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit, !Z.add_0_r.
change (Z.land (zcanon 1) 63) with 1. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (bv_unsigned (ew E A_LEN))), (zcanon_id (bv_unsigned (ew E A_N))) by (unfold M64; lia).
rewrite (zcanon_id (bv_unsigned (ew E A_LEN) * 2)), (zcanon_id (bv_unsigned (ew E A_N) * 2)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma G_havoc : forall E buf cap k ws, (A_N < k)%nat -> gvals E buf cap -> gvals (havoc E k ws) buf cap.
Proof. intros E buf cap k ws Hk G. unfold gvals, A_N, A_BUF, A_CAP, A_LEN in *. rewrite !ew_havoc_old by lia. exact G. Qed.
Lemma G_ewset : forall E buf cap k v, (A_N < k)%nat -> gvals E buf cap -> gvals (ewset E k v) buf cap.
Proof. intros E buf cap k v Hk G. unfold gvals, A_N, A_BUF, A_CAP, A_LEN in *. rewrite !ew_ewset_other by lia. exact G. Qed.
Lemma refused_run : forall E (W : world tfibsegs) ms md buf cap,
st_ok tfibsegs E S_G (restrict (w_H W) ms) -> gvals E buf cap -> cap = 2 ^ 26 ->
SRr tfibsegs W (mkCfg ms md) (at_st S_G S_RF E W (ms_mem ms) md).
Proof.
intros E W ms md buf cap HS G Hcap. pose proof HWXi as HWX.
srr_branch_with tfibtbl_lp_ok HS.
{ srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr]. }
{ exfalso. rewrite branch_ne_U in Hc.
change (SAlu ALU_SRL (SAlu ALU_ADD (SOff 58 0) (SOff 78 0)) (SLit 26)) with sv_big in Hc.
rewrite (G_big E buf cap G), U_SLit, Hcap in Hc. rewrite Z.div_same in Hc by lia. discriminate Hc. }
Qed.
Lemma mg_run : forall E (W : world tfibsegs) ms md buf cap,
st_ok tfibsegs E S_G (restrict (w_H W) ms) -> gvals E buf cap -> cap < 2 ^ 26 ->
SRr tfibsegs W (mkCfg ms md) (at_st S_G S_MG E W (ms_mem ms) md).
Proof.
intros E W ms md buf cap HS G Hcap. pose proof HWXi as HWX.
srr_branch_with tfibtbl_lp_ok HS.
{ exfalso. rewrite branch_ne_U in Hc.
change (SAlu ALU_SRL (SAlu ALU_ADD (SOff 58 0) (SOff 78 0)) (SLit 26)) with sv_big in Hc.
rewrite (G_big E buf cap G), U_SLit in Hc.
rewrite Z.div_small in Hc by (destruct G as (_ & _ & _ & _ & _ & Hc'); lia). discriminate Hc. }
{ srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr]. }
Qed.
Lemma mc_reseat : forall E2 (W' : world tfibsegs) regs3 mem3 regs4 mem4 (nb ncp mblk : Z) ly S md,
st_ok tfibsegs E2 S_MC (mkst regs3 (w64 A_icpt_memcpy) (mrestrict (w_H W') mem3) (seg_rom tfibsegs)) ->
bv_unsigned (ew E2 0) = usp -> usp <= bv_unsigned (ew E2 6) ->
aregs_preserved regs3 regs4 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (nb <= a < nb + ncp) -> ~ (usp - 128 - ESTACK <= a < usp - 128) -> aview tfibsegs (w_H W') mem4 a = aview tfibsegs (w_H W') mem3 a) ->
(forall a, apresent (w_H W') mem3 a -> apresent (w_H W') mem4 a) ->
AR tfibsegs B ly S W' mem3 md -> In (nb, mblk) (ablocks B ly S) -> 0 <= ncp <= req_size mblk -> YM05.ceil_of_top (usp - stack_max_size) ->
(forall a, usp - 65536 <= a < usp - 128 -> apresent (w_H W') mem3 a) ->
st_ok tfibsegs (havoc E2 K_MC (map (getr regs4) CLOB)) S_MCp (mkst regs4 (Z_to_bv 64 RA_MC1) (mrestrict (w_H W') mem4) (seg_rom tfibsegs)).
Proof.
intros E2 W' regs3 mem3 regs4 mem4 nb ncp mblk ly S md HS E2_0 E2_6 HP Hfr Hpres HAR Hin Hreq HCT Hwin.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (al_blocks _ _ ARL ly S W' mem3 md nb mblk HAR Hin) as (_ & _ & Hce & _).
assert (NIMG : forall a, nb <= a < nb + req_size mblk -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ ARL ly S W' mem3 md a HAR (or_introl (ex_intro _ nb (ex_intro _ mblk (conj Hin Ha)))))). }
rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_eq_certs)))))))))). unfold drv_after. change (junk_upd K_MC CLOB) with ([] ++ junk_upd K_MC CLOB).
apply (st_ok_splice_havoc tfibsegs K_MC E2 S_MC regs3 regs4 (w64 A_icpt_memcpy) RA_MC1 (mrestrict (w_H W') mem3) (mrestrict (w_H W') mem4)
(WIN (-128) :: rs_MC) [] CLOB HS).
- exact (proj1 mc_checks).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact (proj1 (proj2 (proj2 (proj2 mc_checks)))).
- cbn [map app]. apply regs_preserved_frame. apply aregs_regs_preserved. exact HP.
- constructor.
- assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (nb <= a < nb + ncp) -> ~ (usp - 128 - ESTACK <= a < usp - 128) ->
mbyte tfibsegs (mrestrict (w_H W') mem4) a = mbyte tfibsegs (mrestrict (w_H W') mem3) a).
{ intros a H0 H1 H2. apply (mbyte_of_aview tfibsegs). apply Hfr; assumption. }
pose proof (st_ok_mem_ok tfibsegs E2 S_MC _ HS) as HM. cbn [ms_mem] in HM. destruct HM as (Hwf & Hok & Hpd).
assert (Hsub : submem rs_MC (ss_mem S_MC)) by exact (proj2 (proj2 rs_sub)).
assert (HMt : mem_ok tfibsegs E2 (mrestrict (w_H W') mem3) rs_MC).
{ apply (mem_ok_sub tfibsegs E2 _ _ rs_MC Hsub). 2:{ split; [exact Hwf|]. split; [exact Hok | exact Hpd]. }
pose proof (proj1 (proj2 mc_checks)) as W2. cbn in W2. apply andb_prop in W2. tauto. }
split; [exact (proj1 (proj2 mc_checks))|]. split.
+ constructor.
* split; [cbn [base_val r_base r_lo WIN]; rewrite E2_0; unfold sp_window_lo in Ulo; lia|].
split; [cbn [base_val r_base r_hi WIN]; rewrite E2_0; lia|]. split; [| constructor].
cbn [r_wlo r_whi r_base base_val WIN]. rewrite E2_0. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. apply Hwin. lia.
* assert (HK : Forall (region_kept tfibsegs E2 (mrestrict (w_H W') mem3) (mrestrict (w_H W') mem4)) rs_MC).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) (proj1 (proj2 (proj2 (proj2 (proj2 mc_checks))))) r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 HMt)) r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E2 (r_base r) + r_lo r <= a < base_val E2 (r_base r) + r_hi r ->
~ (nb <= a < nb + ncp) /\ ~ (usp - 128 - ESTACK <= a < usp - 128)).
{ intros a Ha. destruct (r_base r) as [[|[|[|[|[|[|[|k]]]]]]]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E2_0 in Ha. unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. pose proof (u64_range (ew E2 6)). unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. split; [| unfold ESTACK, sp_window_lo in *; lia].
intros Hab. apply (NIMG a ltac:(lia)). apply in_img_hull. lia. }
split; intros a Ha; [apply SCR; [lia | apply OFF; exact Ha | apply OFF; exact Ha]|].
intros Hw. exact (wview_grows tfibsegs _ _ _ (mem_grows_of_apresent (w_H W') mem3 mem4 Hpres) Hw). }
exact (proj1 (proj2 (mem_ok_kept tfibsegs E2 _ (mrestrict (w_H W') mem4) rs_MC HMt ltac:(pose proof (proj1 (proj2 mc_checks)) as W2; cbn in W2; apply andb_prop in W2; tauto) HK))).
+ split; [| exact (proj2 (proj2 HMt))].
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 mc_checks))))) as Hchk. clear - Hchk E2_0 E2_6 Ulo. unfold sp_window_lo in Ulo.
induction rs_MC as [|r rs IH]; cbn; [exact I|]. cbn in Hchk. apply andb_prop in Hchk as [Hc Hchk].
split; [|exact (IH Hchk)]. unfold extent_disjoint. cbn [r_base r_lo r_hi WIN base_val]. rewrite E2_0.
unfold drv_keep_ok in Hc. destruct (r_base r) as [[|[|[|[|[|[|[|k]]]]]]]|]; try discriminate Hc; cbn [base_val].
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E2_0. left. lia.
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. left. lia.
* apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. right. lia.
Qed.
Section f.
Variables (E3 : YP0m.env) (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(pth : list byte) (data : list byte) (pb : sptr) (buf cap : Z).
Hypothesis HE3 : eagree E3.
Hypothesis HSG : st_ok tfibsegs E3 S_G (restrict (w_H W) ms).
Hypothesis G : gvals E3 buf cap.
Hypothesis HAR0 : AR tfibsegs B ly S W (ms_mem ms) md.
Hypothesis HAI0 : AI tfibsegs (w_H W) (w_A W) md.
Hypothesis HTOP : top_ok usp ly.
Hypothesis Hbl : blocks S = [(pb, cap)].
Hypothesis Hpb : sptr_addr B ly pb = buf.
Hypothesis Hnev : st_nev S + 2 <= EV_MAX.
Hypothesis HR0 : runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp).
Hypothesis Hfds0 : m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 cap)).
Hypothesis Hfs0 : m_fs md = in_fs inp.
Hypothesis HFI0 : FINV ly (w_H W) (ms_mem ms).
Let E3_0 : bv_unsigned (ew E3 0) = usp. Proof. exact (eagree_0 sp inp xw xd a0 p E3 HE3). Qed.
Let E3_6 : usp <= bv_unsigned (ew E3 6). Proof. exact (eagree_6 sp inp xw xd a0 p Hsp Hva Hve E3 HE3). Qed.
Let HCT : YM05.ceil_of_top (usp - stack_max_size). Proof. exact (top_ok_ceil _ _ HTOP). Qed.
Lemma Hin0 : In (buf, cap) (ablocks B ly S). Proof. unfold ablocks. rewrite Hbl, <- Hpb. left. reflexivity. Qed.
Theorem gr_refused : cap = 2 ^ 26 -> srealizes tfibsegs (mkCfg ms md) (diag msg_refused (in_fs inp)).
Proof.
intros Hcap. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof E3_0 as E0'.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (refused_run E3 W ms md buf cap HSG G Hcap) HAI0).
intros W0 c' _ HAI' (-> & ms' & mat & -> & HS & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 S_RF ms' HS eq_refl) as Hshape. rewrite Hshape.
change (Z_to_bv 64 (ss_pc S_RF)) with (w64 0x4192c).
pose proof (st_ok_mem_ok tfibsegs E3 S_RF _ HS) as HM. cbn [restrict ms_mem] in HM.
apply (REFUSED E3 W (ms_regs ms') (ms_mem ms') _ ly S usp (in_fs inp)).
- exact E0'.
- lia.
- exact U16.
- exact (tid_of_st_ok E3 S_RF _ HS ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 10%bv HS); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 11%bv HS); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 12%bv HS); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 1%bv HS); reflexivity.
- unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 2%bv HS). eval_sr_get. cbn [sv_denot].
rewrite E0'. apply u64_lit. unfold sp_window_lo in Ulo; lia.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 3%bv HS); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_RF ms' 4%bv HS); reflexivity.
- rewrite <- (proj1 skipn3_img). exact (mem_ok_sub tfibsegs E3 _ _ _ (submem_skipn 3 _) ltac:(rewrite (proj1 skipn3_img); reflexivity) HM).
- intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
+ eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms') (ss_mem S_RF)); [exact HM | left; reflexivity | exact E0' | lia | lia | cbn; lia].
+ eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms') (ss_mem S_RF)); [exact HM | right; left; reflexivity | exact E0' | lia | lia | cbn; lia].
- exact HAI'.
- apply (AR_after_run B HB ARL ly S W E3 _ (ms_mem ms) (ms_mem ms') md mat HAR0 (proj1 (proj2 (proj2 (proj2 win_ok_iter)))));
[rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
+ apply (apresent_some' (w_H W)). eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms') (ss_mem S_RF)); [exact HM | left; reflexivity | exact E0' | lia | lia | cbn; lia].
+ apply (apresent_some' (w_H W)). eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms') (ss_mem S_RF)); [exact HM | right; left; reflexivity | exact E0' | lia | lia | cbn; lia].
- exact HTOP.
- unfold EV_MAX in *. lia.
- rewrite wvb_fds', Hfds0. reflexivity.
- rewrite wvb_fs', Hfs0. reflexivity.
Qed.
Lemma S_MG_regs2 : sr_get (ss_regs S_MG) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_MG) 3%bv = SLit 67584 /\ sr_get (ss_regs S_MG) 4%bv = SLit 6131600
/\ sr_get (ss_regs S_MG) 8%bv = SLit 2 /\ sr_get (ss_regs S_MG) 10%bv = sv_dbl
/\ sr_get (ss_regs S_MC) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_MC) 3%bv = SLit 67584 /\ sr_get (ss_regs S_MC) 4%bv = SLit 6131600
/\ sr_get (ss_regs S_FR) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs S_FR) 3%bv = SLit 67584 /\ sr_get (ss_regs S_FR) 4%bv = SLit 6131600
/\ sr_get (ss_regs S_FR) 8%bv = SLit 2
/\ sr_get (ss_regs S_RD') 19%bv = sv_len1 /\ sr_get (ss_regs S_RD') 21%bv = sv_dbl /\ sr_get (ss_regs S_RD') 9%bv = SOff A_NB 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem gr_grow : forall (K : TSet),
cap < 2 ^ 26 -> (exists e, 0 <= e /\ cap = 2 ^ e) -> cap mod 65536 = 0 -> pb <> PNull ->
blk (w_H W) (ms_mem ms) buf cap data -> drv_minv S cap (dlen data) -> cap <= dlen data ->
(forall (W' : world tfibsegs) ms' md' ly' S' (pb' : sptr),
let ER' := E_RD EL (ms_regs ms') in
st_ok tfibsegs ER' S_RD (restrict (w_H W') ms') ->
bv_unsigned (ew ER' A_BUF) = sptr_addr B ly' pb' -> bv_unsigned (ew ER' A_LEN) = cap -> bv_unsigned (ew ER' A_CAP) = 2 * cap ->
AR tfibsegs B ly' S' W' (ms_mem ms') md' -> AI tfibsegs (w_H W') (w_A W') md' -> top_ok usp ly' ->
blocks S' = [(pb', 2 * cap)] -> pb' <> PNull -> st_nev S' = st_nev S + 2 -> drv_minv S' (2 * cap) (dlen data) ->
runs_at usp (mrestrict (w_H W') (ms_mem ms')) (runs_main_tfa true sp [a0; p] envp) ->
blk (w_H W') (ms_mem ms') (sptr_addr B ly' pb') cap data ->
FINV ly' (w_H W') (ms_mem ms') ->
m_fds md' = APSG.fds3 (FdFile pth (Z_to_bv 64 cap)) -> m_fs md' = in_fs inp ->
srealizes tfibsegs (mkCfg ms' md') K) ->
srealizes tfibsegs (mkCfg ms md) K.
Proof.
intros K Hcap Hpow Hcapm Hnn HBLK0 Hminv Hdl CONT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof mg_checks as (CK1 & CK2 & CK3 & CK4 & CK5 & _). pose proof G as (V46 & V59 & V58 & V78 & Vs & Hc6).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md buf cap HAR0 Hin0) as (Hbm16 & Hb4096 & Hbce & Happ & Hpres0 & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG0 : forall a, buf <= a < buf + req_size cap -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ ARL ly S W (ms_mem ms) md a HAR0 (or_introl (ex_intro _ buf (ex_intro _ cap (conj Hin0 Ha)))))). }
pose proof S_MG_regs2 as (Q2 & Q3 & Q4 & Q8 & Q10 & T2 & T3 & T4 & F2 & F3 & F4 & F8 & D19 & D21 & D9).
pose proof S_MG_facts as (_ & Q1 & _ & _). pose proof S_MC_facts as (_ & T1 & T10 & T11 & T12). pose proof S_FR_facts as (_ & F1 & F10).
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (mg_run E3 W ms md buf cap HSG G Hcap) HAI0).
intros W0 c' _ HAI' (-> & msG & mat & -> & HS & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 S_MG msG HS eq_refl) as Hshape.
set (regs := ms_regs msG) in *. set (mem := ms_mem msG) in *.
set (md' := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (R1 : getr regs 1%bv = w64 RA_MG) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_MG msG 1%bv HS), Q1; reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_MG msG 2%bv HS), Q2. cbn [sv_denot]. rewrite E3_0. reflexivity. }
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_MG msG 3%bv HS), Q3; reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_MG msG 4%bv HS), Q4; reflexivity).
assert (R8 : getr regs 8%bv = w64 2) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_MG msG 8%bv HS), Q8; reflexivity).
assert (R10 : getr regs 10%bv = w64 (2 * cap)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_MG msG 10%bv HS), Q10. apply denot_of_U. exact (G_dbl E3 buf cap G). }
assert (Hsp' : spZ regs = usp + -128) by (unfold spZ; rewrite R2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = RA_MG) by (unfold raZ; rewrite R1; apply u64_lit; unfold RA_MG; lia).
pose proof (st_ok_mem_ok tfibsegs E3 S_MG _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem S_MG)); [exact HM | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem S_MG)); [exact HM | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
assert (HR : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E3 (ss_facts S_MG) (ss_mem S_G)); [exact (st_ok_facts_ok tfibsegs E3 S_MG _ HS) | exact (proj1 (proj2 wbs_gr)) | exact HFr | rewrite E3_0; lia | exact HR0]. }
assert (HAR : AR tfibsegs B ly S W mem md').
{ apply (AR_after_run B HB ARL ly S W E3 (ss_mem S_G) (ms_mem ms) mem md mat HAR0 (proj1 (proj2 (proj2 (proj2 win_ok_iter)))));
[rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
assert (HBLK : blk (w_H W) mem buf cap data).
{ apply (blk_of_frame_r _ _ _ _ _ buf cap data usp HFr (proj1 (proj2 (proj2 (proj2 win_ok_iter)))) E3_0 Ulo); [| lia | lia | exact HBLK0].
intros a Ha. apply NIMG0. lia. }
assert (HWF : Wf (as_universe B) S) by exact (am_wf _ _ _ _ (proj1 HAR)).
assert (Hbb : blocks_bytes S = cap) by (rewrite blocks_bytes_blocks, Hbl; cbn; lia).
rewrite Hshape. change (Z_to_bv 64 (ss_pc S_MG)) with (w64 (pc_wrap_malloc Tfib_code)). rewrite <- (ts_code B HB).
fold regs mem. change (mkCfg (mkst regs (w64 (pc_wrap_malloc (as_code B))) mem (seg_rom tfibsegs)) md')
with (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md').
apply (MSITE ly S W regs mem md' (2 * cap) K).
-
split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [unfold EV_MAX in *; lia|].
split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra; unfold RA_MG; lia|].
split; [rewrite Hsp'; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [| exact (drv_minv_qtight _ _ _ Hminv)]. unfold s0Z. rewrite R8. unfold w64. rewrite u64_lit by lia. lia.
- exact R10.
- unfold MALLOC_MAX. lia.
- rewrite Hbb. unfold LIVE_MAX. lia.
- rewrite (ts_code B HB), Hra. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- exact HAI'.
-
intros ly' S' W' regs' mem' md2 trc tr p' Hnn' Htrc Hpath HPOST Ha0 Hwle HAI2.
unfold cfg_at. rewrite Hra.
pose proof HPOST as (HAR' & Hlyle & _ & HPres & Hio & Hfr' & Hsc').
destruct (atok_apath _ _ _ tr _ (ml_malloc _ ML S (2 * cap) trc HWF ltac:(unfold EV_MAX in *; lia)
ltac:(unfold MALLOC_MAX; lia) ltac:(rewrite Hbb; unfold LIVE_MAX; lia) Htrc) Hpath)
as (ns' & HMP). cbn [malloc_post] in HMP. destruct HMP as (HWF' & Hnev' & _ & HfrM & Hbl' & HQT').
assert (Hblocks : blocks S' = [(pb, cap); (p', 2 * cap)] /\ ~ In p' [pb]).
{ rewrite Hbl in Hbl'. destruct p'; [exfalso; exact (Hnn' eq_refl) | exact Hbl' | exact Hbl' | exact Hbl']. }
destruct Hblocks as [Hblocks Hp'].
set (nb := sptr_addr B ly' p') in *.
assert (Etop : ly_top ly' = ly_top ly) by (destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
pose proof (al_layout _ _ ARL ly S W mem md' ly' HAR Hlyle) as (Habl & _ & _).
assert (Hpb' : sptr_addr B ly' pb = buf).
{ unfold ablocks in Habl. rewrite Hbl in Habl. cbn in Habl. injection Habl as Habl. rewrite Habl. exact Hpb. }
assert (Hin1 : In (buf, cap) (ablocks B ly' S')) by (unfold ablocks; rewrite Hblocks; cbn; left; rewrite Hpb'; reflexivity).
assert (Hin2 : In (nb, 2 * cap) (ablocks B ly' S')) by (unfold ablocks; rewrite Hblocks; cbn; right; left; reflexivity).
pose proof (al_blocks _ _ ARL ly' S' W' mem' md2 _ _ HAR' Hin2) as (Hnb16 & Hnb4096 & Hnbce & Hnapp & HpresN & _).
pose proof (al_blocks _ _ ARL ly' S' W' mem' md2 _ _ HAR' Hin1) as (_ & _ & _ & _ & HpresB & _).
assert (Hreq1 : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (Hreq2 : req_size (2 * cap) = 2 * cap) by (unfold req_size; destruct (Z.eqb_spec (2 * cap) 0); lia).
rewrite Hreq2 in Hnbce, HpresN, Hnapp.
assert (NIMGN : forall a, nb <= a < nb + 2 * cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : nb <= a < nb + req_size (2 * cap)) by (rewrite Hreq2; exact Ha).
exact (proj2 (al_client_img _ _ ARL ly' S' W' mem' md2 a HAR' (or_introl (ex_intro _ nb (ex_intro _ (2 * cap) (conj Hin2 Ha')))))). }
assert (NIMGB : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a) by (intros a Ha; apply NIMG0; lia).
assert (Hsep : nb + 2 * cap <= buf \/ buf + cap <= nb).
{ pose proof (sep_blocks tfibsegs B ARL ly' S' W' mem' md2 buf cap nb (2 * cap) HAR' Hin1 Hin2 ltac:(intros X; injection X; lia)) as X.
unfold zdisjoint in X. cbn [fst snd] in X. rewrite Hreq1, Hreq2 in X. lia. }
assert (Hcap2 : 2 * cap <= 2 ^ 26) by (destruct Hpow as (e & He & Hce); exact (pow2_double_le cap e He Hce Hcap)).
pose proof (drv_after_call B HB ARL K_MG E3 S_MG msG ly S W md' (fun a => nb <= a < nb + req_size (2 * cap)) ly' S' W' regs' mem' md2 rs_MG
RA_MG usp (-128) HS eq_refl CK1 CK2 CK3 CK4 (proj1 rs_sub) Q1 HPOST HAR
ltac:(intros a Ha; rewrite Hreq2 in Ha; split; [lia | apply NIMGN; lia])
CK5 E3_0 E3_6 Hsp' ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin; lia)) as HS2.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_eq_certs))))))) in HS2.
set (E2 := havoc E3 K_MG (map (getr regs') CLOB)) in HS2.
assert (A117 : ew E2 A_NB = w64 nb).
{ subst E2. change A_NB with (K_MG + 4)%nat. rewrite (ew_havoc_new E3 K_MG _ 4 (w64 0)) by (cbn; lia). cbn. exact Ha0. }
assert (U117 : bv_unsigned (ew E2 A_NB) = nb) by (rewrite A117; apply u64_lit; lia).
assert (E2old : forall k, (k < K_MG)%nat -> ew E2 k = ew E3 k) by (intros k Hk; subst E2; apply ew_havoc_old; exact Hk).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold K_MG; lia); exact E3_0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold K_MG; lia); exact E3_6).
assert (G2 : gvals E2 buf cap) by (subst E2; apply G_havoc; [unfold K_MG, A_N; lia | exact G]).
assert (HE2 : eagree E2) by (subst E2; apply eagree_havoc; [exact HE3 | unfold K_MG, K_M1; lia]).
apply (st_ok_add_cond tfibsegs _ _ _ Instr.BC_NE (SOff A_NB 0) (SLit 0)) in HS2.
2:{ cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken]. rewrite Z.add_0_r, U117. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 nb) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by lia. lia. }
apply (st_ok_add_fact tfibsegs E2 _ _ A_NB blkq_fact) in HS2.
2:{ unfold afact_ok, blkq_fact. cbn [af_lo af_hi af_al2]. rewrite U117. change (2 ^ 4) with 16. repeat split; lia. }
destruct (same_io_fs_fds _ _ Hio) as [Efs Efds].
assert (HR' : runs_at usp (mrestrict (w_H W') mem') (runs_main_tfa true sp [a0; p] envp)).
{ apply (runs_at_of_aview (w_H W) (w_H W') mem mem' usp); [| exact Ulo | exact HR].
intros a Ha. apply Hfr'.
- unfold sp_window_lo in Ulo. lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR X). lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR' X). lia.
- intros [X|X]; [rewrite Hsp' in X; unfold ASTACK in X; lia|]. rewrite (ts_errno B HB) in X. unfold TFIB_ERRNO, sp_window_lo in *. lia.
- intros [X1 X2]. rewrite Hreq2 in X2. lia. }
assert (HBLK' : blk (w_H W') mem' buf cap data).
{ apply (blk_copy (w_H W) (w_H W') mem mem' buf buf cap data); [| exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact HBLK].
intros i Hi. apply Hfr'.
- lia.
- exact (proj2 (Hpres0 (buf + i) ltac:(lia))).
- exact (proj2 (HpresB (buf + i) ltac:(rewrite Hreq1; lia))).
- apply (not_ascratch ASTACK regs (buf + i) (usp + -128) Hsp'); [apply NIMGB; lia | lia | unfold ASTACK; lia].
- intros [X1 X2]. rewrite Hreq2 in X2. lia. }
assert (RUN3 : SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 RA_MG) mem' (seg_rom tfibsegs)) md2)
(at_st (add_atom (add_cond S_MGp (cPTR A_NB)) A_NB blkq_fact) S_MC E2 W' mem' md2)).
{ pose proof HS2 as HS3. pose proof HWXi as HWX. srr_run_to_with tfibtbl_lp_ok HS3 A_icpt_memcpy.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS3|]. split; [exact HF0 | exact HFr0]. }
apply (SRr_srealizes tfibsegs W' _ _ _ RUN3 HAI2).
intros W1 c1 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E2 S_MC ms3 HS3 eq_refl) as Hshape3.
set (regs3 := ms_regs ms3) in *. set (mem3 := ms_mem ms3) in *.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
assert (R1' : getr regs3 1%bv = w64 RA_MC1) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 1%bv HS3), T1; reflexivity).
assert (R2' : getr regs3 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 2%bv HS3), T2. cbn [sv_denot]. rewrite E2_0. reflexivity. }
assert (R3' : getr regs3 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 3%bv HS3), T3; reflexivity).
assert (R4' : getr regs3 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 4%bv HS3), T4; reflexivity).
assert (R10' : getr regs3 10%bv = w64 nb).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 10%bv HS3), T10. cbn [sv_denot]. rewrite Z.add_0_r, U117. reflexivity. }
assert (R11' : getr regs3 11%bv = w64 buf).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 11%bv HS3), T11. cbn [sv_denot]. rewrite Z.add_0_r.
destruct G2 as (V46' & _). rewrite V46'. reflexivity. }
assert (R12' : getr regs3 12%bv = w64 cap).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_MC ms3 12%bv HS3), T12. apply denot_of_U. exact (G_len1 E2 buf cap G2). }
assert (Hsp3 : spZ regs3 = usp - 128) by (unfold spZ; rewrite R2'; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (Hra3 : raZ regs3 = RA_MC1) by (unfold raZ; rewrite R1'; apply u64_lit; unfold RA_MC1; lia).
pose proof (st_ok_mem_ok tfibsegs E2 S_MC _ HS3) as HM3. cbn [restrict ms_mem] in HM3. fold mem3 in HM3.
assert (Hwin3 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem3 a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E2 (w_H W') mem3 (ss_mem S_MC)); [exact HM3 | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') mem3 (ss_mem S_MC)); [exact HM3 | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
assert (HAR3 : AR tfibsegs B ly' S' W' mem3 md3).
{ apply (AR_after_run B HB ARL ly' S' W' E2 _ mem' mem3 md2 mat3 HAR' (proj1 win_ok_gr)); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HF3 |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin3 a Ha)). }
assert (HR3 : runs_at usp (mrestrict (w_H W') mem3) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E2 (ss_facts S_MC) (ss_mem S_MGp)); [exact (st_ok_facts_ok tfibsegs E2 S_MC _ HS3) | exact (proj1 (proj2 (proj2 (proj2 wbs_gr)))) | exact HFr3 | rewrite E2_0; lia | exact HR']. }
assert (HBLK3 : blk (w_H W') mem3 buf cap data).
{ apply (blk_of_frame_r _ _ _ _ _ buf cap data usp HFr3 (proj1 win_ok_gr) E2_0 Ulo); [intros a Ha; apply NIMGB; lia | lia | lia | exact HBLK']. }
pose proof (al_blocks _ _ ARL ly' S' W' mem3 md3 _ _ HAR3 Hin2) as (_ & _ & _ & _ & HpresN3 & _). rewrite Hreq2 in HpresN3.
pose proof (al_blocks _ _ ARL ly' S' W' mem3 md3 _ _ HAR3 Hin1) as (_ & _ & _ & _ & HpresB3 & _). rewrite Hreq1 in HpresB3.
rewrite Hshape3. change (Z_to_bv 64 (ss_pc S_MC)) with (w64 (pc_wrap_memcpy Tfib_code)). rewrite <- (ts_code B HB).
fold regs3 mem3. change (mkCfg (mkst regs3 (w64 (pc_wrap_memcpy (as_code B))) mem3 (seg_rom tfibsegs)) md3)
with (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs3 mem3 md3).
eapply (SRr_srealizes tfibsegs W' (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs3 mem3 md3)); [| exact HAI3 |].
{ apply (MCPY ly' S' W' regs3 mem3 md3 nb buf cap).
- split; [exact HAR3|]. split; [pose proof (top_ok_le _ _ _ _ Hlyle HTOP) as (_ & TK2 & TK3 & _); exact (conj TK2 TK3)|]. split; [rewrite R1'; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Hsp3; replace (usp - 128) with (usp + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
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
rewrite Hsp3. unfold ESTACK in *. lia.
- apply (amem_range_of_block tfibsegs B ARL ly' S' W' mem3 md3 nb (2 * cap) nb cap HAR3 Hin2); [lia | rewrite Hreq2; lia].
- apply (range_addressable_of_block' B ARL ly' S' W' mem3 md3 nb (2 * cap) nb cap HAR3 Hin2); [lia | rewrite Hreq2; lia].
- intros Hn0. apply (shadow_hull_vis_of_block' B ARL ly' S' W' mem3 md3 nb (2 * cap) nb cap HAR3 Hin2); [lia | rewrite Hreq2; lia | lia].
- lia.
- lia.
- intros a Ha. split; [apply (aview_some_of_apresent tfibsegs); exact (proj1 (HpresB3 a ltac:(lia)))|].
rewrite Hsp3. unfold ESTACK in *. lia.
- lia.
- apply (amem_range_of_block tfibsegs B ARL ly' S' W' mem3 md3 buf cap buf cap HAR3 Hin1); [lia | rewrite Hreq1; lia].
- apply (range_addressable_of_block' B ARL ly' S' W' mem3 md3 buf cap buf cap HAR3 Hin1); [lia | rewrite Hreq1; lia].
- intros Hn0. apply (shadow_hull_vis_of_block' B ARL ly' S' W' mem3 md3 buf cap buf cap HAR3 Hin1); [lia | rewrite Hreq1; lia | lia]. }
cbv beta. intros W2 c2 _ HAI4 (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hs4 & Ha04 & Hcpy & Hfr4 & Hpres4). cbn [cfg_model] in HAI4.
unfold cfg_at. rewrite Hra3. rewrite Hsp3 in Hfr4.
rewrite Hshape3, restrict_mkst_fx in HS3. fold regs3 mem3 in HS3.
pose proof (mc_reseat E2 W' regs3 mem3 regs4 mem4 nb cap (2 * cap) ly' S' md3 HS3 E2_0 E2_6 HP4 Hfr4 Hpres4 HAR3 Hin2 ltac:(rewrite Hreq2; lia) HCT
ltac:(intros a Ha; apply Hwin3; lia)) as HS5.
set (E4 := havoc E2 K_MC (map (getr regs4) CLOB)) in HS5.
assert (E4old : forall k, (k < K_MC)%nat -> ew E4 k = ew E2 k) by (intros k Hk; subst E4; apply ew_havoc_old; exact Hk).
assert (E4_0 : bv_unsigned (ew E4 0) = usp) by (rewrite E4old by (unfold K_MC; lia); exact E2_0).
assert (E4_6 : usp <= bv_unsigned (ew E4 6)) by (rewrite E4old by (unfold K_MC; lia); exact E2_6).
assert (G4 : gvals E4 buf cap) by (subst E4; apply G_havoc; [unfold K_MC, A_N; lia | exact G2]).
assert (HE4 : eagree E4) by (subst E4; apply eagree_havoc; [exact HE2 | unfold K_MC, K_M1; lia]).
assert (U117_4 : bv_unsigned (ew E4 A_NB) = nb) by (unfold A_NB; rewrite E4old by (unfold K_MC; lia); exact U117).
pose proof (same_but_materialized_frame _ _ Hs4) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds4 & _ & _ & Hfs4 & _).
assert (HR4 : runs_at usp (mrestrict (w_H W') mem4) (runs_main_tfa true sp [a0; p] envp)).
{ apply (runs_at_of_aview (w_H W') (w_H W') mem3 mem4 usp); [| exact Ulo | exact HR3].
intros a Ha. apply Hfr4; unfold ESTACK in *; lia. }
assert (HBLK4 : blk (w_H W') mem4 nb cap data).
{ apply (blk_copy (w_H W') (w_H W') mem3 mem4 buf nb cap data Hcpy);
[exact (fun i Hi => NIMGB (buf + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGN (nb + i) ltac:(lia)) | lia | lia | exact HBLK3]. }
assert (Hwin4 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem4 a) by (intros a Ha; apply Hpres4; apply Hwin3; exact Ha).
rewrite <- restrict_mkst_fx in HS5.
assert (RUN5 : SRr tfibsegs W' (mkCfg (mkst regs4 (Z_to_bv 64 RA_MC1) mem4 (seg_rom tfibsegs)) md4) (at_st S_MCp S_FR E4 W' mem4 md4)).
{ pose proof HS5 as HS6. pose proof HWXi as HWX. srr_run_to_with tfibtbl_lp_ok HS6 A_wrap_free.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS6 with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS6|]. split; [exact HF0 | exact HFr0]. }
apply (SRr_srealizes tfibsegs W' _ _ _ RUN5 HAI4).
intros W3 c3 _ HAI5 (-> & ms5 & mat5 & -> & HS6 & HF5 & HFr5). cbn [cfg_model] in HAI5.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E4 S_FR ms5 HS6 eq_refl) as Hshape5.
set (regs5 := ms_regs ms5) in *. set (mem5 := ms_mem ms5) in *.
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4) in *.
assert (R1'' : getr regs5 1%bv = w64 RA_FR) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FR ms5 1%bv HS6), F1; reflexivity).
assert (R2'' : getr regs5 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FR ms5 2%bv HS6), F2. cbn [sv_denot]. rewrite E4_0. reflexivity. }
assert (R3'' : getr regs5 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FR ms5 3%bv HS6), F3; reflexivity).
assert (R4'' : getr regs5 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FR ms5 4%bv HS6), F4; reflexivity).
assert (R8'' : getr regs5 8%bv = w64 2) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FR ms5 8%bv HS6), F8; reflexivity).
assert (R10'' : getr regs5 10%bv = w64 buf).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FR ms5 10%bv HS6), F10. cbn [sv_denot]. rewrite Z.add_0_r.
destruct G4 as (V46' & _). rewrite V46'. reflexivity. }
assert (Hsp5 : spZ regs5 = usp + -128) by (unfold spZ; rewrite R2''; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra5 : raZ regs5 = RA_FR) by (unfold raZ; rewrite R1''; apply u64_lit; unfold RA_FR; lia).
pose proof (st_ok_mem_ok tfibsegs E4 S_FR _ HS6) as HM5. cbn [restrict ms_mem] in HM5. fold mem5 in HM5.
assert (Hwin5 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem5 a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E4 (w_H W') mem5 (ss_mem S_FR)); [exact HM5 | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') mem5 (ss_mem S_FR)); [exact HM5 | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HAR5 : AR tfibsegs B ly' S' W' mem5 md5).
{ apply (AR_after_run B HB ARL ly' S' W' E4 (ss_mem S_MCp) mem4 mem5 md4 mat5 HAR4 (proj1 (proj2 win_ok_gr))); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HF5 |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin5 a Ha)). }
assert (HR5 : runs_at usp (mrestrict (w_H W') mem5) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E4 (ss_facts S_FR) (ss_mem S_MCp)); [exact (st_ok_facts_ok tfibsegs E4 S_FR _ HS6) | exact (proj2 (proj2 (proj2 (proj2 wbs_gr)))) | exact HFr5 | rewrite E4_0; lia | exact HR4]. }
assert (HBLK5 : blk (w_H W') mem5 nb cap data).
{ apply (blk_of_frame_r _ _ _ _ _ nb cap data usp HFr5 (proj1 (proj2 win_ok_gr)) E4_0 Ulo); [intros a Ha; apply NIMGN; lia | lia | lia | exact HBLK4]. }
pose proof (al_blocks _ _ ARL ly' S' W' mem5 md5 _ _ HAR5 Hin2) as (_ & _ & _ & _ & HpresN5 & _). rewrite Hreq2 in HpresN5.
rewrite Hshape5. change (Z_to_bv 64 (ss_pc S_FR)) with (w64 (pc_wrap_free Tfib_code)). rewrite <- (ts_code B HB).
fold regs5 mem5. change (mkCfg (mkst regs5 (w64 (pc_wrap_free (as_code B))) mem5 (seg_rom tfibsegs)) md5)
with (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs5 mem5 md5).
eapply (SRr_srealizes tfibsegs W' (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs5 mem5 md5)); [| exact HAI5 |].
{ apply (FREE ly' S' W' regs5 mem5 md5 pb cap).
- split; [exact HAR5|]. split; [pose proof (top_ok_le _ _ _ _ Hlyle HTOP) as (_ & TK2 & TK3 & _); exact (conj TK2 TK3)|]. split; [rewrite Hnev'; unfold EV_MAX in *; lia|].
split; [rewrite R1''; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra5; unfold RA_FR; lia|].
split; [rewrite Hsp5; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp5; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp5, Etop; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp5; intros a Ha; apply Hwin5; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3''|]. split; [rewrite (ts_tp B HB); exact R4''|].
split; [| exact (HQT' (drv_minv_qtight _ _ _ Hminv))]. unfold s0Z. rewrite R8''. unfold w64. rewrite u64_lit by lia. lia.
- rewrite Hblocks. left. reflexivity.
- rewrite Hpb'. exact R10''.
- rewrite (ts_code B HB), Hra5. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto. }
cbv beta. intros W4 c4 Hwle4 HAI6 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6). cbn [cfg_model] in HAI6.
unfold cfg_at. rewrite Hra5.
pose proof HPOST6 as (HAR6 & Hlyle6 & Hwle6 & HP6 & Hio6 & Hfr6 & Hsc6).
destruct (atok_apath _ _ _ tr6 _ (ml_free _ ML S' pb cap trc6 HWF' ltac:(rewrite Hnev'; unfold EV_MAX in *; lia)
ltac:(right; rewrite Hblocks; left; reflexivity) Htrc6) Hpath6) as (ns6 & HFP).
cbn [free_post snd] in HFP. destruct HFP as (HWF6 & Hnev6 & _ & HfrF & (l1 & l2 & Hcase & Hbl6) & HQT6). cbn [snd] in HWF6, Hnev6, Hbl6, HfrF, HQT6.
destruct Hcase as [[Hnull _] | Hsplit]; [exfalso; exact (Hnn Hnull)|]. rewrite Hblocks in Hsplit.
destruct (blocks_after_free pb p' cap (2 * cap) l1 l2 Hsplit Hp') as [-> ->]. cbn [app] in Hbl6.
assert (Etop6 : ly_top ly6 = ly_top ly') by (destruct Hlyle6 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
pose proof (al_layout _ _ ARL ly' S' W' mem5 md5 ly6 HAR5 Hlyle6) as (Habl6 & _ & _).
assert (Hnb6 : sptr_addr B ly6 p' = nb).
{ unfold ablocks in Habl6. rewrite Hblocks in Habl6. cbn in Habl6. injection Habl6 as _ Habl6. exact Habl6. }
assert (Hin6 : In (nb, 2 * cap) (ablocks B ly6 S6)) by (unfold ablocks; rewrite Hbl6; cbn; left; rewrite Hnb6; reflexivity).
pose proof (al_blocks _ _ ARL ly6 S6 W4 mem6 md6 _ _ HAR6 Hin6) as (_ & _ & _ & _ & HpresN6 & _). rewrite Hreq2 in HpresN6.
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
assert (HR6 : runs_at usp (mrestrict (w_H W4) mem6) (runs_main_tfa true sp [a0; p] envp)).
{ apply (runs_at_of_aview (w_H W') (w_H W4) mem5 mem6 usp); [| exact Ulo | exact HR5].
intros a Ha. apply Hfr6.
- unfold sp_window_lo in Ulo. lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR5 X). lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR6 X). lia.
- intros [X|X]; [rewrite Hsp5 in X; unfold ASTACK in X; lia|]. rewrite (ts_errno B HB) in X. unfold TFIB_ERRNO, sp_window_lo in *. lia.
- intros [X1 X2]. rewrite Hreq1 in X2. lia. }
assert (HBLK6 : blk (w_H W4) mem6 nb cap data).
{ apply (blk_copy (w_H W') (w_H W4) mem5 mem6 nb nb cap data);
[| exact (fun i Hi => NIMGN (nb + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGN (nb + i) ltac:(lia)) | lia | lia | exact HBLK5].
intros i Hi. apply Hfr6.
- lia.
- exact (proj2 (HpresN5 (nb + i) ltac:(lia))).
- exact (proj2 (HpresN6 (nb + i) ltac:(lia))).
- apply (not_ascratch ASTACK regs5 (nb + i) (usp + -128) Hsp5); [apply NIMGN; lia | lia | unfold ASTACK; lia].
- intros [X1 X2]. rewrite Hreq1 in X2. lia. }
pose proof fr_checks as (FK1 & FK2 & FK3 & FK4 & FK5 & _).
pose proof (drv_after_call B HB ARL K_FR E4 S_FR ms5 ly' S' W' md5 (fun a => sptr_addr B ly' pb <= a < sptr_addr B ly' pb + req_size cap)
ly6 S6 W4 regs6 mem6 md6 rs_FR RA_FR usp (-128) HS6 eq_refl FK1 FK2 FK3 FK4 (proj1 (proj2 rs_sub)) F1 HPOST6 HAR5
ltac:(intros a Ha; rewrite Hpb', Hreq1 in Ha; split; [lia | apply NIMGB; lia])
FK5 E4_0 E4_6 Hsp5 ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin5; lia)) as HS7.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_eq_certs))))))))))) in HS7.
set (E6 := havoc E4 K_FR (map (getr regs6) CLOB)) in HS7.
assert (E6old : forall k, (k < K_FR)%nat -> ew E6 k = ew E4 k) by (intros k Hk; subst E6; apply ew_havoc_old; exact Hk).
assert (E6_0 : bv_unsigned (ew E6 0) = usp) by (rewrite E6old by (unfold K_FR; lia); exact E4_0).
assert (G6 : gvals E6 buf cap) by (subst E6; apply G_havoc; [unfold K_FR, A_N; lia | exact G4]).
assert (HE6 : eagree E6) by (subst E6; apply eagree_havoc; [exact HE4 | unfold K_FR, K_M1; lia]).
assert (U117_6 : bv_unsigned (ew E6 A_NB) = nb) by (unfold A_NB; rewrite E6old by (unfold K_FR; lia); exact U117_4).
pose proof (add_rt B HB sp inp xw xd a0 p Hsp E6 S_RD' W4 _ ly6 S6 md6 HE6 HS7 HAR6 (proj2 (proj2 rd0_ext))) as HS8.
rewrite (proj2 (proj2 with_rt_eqs)) in HS8.
pose proof (reabs_RD EL E6 S_RD'_rt (mkst regs6 (Z_to_bv 64 RA_FR) mem6 (seg_rom tfibsegs)) (w_H W4) (proj1 HE6) (proj2 HE6) HS8
(proj2 (proj2 (proj2 (proj2 (proj2 mem_RD_rt))))) (proj2 (proj2 reabs_chk_RD))
ltac:(rewrite (proj1 (proj2 (proj2 mem_RD_rt))); apply submem_refl)) as HSR.
cbn [ms_regs mkst] in HSR.
assert (X19 : getr regs6 19%bv = w64 cap).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W4) E6 S_RD' _ 19%bv HS7), D19. apply denot_of_U. exact (G_len1 E6 buf cap G6). }
assert (X21 : getr regs6 21%bv = w64 (2 * cap)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W4) E6 S_RD' _ 21%bv HS7), D21. apply denot_of_U. exact (G_dbl E6 buf cap G6). }
assert (X9 : getr regs6 9%bv = w64 nb).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W4) E6 S_RD' _ 9%bv HS7), D9. cbn [sv_denot]. rewrite Z.add_0_r, U117_6. reflexivity. }
assert (A46 : ew (E_RD EL regs6) A_BUF = w64 nb) by (unfold A_BUF; change 46%nat with (K_M1 + 4)%nat; rewrite (E_RD_new EL regs6 4) by (cbn; lia); exact X9).
assert (A58 : ew (E_RD EL regs6) A_LEN = w64 cap) by (unfold A_LEN; change 58%nat with (K_M1 + 16)%nat; rewrite (E_RD_new EL regs6 16) by (cbn; lia); exact X19).
assert (A59 : ew (E_RD EL regs6) A_CAP = w64 (2 * cap)) by (unfold A_CAP; change 59%nat with (K_M1 + 17)%nat; rewrite (E_RD_new EL regs6 17) by (cbn; lia); exact X21).
specialize (HSR ltac:(unfold afact_ok, fact_len, fact_cap; cbn [af_lo af_hi af_al2]; rewrite A58, A59; unfold w64; rewrite !u64_lit by lia;
repeat split; first [lia | rewrite Z.mod_1_r; reflexivity |
change (2 ^ 16) with 65536; replace (2 * cap) with (cap + cap) by lia; rewrite <- Zplus_mod_idemp_l, Hcapm, Z.add_0_l; exact Hcapm])).
rewrite <- restrict_mkst_fx in HSR |- * || idtac.
apply (CONT W4 (mkst regs6 (Z_to_bv 64 RA_FR) mem6 (seg_rom tfibsegs)) md6 ly6 S6 p'); cbn [ms_regs ms_mem mkst].
+ exact HSR.
+ rewrite Hnb6, A46. apply u64_lit. lia.
+ rewrite A58. apply u64_lit. lia.
+ rewrite A59. apply u64_lit. lia.
+ exact HAR6.
+ exact HAI6.
+ exact (top_ok_le _ _ _ _ Hlyle6 (top_ok_le _ _ _ _ Hlyle HTOP)).
+ exact Hbl6.
+ exact Hnn'.
+ rewrite Hnev6, Hnev'. lia.
+ exact (drv_minv_grow (as_universe B) S S' S6 cap (dlen data) trc tr p' trc6 tr6 pb Hminv ltac:(lia) Hdl Hpath HWF'
ltac:(rewrite Hblocks; left; reflexivity) Hpath6 HfrM HfrF HQT' HQT6).
+ exact HR6.
+ rewrite Hnb6. exact HBLK6.
+
assert (HFIg : FINV ly (w_H W) mem) by exact (finv_run B ly S W (ms_mem ms) md (w_H W) E3 (ss_mem S_G) _ _ usp HAR0 HFr (proj1 (proj2 (proj2 (proj2 win_ok_iter)))) E3_0 Ulo Uhi HTOP HFI0).
assert (HFIm : FINV ly' (w_H W') mem').
{ apply (finv_site B HB ARL ASTACK ly S W regs mem md' _ ly' S' W' regs' mem' md2 usp HAR HPOST); [| exact HTOP | exact Ulo | exact Uhi | rewrite Hsp'; lia | unfold ASTACK; lia | exact HFIg].
intros a Ha. right. exists nb, (2 * cap). exact (conj Hin2 Ha). }
pose proof (top_ok_le _ _ _ _ Hlyle HTOP) as HTOP'.
assert (HFI3 : FINV ly' (w_H W') mem3) by exact (finv_run B ly' S' W' mem' md2 (w_H W') E2 (ss_mem S_MGp) _ _ usp HAR' HFr3 (proj1 win_ok_gr) E2_0 Ulo Uhi HTOP' HFIm).
assert (HFI4 : FINV ly' (w_H W') mem4).
{ apply (finv_icpt B HB ARL ly' S' W' mem3 md3 mem4 (fun a => nb <= a < nb + cap) (usp - 128 - ESTACK) (usp - 128) usp HAR3 HTOP' Ulo Uhi Hfr4); [unfold ESTACK; lia | lia | | exact HFI3].
intros a Ha. exists nb, (2 * cap). split; [exact Hin2 | rewrite Hreq2; lia]. }
assert (HFI5 : FINV ly' (w_H W') mem5) by exact (finv_run B ly' S' W' mem4 md4 (w_H W') E4 (ss_mem S_MCp) _ _ usp HAR4 HFr5 (proj1 (proj2 win_ok_gr)) E4_0 Ulo Uhi HTOP' HFI4).
apply (finv_site B HB ARL ASTACK ly' S' W' regs5 mem5 md5 _ ly6 S6 W4 regs6 mem6 md6 usp HAR5 HPOST6); [| exact HTOP' | exact Ulo | exact Uhi | rewrite Hsp5; lia | unfold ASTACK; lia | exact HFI5].
intros a Ha. left. exists buf, cap. split; [exact Hin1 | rewrite Hpb' in Ha; exact Ha].
+ rewrite Efds6. subst md5. rewrite wvb_fds', Hfds4. subst md3. rewrite wvb_fds', Efds. subst md'. rewrite wvb_fds'. exact Hfds0.
+ rewrite Efs6. subst md5. rewrite wvb_fs', Hfs4. subst md3. rewrite wvb_fs', Efs. subst md'. rewrite wvb_fs'. exact Hfs0.
Qed.
End f.
End Gr.
End c.
