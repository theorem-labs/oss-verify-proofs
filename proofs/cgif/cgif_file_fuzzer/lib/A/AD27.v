(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP01 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD2a AD26 AD24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD21 AD25 AD22 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c AD2d AD29 AD1x AD28.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition img_msg_chk (p : Z) (msg : list byte) : bool :=
forallb (fun i : nat => match seg_rom tfibsegs (Z_to_bv 64 (p + Z.of_nat i)) with Some b => bv_eqb b (nth i msg NUL) | None => false end)
(seq 0 (length msg)).
Lemma img_msg_chk_sound : forall p msg, img_msg_chk p msg = true ->
forall i, (i < length msg)%nat -> seg_rom tfibsegs (Z_to_bv 64 (p + Z.of_nat i)) = Some (nth i msg NUL).
Proof.
intros p msg Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hc i ltac:(apply in_seq; lia)) as X. cbn beta in X.
destruct (seg_rom tfibsegs (Z_to_bv 64 (p + Z.of_nat i))) as [b|]; [|discriminate X]. apply (proj1 (Fs.bv_eqb_eq _ _)) in X. rewrite X. reflexivity.
Qed.
Lemma msgs_img : img_msg_chk 0x147d6 msg_oom = true /\ img_msg_chk 0x1f889 msg_short = true /\ img_msg_chk 0x1586a msg_overrun = true
/\ length msg_oom = 19%nat /\ length msg_short = 31%nat /\ length msg_overrun = 31%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma ret_oks : YK0s.ret_ok (Z_to_bv 64 0x80280) /\ YK0s.ret_ok (Z_to_bv 64 0x8cf08) /\ YK0s.ret_ok (Z_to_bv 64 0x80278) /\ YK0s.ret_ok (Z_to_bv 64 0x80254)
/\ YK0s.ret_ok (Z_to_bv 64 0x801e4) /\ YK0s.ret_ok (Z_to_bv 64 0x801a4) /\ YK0s.ret_ok (Z_to_bv 64 RA_JF).
Proof. unfold YK0s.ret_ok. repeat split; apply bv_eq; vm_compute; reflexivity. Qed.
Definition X_a0 : list sv := [SLit 2; SLit 2; SOff 206 0; SLit 2; SLit 2].
Definition X_spo : list Z := [-128; -128; -48; -48; -48].
Definition X_ra : list Z := [0x80280; 0x80280; 0x8cf08; 0x8cf08; 0x8cf08].
Definition X_mspo : list Z := [-128; -128; -48; -128; -128].
Definition X_wf : list bool := [false; false; false; true; true].
Definition X_img : list smem := [IMG_X; IMG_X; IMG_XL; IMG_X; IMG_X].
Lemma XSTS_row : forall i, (i < 5)%nat ->
sr_get (ss_regs (nth i XSTS S_J7x)) 10%bv = nth i X_a0 (SLit 0) /\ sr_get (ss_regs (nth i XSTS S_J7x)) 2%bv = SOff 0 (nth i X_spo 0) /\
sr_get (ss_regs (nth i XSTS S_J7x)) 1%bv = SLit (nth i X_ra 0) /\ ss_mem (nth i XSTS S_J7x) = jmemI (nth i X_img IMG_X) (nth i X_mspo 0) (nth i X_wf false) /\
YK0s.ret_ok (Z_to_bv 64 (nth i X_ra 0)) /\ (nth i X_spo 0 = -128 \/ nth i X_spo 0 = -48) /\ (nth i X_mspo 0 = -128 \/ nth i X_mspo 0 = -48)
/\ XIok (nth i X_img IMG_X) /\ ((nth i X_img IMG_X = IMG_XL /\ i = 2%nat) \/ (nth i X_img IMG_X = IMG_X /\ i <> 2%nat)).
Proof.
pose proof ret_oks as (K1 & K2 & _).
intros [|[|[|[|[|i]]]]] Hi; [..|cbn in Hi; lia]; cbn [nth X_a0 X_spo X_ra X_mspo X_wf X_img XSTS];
(split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
(split; [assumption|]); (split; [lia|]); (split; [lia|]); (split; [first [left; reflexivity | right; reflexivity] | first [left; split; [reflexivity | lia] | right; split; [reflexivity | lia]]]).
Qed.
Definition nege_fn (w : word) : word := sv_denot (mkEnv (fun _ => w) (fun _ => [])) sv_nege.
Lemma nege_chk : forallb (fun e => bv_eqb (nege_fn (errno_ret e)) (Z_to_bv 64 (2 ^ 64 - e))) (map Z.of_nat (seq 1 4095)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nege_val : forall E e, 0 < e < 4096 -> ew E A_NEGE = errno_ret e -> sv_denot E sv_nege = Z_to_bv 64 (2 ^ 64 - e).
Proof.
intros E e He H41.
assert (X : sv_denot E sv_nege = nege_fn (ew E A_NEGE)) by reflexivity. rewrite X, H41.
pose proof (proj1 (forallb_forall _ _) nege_chk e ltac:(apply in_map_iff; exists (Z.to_nat e); split; [lia | apply in_seq; lia])) as Y.
apply (proj1 (Fs.bv_eqb_eq _ _)) in Y. exact Y.
Qed.
Lemma CO_checks : wr_below_sp (ss_facts S_CO1) (ss_mem S_CO) = true /\ wr_below_sp (ss_facts S_COf) (ss_mem S_CO) = true /\ ss_facts S_CO1 = ss_facts S_CO
/\ atom_lookup (f_atoms (ss_facts S_COf)) 8%nat = Some (mkAF 1 4194303 0) /\ forallb drv_win_ok (ss_mem S_CO) = true /\ ss_mem S_CO1 = ss_mem S_CO
/\ ss_resv S_CO = None /\ ss_resv S_CO1 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma S_CO_hd : exists cs, hd R_errno (ss_mem S_CO) = YP09.mkRegion (Some 0%nat) (-65536) 0 (-65536) 0 cs /\ ss_mem S_CO <> [] /\ ss_mem S_COf <> [].
Proof. eexists. split; [vm_compute; reflexivity | split; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])]. Qed.
Lemma img_sub_COf : submem IMG_REGIONS (ss_mem S_COf).
Proof.
change (ss_mem S_COf) with (firstn 4 (ss_mem S_COf) ++ IMG_REGIONS ++ skipn 37 (ss_mem S_COf)).
do 4 apply submem_drop. induction IMG_REGIONS as [|r rs IH]; cbn; [apply submem_nil | apply submem_keep; [repeat split; try lia; auto | exact IH]].
Qed.
Lemma img_sub_US : submem IMG_REGIONS (ss_mem S_US).
Proof.
change (ss_mem S_US) with (firstn 3 (ss_mem S_US) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_US)).
do 3 apply submem_drop. induction IMG_REGIONS as [|r rs IH]; cbn; [apply submem_nil | apply submem_keep; [repeat split; try lia; auto | exact IH]].
Qed.
Lemma US_checks : atom_lookup (f_atoms (ss_facts S_US)) 8%nat = Some (mkAF 1 4194303 0) /\ ss_mem S_US <> [] /\ regions_wf (ss_mem (ss_main false)) = true
/\ atom_lookup (f_atoms (ss_facts (ss_main false))) 8%nat = Some (mkAF 1 4194303 0).
Proof. vm_compute. repeat split; try reflexivity; discriminate. Qed.
Lemma FW_facts : forall b : bool, let ss := if b then S_SHORT else S_OVR in
ss_pc ss = A_icpt_fwrite /\ sr_get (ss_regs ss) 10%bv = SLit (if b then 0x1f889 else 0x1586a) /\ sr_get (ss_regs ss) 11%bv = SLit 31 /\
sr_get (ss_regs ss) 12%bv = SLit 1 /\ sr_get (ss_regs ss) 13%bv = SLit 0xa2578 /\ sr_get (ss_regs ss) 1%bv = SLit 0x801e4 /\
sr_get (ss_regs ss) 2%bv = SOff 0 (-128) /\ sr_get (ss_regs ss) 3%bv = SLit TFIB_GP /\ sr_get (ss_regs ss) 4%bv = SLit TFIB_TP /\
sr_get (ss_regs ss) 8%bv = SLit 2 /\ sr_get (ss_regs ss) 9%bv = SOff A_BUF 0 /\ ss_resv ss = None /\
atom_lookup (f_atoms (ss_facts ss)) 8%nat = Some (mkAF 1 4194303 0) /\
hd R_errno (tl (ss_mem ss)) = YP09.mkRegion (Some 0%nat) (-128) 0 (-128) 0 JFR_chunks /\ (2 <= length (ss_mem ss))%nat /\
skipn 3 (firstn 36 (ss_mem ss)) = IMG_REGIONS.
Proof. intros [|]; vm_compute; repeat split; try reflexivity; apply Nat.leb_le; reflexivity. Qed.
Lemma FW_hd : forall b : bool, exists cs, hd R_errno (ss_mem (if b then S_SHORT else S_OVR)) = YP09.mkRegion (Some 0%nat) (-65536) (-128) (-65536) (-128) cs.
Proof. intros [|]; eexists; vm_compute; reflexivity. Qed.
Lemma img_sub_FW : forall b : bool, submem IMG_REGIONS (ss_mem (if b then S_SHORT else S_OVR)).
Proof.
intros [|].
- change (ss_mem S_SHORT) with (firstn 3 (ss_mem S_SHORT) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_SHORT)).
do 3 apply submem_drop. apply submem_app_r.
- change (ss_mem S_OVR) with (firstn 3 (ss_mem S_OVR) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_OVR)).
do 3 apply submem_drop. apply submem_app_r.
Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section f.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d727 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d73c (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15859 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Hypothesis FREE : free_site_tfa B.
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma est_frame_run : forall H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb se_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
est H m -> est H m'.
Proof.
intros H E rs m m' HF Hok U0 HE. apply (ESTF H H m m' HE). intros a Ha.
apply (aview_kept_run F_STDERR_LO F_STDERR_HI E rs H m m' a HF Hok U0); unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in *; lia.
Qed.
Lemma so_state_run : forall k H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb sx_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
so_state xst k H m -> so_state xst k H m'.
Proof.
intros k H E rs m m' HF Hok U0 HS. apply (so_state_keep xst XFR k H H m m'); [| exact HS]. intros a Ha.
assert (H1 : forallb (win_avoids STDOUT_LO STDOUT_HI) rs = true /\ forallb (win_avoids SOBUF_LO SOBUF_HI) rs = true).
{ split; apply forallb_forall; intros r Hr; pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X; unfold sx_win_ok in X; apply andb_prop in X; tauto. }
destruct Ha as [Ha|Ha].
- apply (aview_kept_run STDOUT_LO STDOUT_HI E rs H m m' a HF (proj1 H1) U0); unfold STDOUT_LO, STDOUT_HI in *; lia.
- apply (aview_kept_run SOBUF_LO SOBUF_HI E rs H m m' a HF (proj2 H1) U0); unfold SOBUF_LO, SOBUF_HI in *; lia.
Qed.
Lemma se_not_owned : forall ly S W mem md a, AR tfibsegs B ly S W mem md -> STDERR_MUT a -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a HAR Ha X.
assert (Hi : in_img tfibsegs a) by (apply in_img_rw; unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Ha; lia).
pose proof (proj1 (al_owned_image _ _ ARL _ _ _ _ _ _ HAR Hi) X) as Y. rewrite (ts_owned B HB) in Y.
apply Exists_exists in Y as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Tfib_owned_static in Hin. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Ha. cbn in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma site_keep_free : forall ly S W mem md ly' S' W' regs regs' mem' md' (Eb : Z -> Prop) usp k,
acall_post tfibsegs B ASTACK ly S W regs mem md Eb ly' S' W' regs' mem' md' -> AR tfibsegs B ly S W mem md ->
(forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) -> spZ regs = usp - 128 -> sp_window_lo <= usp ->
est (w_H W) mem -> so_state xst k (w_H W) mem ->
est (w_H W') mem' /\ so_state xst k (w_H W') mem'.
Proof.
intros ly S W mem md ly' S' W' regs regs' mem' md' Eb usp k HPOST HAR HEb Hsp Ulo HE HSO.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & _).
assert (KEEP : forall a, (STDERR_MUT a \/ STDOUT_MUT a) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha.
assert (Hr : 0xa2578 <= a < 0x5f9ee8) by (unfold STDERR_MUT, STDOUT_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
apply Hfr.
- lia.
- destruct Ha as [Ha|Ha]; [exact (se_not_owned ly S W mem md a HAR Ha) | exact (so_not_owned B HB ARL ly S W mem md a HAR Ha)].
- destruct Ha as [Ha|Ha]; [exact (se_not_owned ly' S' W' mem' md' a HAR' Ha) | exact (so_not_owned B HB ARL ly' S' W' mem' md' a HAR' Ha)].
- unfold ascratch. rewrite Hsp, (ts_errno B HB). unfold TFIB_ERRNO, ASTACK. unfold sp_window_lo in Ulo.
unfold STDERR_MUT, STDOUT_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- intros X. apply (proj2 (HEb a X)). apply in_img_rw. lia. }
split.
- apply (ESTF (w_H W) (w_H W') mem mem' HE). intros a Ha. apply KEEP. left. exact Ha.
- apply (so_state_keep xst XFR k (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. apply KEEP. right. exact Ha.
Qed.
Lemma img_kept_site : forall E (H : word -> bool) m m' (slo shi : Z),
mem_ok tfibsegs E (mrestrict H m) IMG_X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ STDERR_MUT a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
0x5fb000 <= slo ->
mem_ok tfibsegs E (mrestrict H m') IMG_X.
Proof.
intros E H m m' slo shi HM Hfr Hslo.
apply (mem_ok_kept tfibsegs E _ (mrestrict H m') IMG_X HM IMG_X_nocdata).
apply Forall_forall. intros r Hr. unfold region_kept.
pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 HM)) r Hr) as (B1 & B2 & _).
pose proof (proj1 (forallb_forall _ _) IMG_X_keep r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (forallb_forall _ _) IMG_X_abs r Hr) as Ha. unfold is_abs in Ha.
pose proof (proj1 (forallb_forall _ _) IMG_X_se r Hr) as Hx. unfold se_ext_ok, ext_avoids in Hx. cbn [fst snd] in Hx.
destruct (r_base r) as [bb|]; [discriminate Ha|]. cbn [base_val] in B1, B2 |- *.
apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
split; intros a Hra.
- apply (mbyte_of_aview tfibsegs). apply Hfr; [lia | lia |].
unfold STDERR_MUT. apply orb_prop in Hx as [Hx|Hx]; apply Z.leb_le in Hx; unfold F_STDERR_LO, F_STDERR_HI in *; lia.
- intros _. apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
unfold writable_at. apply tfib_rw_window. rewrite u64_lit by lia. lia.
Qed.
Lemma jfr_kept_site : forall E (H : word -> bool) m m' (usp slo shi : Z),
Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) usp) JFR_chunks ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ STDERR_MUT a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
shi <= usp - 128 -> sp_window_lo <= usp <= sp_window_hi ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict H m') usp) JFR_chunks.
Proof.
intros E H m m' usp slo shi HC Hfr Hshi [Ulo Uhi]. unfold sp_window_lo, sp_window_hi in *.
apply Forall_forall. intros c Hc i Hi. destruct (proj1 (Forall_forall _ _) HC c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
assert (Hoff : -128 <= YP09.c_off c /\ YP09.c_off c + c_len c <= -48).
{ clear - Hc. cbn in Hc. repeat (destruct Hc as [<-|Hc]; [cbn; lia|]). destruct Hc. }
rewrite <- Hb2. apply (mbyte_of_aview tfibsegs). apply Hfr; [lia | lia |].
unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI. lia.
Qed.
Lemma jfr_of_region : forall E (H : word -> bool) m rs lo hi wlo whi usp,
mem_ok tfibsegs E (mrestrict H m) rs -> In (YP09.mkRegion (Some 0%nat) lo hi wlo whi JFR_chunks) rs -> bv_unsigned (ew E 0) = usp ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) usp) JFR_chunks.
Proof.
intros E H m rs lo hi wlo whi usp (_ & Hok & _) Hin E0. pose proof (proj1 (Forall_forall _ _) Hok _ Hin) as (_ & _ & _ & HC).
cbn [r_chunks r_base base_val] in HC. rewrite E0 in HC. exact HC.
Qed.
Lemma jmemI_present : forall XI spo wf E (H : word -> bool) mem usp,
mem_ok tfibsegs E (mrestrict H mem) (jmemI XI spo wf) -> bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> (spo = -128 \/ spo = -48) ->
forall a, usp - 65536 <= a < usp -> apresent H mem a.
Proof.
intros XI spo wf E H mem usp (_ & Hok & _) E0 [Ulo Uhi] Hspo a Ha. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range (ew E 0)).
assert (X : forall lo hi wlo whi cs, In (YP09.mkRegion (Some 0%nat) lo hi wlo whi cs) (jmemI XI spo wf) -> usp + wlo <= a < usp + whi -> apresent H mem a).
{ intros lo hi wlo whi cs Hin Hr. pose proof (proj1 (Forall_forall _ _) Hok _ Hin) as (_ & _ & Wr & _). cbn [r_base r_wlo r_whi base_val] in Wr. rewrite E0 in Wr.
apply apresent_of_writable; [lia|]. replace a with (usp + (a - usp)) by lia. apply Wr. lia. }
destruct (Z.lt_ge_cases a (usp + spo)).
- apply (X (-65536) spo (-65536) spo []); [left; reflexivity | lia].
- destruct wf.
+ apply (X (-128) 0 (-128) 0 JFR_chunks); [right; left; reflexivity | destruct Hspo as [-> | ->]; [lia|]].
lia.
+ apply (X spo 0 spo 0 []); [right; left; reflexivity | lia].
Qed.
Lemma jmem_present : forall spo wf E (H : word -> bool) mem usp,
mem_ok tfibsegs E (mrestrict H mem) (jmem spo wf) -> bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> (spo = -128 \/ spo = -48) ->
forall a, usp - 65536 <= a < usp -> apresent H mem a.
Proof. intros spo wf. exact (jmemI_present IMG_X spo wf). Qed.
Lemma j7_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_J7 (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmem (-128) false) S_J7x E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 S_Jx_eq). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma j5_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_J5 (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmem (-128) false) S_J5x E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 S_Jx_eq)). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma jx_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_JX (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmemL (-48) false) S_JXx E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 (proj2 S_Jx_eq))). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma ju_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_JU (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmem (-128) true) S_JUx E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 (proj2 (proj2 S_Jx_eq)))). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma jf_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_JF (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmem (-128) true) S_JFc E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 S_Jx_eq))))). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma jfx_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_JFr (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmem (-128) true) S_JFx E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 S_Jx_eq)))))). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma run_to_exit : forall (i : nat) ss0 E (W : world tfibsegs) ms md ly S (usp : Z) fs (code : Z) (k : nat) (I0 : smem) spo0 wf0,
(i < 5)%nat ->
SRr tfibsegs W (mkCfg ms md) (at_rs (ss_mem ss0) (nth i XSTS S_J7x) E W (ms_mem ms) md) ->
ss_mem ss0 = jmemI I0 spo0 wf0 -> XIok I0 -> (spo0 = -128 \/ spo0 = -48) -> (i = 2%nat \/ k = 0%nat) ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
sv_denot E (nth i X_a0 (SLit 0)) = w64 code -> (code = 0 \/ code = 2) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly -> st_nev S < EV_MAX ->
est (w_H W) (ms_mem ms) -> so_state xst k (w_H W) (ms_mem ms) ->
((1 <= k)%nat -> fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
Proof.
intros i ss0 E W ms md ly S usp fs code k I0 spo0 wf0 Hi HRUN Hm0 HI0 Hspo0 Hik E0 [Ulo Uhi] U16 Htid Hcode Hc02 HAI HAR HTOP Hnev HE HSO Hfd1 Hfs.
pose proof (u64_range (ew E 0)) as U0.
set (ssx := nth i XSTS S_J7x) in *.
pose proof (proj1 (Forall_forall _ _) XSTS_facts ssx ltac:(subst ssx; apply nth_In; cbn; lia)) as (Hpc & G3 & G4 & Hrv & _).
pose proof (XSTS_row i Hi) as (Ra0 & Rsp & Rra & Mx & Hret & Hspo & Hmspo & HXI & HXlate). fold ssx in Ra0, Rsp, Rra, Mx.
set (spo := nth i X_spo 0) in *. set (rav := nth i X_ra 0) in *. set (mspo := nth i X_mspo 0) in *. set (wf := nth i X_wf false) in *. set (XI := nth i X_img IMG_X) in *.
pose proof (jmemI_checks I0 spo0 wf0 HI0 Hspo0) as (WOK0 & SEK0 & SXK0 & _). pose proof (jmemI_checks XI mspo wf HXI Hmspo) as (WOK & SEK & SXK & JWF & _).
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ HRUN HAI).
intros W1 c1 _ HAI1 (-> & msX & matX & -> & HSX & HFX & HFrX). cbn [cfg_model] in HAI1. rewrite Hm0 in HFX, HFrX.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ssx msX HSX Hrv) as Hshape.
pose proof (st_ok_mem_ok tfibsegs E ssx _ HSX) as HMX. cbn [restrict ms_mem] in HMX. rewrite Mx in HMX.
pose proof (jmemI_present XI mspo wf E (w_H W) (ms_mem msX) usp HMX E0 (conj Ulo Uhi) Hmspo) as HwinX.
assert (RG : forall r, getr (ms_regs msX) r = sv_denot E (sr_get (ss_regs ssx) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E ssx msX r HSX)).
rewrite Hshape, Hpc. change (Z_to_bv 64 A_exit) with (w64 A_exit).
apply (EXS XI E W (ms_regs msX) (ms_mem msX) (with_vm_backing (m_vm_lazy md) matX md) ly S usp (- spo) fs code k).
-
destruct HXlate as [[HL _] | [HX Hne]]; [right; exact HL | left]. split; [exact HX|]. destruct Hik as [Hik | Hk]; [exfalso; exact (Hne Hik) | exact Hk].
- exact E0.
- lia.
- exact U16.
- exact Htid.
- rewrite (RG 10%bv), Ra0. exact Hcode.
- exact Hc02.
- unfold spZ. rewrite (RG 2%bv), Rsp. cbn [sv_denot]. rewrite E0, u64_lit by (unfold sp_window_lo in Ulo; lia). lia.
- lia.
- rewrite (RG 1%bv), Rra. cbn [sv_denot]. exact Hret.
- rewrite (RG 3%bv), G3. reflexivity.
- rewrite (RG 4%bv), G4. reflexivity.
- apply (mem_ok_sub tfibsegs E _ (jmemI XI mspo wf)); [unfold jmemI; do 2 apply submem_drop; apply submem_refl | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (XI_checks XI HXI))))))) | exact HMX].
- exact HwinX.
- exact HAI1.
- apply (AR_after_run B HB ARL ly S W E (jmemI I0 spo0 wf0) (ms_mem ms) (ms_mem msX) md matX HAR WOK0); [rewrite E0; exact Ulo | rewrite E0; exact (top_ok_ceil _ _ HTOP) | exact HFX |].
rewrite E0. intros a Ha. exact (apresent_some' _ _ _ (HwinX a Ha)).
- exact HTOP.
- exact Hnev.
- exact (est_frame_run (w_H W) E (jmemI I0 spo0 wf0) _ _ HFrX SEK0 ltac:(rewrite E0; exact Ulo) HE).
- exact (so_state_run k (w_H W) E (jmemI I0 spo0 wf0) _ _ HFrX SXK0 ltac:(rewrite E0; exact Ulo) HSO).
- intros Hk. rewrite wvb_fds'. exact (Hfd1 Hk).
- rewrite wvb_fs'. exact Hfs.
Qed.
Lemma exit2_tail : forall (b : bool) E (W : world tfibsegs) regs mem md ly S (usp : Z) (fs : Fs),
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_X ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
est (w_H W) mem -> stdout_img (w_H W) mem -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (Z_to_bv 64 (if b then 0x80278 else 0x80254)) mem (seg_rom tfibsegs)) md) (ex 2 fs).
Proof.
intros b E W regs mem md ly S usp fs E0 [Ulo Uhi] U16 Htid Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev HEst HSO Hfs.
pose proof (regs_ok_J E regs (-128) usp E0 ltac:(lia) Ulo ltac:(lia) R3 R4) as HR.
pose proof (st_ok_J IMG_X E regs (jregs (-128)) (-128) (if b then 0x80278 else 0x80254) usp false (w_H W) mem (or_introl eq_refl) HR E0 Ulo ltac:(lia) HM Hwin ltac:(discriminate)) as HS.
assert (HS' : st_ok tfibsegs (E_J E regs) (if b then S_J7 else S_J5) (restrict (w_H W) (mkst regs (Z_to_bv 64 (if b then 0x80278 else 0x80254)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. pose proof S_J_defs as (D7 & D5 & _). destruct b; [rewrite D7 | rewrite D5]; exact HS. }
clear HS. set (E2 := E_J E regs) in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact E0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 fs))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
apply (run_to_exit (if b then 0 else 1)%nat (if b then S_J7 else S_J5) E2 W _ md ly S usp fs 2 0%nat IMG_X (-128) false); [| | | left; reflexivity | | right; reflexivity | ..].
- destruct b; cbn; lia.
- cbn [ms_mem mkst]. pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M7 & M5 & _).
destruct b; cbn [nth XSTS]; [rewrite M7; exact (j7_run E2 W _ md HS') | rewrite M5; exact (j5_run E2 W _ md HS')].
- pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M7 & M5 & _). destruct b; [exact M7 | exact M5].
- left. reflexivity.
- exact E2_0.
- lia.
- exact U16.
- subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
- destruct b; reflexivity.
- right. reflexivity.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact Hnev.
- exact HEst.
- left. split; [reflexivity | exact HSO].
- intros Hk. exfalso. lia.
- exact Hfs.
Qed.
Lemma sbm_fs_eq : forall md md', same_but_materialized md md' -> m_fs md' = m_fs md.
Proof. intros md md' Hs. rewrite Hs. apply wvb_fs'. Qed.
Lemma sbm_fds_eq : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md.
Proof. intros md md' Hs. rewrite Hs. apply wvb_fds'. Qed.
Lemma fpr_leaf : forall (fmt : Z) (lit1 : list byte), fprintf_s_site_tfa B est fmt lit1 nlB ->
forall E (W : world tfibsegs) regs mem md ly S (usp : Z) (p : list byte) (zp : Z) (fs : Fs),
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
getr regs 10%bv = w64 0xa2578 -> getr regs 11%bv = w64 fmt -> getr regs 12%bv = w64 zp ->
getr regs 1%bv = w64 0x80254 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
usp <= zp -> zp + Z.of_nat (length p) + 1 < kHighMemEnd -> ~ In NUL p -> Z.of_nat (length p) <= 131071 ->
YP03.bytes_at (mrestrict (w_H W) mem) zp (p ++ [NUL]) ->
(forall a, zp + Z.of_nat (length p) < a < zp + Z.of_nat (length p) - (zp + Z.of_nat (length p)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x4192c) mem (seg_rom tfibsegs)) md) (wr ch_stderr (lit1 ++ p ++ nlB) (ex 2 fs)).
Proof.
intros fmt lit1 FP E W regs mem md ly S usp p zp fs E0 [Ulo Uhi] U16 Htid R10 R11 R12 R1 Hsp R3 R4 Hzp1 Hzp2 Hnn Hlen HBr Htl HM Hwin HAI HAR HTOP Hnev Hfd2 Hfs.
pose proof (imgs_of_R E (w_H W) mem HM) as [HSO HSE].
assert (Hra : raZ regs = 0x80254) by (unfold raZ; rewrite R1; apply u64_lit; lia).
change (mkCfg (mkst regs (w64 0x4192c) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_fprintf regs mem md).
apply (FP ly S W regs mem md E zp p (ex 2 fs)).
- split; [exact HAR|]. split; [rewrite R1; exact (proj1 (proj2 (proj2 (proj2 ret_oks))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp; intros a Ha; apply Hwin; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB). exact (conj R3 R4).
- exact R10.
- exact R11.
- exact R12.
- exact Hlen.
- exact Hnn.
- rewrite Hsp. lia.
- exact Hzp2.
- exact HBr.
- exact Htl.
- exact HM.
- exact Hfd2.
- exact HAI.
- intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra. change (w64 0x80254) with (Z_to_bv 64 (if false then 0x80278 else 0x80254)).
apply (exit2_tail false E W regs' mem' md' ly S usp fs E0 (conj Ulo Uhi) U16 Htid).
+ unfold spZ. replace (getr regs' 2%bv) with (getr regs 2%bv) by (symmetry; exact (HP 2 ltac:(unfold acallee_saved; lia))). exact Hsp.
+ replace (getr regs' 3%bv) with (getr regs 3%bv) by (symmetry; exact (HP 3 ltac:(unfold acallee_saved; lia))). exact R3.
+ replace (getr regs' 4%bv) with (getr regs 4%bv) by (symmetry; exact (HP 4 ltac:(unfold acallee_saved; lia))). exact R4.
+ apply (img_kept_site E (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R E _ HM) Hfr). rewrite Hsp. unfold DIAG_STK, sp_window_lo in *. lia.
+ intros a Ha. pose proof (Hwin a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa].
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ exact Hnev.
+ exact HE'.
+ intros a Ha. rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ rewrite (sbm_fs_eq md md' Hsbm). exact Hfs.
Qed.
Theorem tfib_rderr_leaf : rderr_leaf_tfa B.
Proof.
intros E W regs mem md ly S usp p zp fs E0 U U16 Htid R10 R11 R12 R1 Hsp R3 R4 Hzp1 Hzp2 Hnn Hlen HBr Htl HM Hwin HAI HAR HTOP Hnev Hfd2 Hfs.
unfold diag, msg_read_error.
exact (fpr_leaf 0x1d73c _ FPR E W regs mem md ly S usp p zp fs E0 U U16 Htid R10 R11 R12 R1 Hsp R3 R4 Hzp1 Hzp2 Hnn Hlen HBr Htl HM Hwin HAI HAR HTOP Hnev Hfd2 Hfs).
Qed.
Theorem tfib_refused_leaf : refused_leaf_tfa B.
Proof.
intros E W regs mem md ly S usp fs E0 [Ulo Uhi] U16 Htid R10 R11 R12 R1 Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev Hfd2 Hfs.
pose proof (imgs_of_R E (w_H W) mem HM) as [HSO HSE].
assert (Hra : raZ regs = 0x80254) by (unfold raZ; rewrite R1; apply u64_lit; lia).
unfold diag. change (mkCfg (mkst regs (w64 0x4192c) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_fprintf regs mem md).
apply (RFS ly S W regs mem md E (ex 2 fs)).
- split; [exact HAR|]. split; [rewrite R1; exact (proj1 (proj2 (proj2 (proj2 ret_oks))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp; intros a Ha; apply Hwin; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB). exact (conj R3 R4).
- exact R10.
- exact R11.
- exact R12.
- exact HM.
- exact Hfd2.
- exact HAI.
- intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra. change (w64 0x80254) with (Z_to_bv 64 (if false then 0x80278 else 0x80254)).
apply (exit2_tail false E W regs' mem' md' ly S usp fs E0 (conj Ulo Uhi) U16 Htid).
+ unfold spZ. replace (getr regs' 2%bv) with (getr regs 2%bv) by (symmetry; exact (HP 2 ltac:(unfold acallee_saved; lia))). exact Hsp.
+ replace (getr regs' 3%bv) with (getr regs 3%bv) by (symmetry; exact (HP 3 ltac:(unfold acallee_saved; lia))). exact R3.
+ replace (getr regs' 4%bv) with (getr regs 4%bv) by (symmetry; exact (HP 4 ltac:(unfold acallee_saved; lia))). exact R4.
+ apply (img_kept_site E (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R E _ HM) Hfr). rewrite Hsp. unfold DIAG_STK, sp_window_lo in *. lia.
+ intros a Ha. pose proof (Hwin a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa].
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ exact Hnev.
+ exact HE'.
+ intros a Ha. rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ rewrite (sbm_fs_eq md md' Hsbm). exact Hfs.
Qed.
Lemma co_run1 : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_CO (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_CO S_CO1 E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 S_COUS_eq). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma co_run2 : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E (add_cond S_CO1 cond_CO) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_CO S_COf E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 S_COUS_eq)). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma win0_present : forall E (H : word -> bool) mem rs cs usp,
mem_ok tfibsegs E (mrestrict H mem) rs -> hd R_errno rs = YP09.mkRegion (Some 0%nat) (-65536) 0 (-65536) 0 cs -> rs <> [] ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi ->
forall a, usp - 65536 <= a < usp -> apresent H mem a.
Proof.
intros E H mem rs cs usp (_ & Hok & _) Hhd Hne E0 [Ulo Uhi] a Ha. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range (ew E 0)).
destruct rs as [|r rs]; [congruence|]. cbn [hd] in Hhd. subst r.
pose proof (Forall_inv Hok) as (_ & _ & Wr & _). cbn [r_base r_wlo r_whi base_val] in Wr. rewrite E0 in Wr.
apply apresent_of_writable; [lia|]. replace a with (usp + (a - usp)) by lia. apply Wr. lia.
Qed.
Theorem tfib_cannot_open : cannot_open_tfa B.
Proof.
intros sp inp xw xd W regs mem md ly a0 p e Hargv Hsp Hva Hve Hfit Hregs Hmem HG HR HAI HAR HTOP Hfs Hfds He.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
set (EL := YP08.E0 sp [a0; p] (in_envp inp) xw xd) in *. set (usp := bv_unsigned sp) in *.
set (E1 := ewset EL A_NEGE (errno_ret e)).
assert (E1_0 : bv_unsigned (ew E1 0) = usp) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); reflexivity).
assert (E1_41 : ew E1 A_NEGE = errno_ret e) by (subst E1; apply ew_ewset_same).
assert (Herr : bv_unsigned (errno_ret e) = 2 ^ 64 - e).
{ unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
pose proof CO_checks as (WB1 & WB2 & GF1 & TIDf & WOK & M1eq & RV0 & RV1).
pose proof (st_ok_resume_atom tfibsegs A_NEGE fact_err EL ss_open regs (mrestrict (w_H W) mem) (errno_ret e) Hregs Hmem HG
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO1_facts)))))) ltac:(cbn [af_lo af_hi fact_err]; rewrite Herr; lia) ltac:(cbn; lia)
ltac:(cbn [af_al2 fact_err]; rewrite Z.pow_0_r; apply Z.mod_1_r)) as HS0.
fold E1 in HS0. change (resume ss_open (SOff A_NEGE 0) (ss_mem ss_open) _) with S_COr in HS0.
assert (HS1 : st_ok tfibsegs E1 S_CO (restrict (w_H W) (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, S_CO_eq. apply (st_ok_app_regions E1 S_COr _ [R_errno] HS0 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO1_facts))))))).
- constructor; [apply region_ok_errno | constructor].
- cbn. split; [constructor | exact I].
- intros r1 r2 Hr1 Hr2. destruct Hr2 as [<-|[]].
pose proof (proj1 (forallb_forall _ _) (proj1 S_CO_ext) r1 Hr1) as Y. unfold ext_chk2 in Y. cbn [r_base R_errno r_lo r_hi] in Y.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_errno base_val].
assert (A1 : usp <= bv_unsigned (ew E1 1)) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); subst EL usp; rewrite (YP08.ew1 sp [a0; p] (in_envp inp) Hsp Hva Hve); unfold z_strs; lia).
assert (A2 : usp <= bv_unsigned (ew E1 2)) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); subst EL usp; rewrite (YP08.ew2' sp [a0; p] (in_envp inp) Hsp Hva Hve) by (cbn; lia);
pose proof (YP08.z_argv_bounds sp [a0; p] (in_envp inp) 1 ltac:(cbn; lia)) as [Z1 _]; unfold z_strs in Z1; lia).
assert (A6 : usp <= bv_unsigned (ew E1 6)) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); subst EL usp; exact (AD29.EL6 sp inp xw xd a0 p Hsp Hva Hve)).
unfold sp_window_lo in Ulo.
destruct (r_base r1) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate Y; cbn [base_val]; try (apply Z.leb_le in Y).
+ rewrite E1_0. right. lia.
+ right. lia.
+ right. lia.
+ right. lia.
+ apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia. }
apply (SRr_srealizes tfibsegs W _ _ _ (co_run1 E1 W _ md HS1) HAI).
intros Wa ca _ HAIa (-> & ms1 & mat1 & -> & HSa & HFa & HFra). cbn [cfg_model ms_mem mkst] in HAIa, HFa, HFra |- *.
assert (HSb : st_ok tfibsegs E1 (add_cond S_CO1 cond_CO) (restrict (w_H W) ms1)).
{ apply (st_ok_add_cond tfibsegs E1 S_CO1 _ BC_GEU sv_nege (SLit LIT_M4095) HSa).
rewrite (nege_val E1 e He E1_41). cbn [sv_denot Sem.branch_taken]. unfold LIT_M4095.
unfold bv_ltu. rewrite !u64_lit by lia. destruct (Z.ltb_spec (2 ^ 64 - e) 18446744073709547521); [lia | reflexivity]. }
apply (SRr_srealizes tfibsegs W _ _ _ (co_run2 E1 W ms1 _ HSb) HAIa).
intros Wb cb _ HAIb (-> & ms2 & mat2 & -> & HS2 & HFb & HFrb). cbn [cfg_model] in HAIb.
pose proof S_COf_facts as (Ppc & Pra & Psp & Pa0 & Pa1 & Pa2 & Pgp & Ptp & Prv).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E1 S_COf ms2 HS2 Prv) as Hshape. rewrite Hshape, Ppc. change (Z_to_bv 64 0x4192c) with (w64 0x4192c).
pose proof (st_ok_mem_ok tfibsegs E1 S_COf _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (RG : forall r, getr (ms_regs ms2) r = sv_denot E1 (sr_get (ss_regs S_COf) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E1 S_COf ms2 r HS2)).
assert (HR2 : runs_at usp (mrestrict (w_H W) (ms_mem ms2)) (runs_main_tfa true sp [a0; p] (in_envp inp))).
{ eapply (runs_at_frame E1 (ss_facts S_COf) (ss_mem S_CO)); [exact (st_ok_facts_ok tfibsegs E1 S_COf _ HS2) | exact WB2 | exact HFrb | rewrite E1_0; lia |].
eapply (runs_at_frame E1 (ss_facts S_CO1) (ss_mem S_CO)); [exact (st_ok_facts_ok tfibsegs E1 S_CO1 _ HSa) | exact WB1 | exact HFra | rewrite E1_0; lia | exact HR]. }
pose proof (runs_at_nth _ _ _ 2 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
destruct S_COf_mem as (cs0 & Hhd & _).
pose proof (win0_present E1 (w_H W) (ms_mem ms2) (ss_mem S_COf) cs0 usp HM2 Hhd ltac:(destruct S_CO_hd as (_ & _ & _ & X); exact X) E1_0 (conj Ulo Uhi)) as Hwin2.
unfold diag, msg_cannot_open.
apply (fpr_leaf 0x1d727 _ FPO E1 W (ms_regs ms2) (ms_mem ms2) _ ly init_state usp p (z_argv usp [a0; p] (in_envp inp) 1) (in_fs inp) E1_0 (conj Ulo Uhi) U16).
- exact (tid_of_st_ok E1 S_COf _ HS2 TIDf).
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. cbn [sv_denot]. rewrite Z.add_0_r. subst E1. rewrite ew_ewset_other by (unfold A_NEGE; lia).
subst EL. rewrite (YP08.ew2' sp [a0; p] (in_envp inp) Hsp Hva Hve) by (cbn; lia). reflexivity.
- rewrite (RG 1%bv), Pra. reflexivity.
- unfold spZ. rewrite (RG 2%bv), Psp. cbn [sv_denot]. rewrite E1_0. apply u64_lit. unfold sp_window_lo in Ulo. lia.
- rewrite (RG 3%bv), Pgp. reflexivity.
- rewrite (RG 4%bv), Ptp. reflexivity.
- pose proof (YP08.z_argv_bounds sp [a0; p] (in_envp inp) 1 ltac:(cbn; lia)) as [Z1 _]. unfold z_strs in Z1. subst usp. lia.
- exact (argv_str_fits' sp [a0; p] (in_envp inp) 1 Hfit ltac:(cbn; lia)).
- exact (argv_no_nul [a0; p] Hva 1 ltac:(cbn; lia)).
- exact (argv_str_len [a0; p] Hva 1 ltac:(cbn; lia)).
- exact HBr.
- subst usp. exact (argv_over_read sp (StackLayout.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) [a0; p] (in_envp inp) true _ 1 Hsp ltac:(cbn; lia) HR2).
- exact (mem_ok_sub tfibsegs E1 _ _ IMG_REGIONS img_sub_COf img_regions_wf HM2).
- exact Hwin2.
- exact HAIb.
- pose proof (st_ok_mem_ok tfibsegs E1 S_CO1 _ HSa) as HMa. cbn [restrict ms_mem] in HMa. rewrite M1eq in HMa.
destruct S_CO_hd as (cs1 & Hhd1 & Hne1 & _).
pose proof (win0_present E1 (w_H W) (ms_mem ms1) (ss_mem S_CO) cs1 usp HMa Hhd1 Hne1 E1_0 (conj Ulo Uhi)) as Hwin1.
apply (AR_after_run B HB ARL ly init_state W E1 (ss_mem S_CO) (ms_mem ms1) (ms_mem ms2) _ mat2); [| exact WOK | rewrite E1_0; exact Ulo | rewrite E1_0; exact (top_ok_ceil _ _ HTOP) | exact HFb | rewrite E1_0; intros a Ha; exact (apresent_some' _ _ _ (Hwin2 a Ha))].
apply (AR_after_run B HB ARL ly init_state W E1 (ss_mem S_CO) mem (ms_mem ms1) md mat1 HAR WOK); [rewrite E1_0; exact Ulo | rewrite E1_0; exact (top_ok_ceil _ _ HTOP) | exact HFa |].
rewrite E1_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin1 a Ha)).
- exact HTOP.
- cbn. unfold EV_MAX. lia.
- rewrite !wvb_fds', Hfds. reflexivity.
- rewrite !wvb_fs'. exact Hfs.
Qed.
Lemma us_run : forall sp (argv envp : list (list byte)) xw xd (W : world tfibsegs) ms md,
valid_sp sp -> valid_argv argv -> valid_envp envp -> (length argv <> 2)%nat ->
st_ok tfibsegs (YP08.E0 sp argv envp xw xd) (ss_main false) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st (ss_main false) S_US (YP08.E0 sp argv envp xw xd) W (ms_mem ms) md).
Proof.
intros sp argv envp xw xd W ms md Hsp Hva Hve Hlen HS. pose proof HWXi as HWX.
srr_run_with tfibtbl_drv_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibtbl_drv_ok HS.
2:{ exfalso. cbn [Sem.branch_taken sv_denot] in Hc. rewrite Z.add_0_r in Hc.
pose proof (YP08.ew3 sp argv envp Hva xw xd) as E3.
apply Bool.negb_false_iff in Hc. apply (proj1 (Fs.bv_eqb_eq _ _)) in Hc.
apply (f_equal bv_unsigned) in Hc. rewrite Z_to_bv_bv_unsigned, E3, u64_lit in Hc by lia. lia. }
pose proof (proj1 (proj2 (proj2 S_COUS_eq))) as QU. unfold run_x in QU.
srr_run_with tbl_x_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split.
- eapply frame_of_trans; [| exact HF1 | exact HF]. vm_compute. reflexivity.
- eapply frame_of_trans; [| exact HFr1 | exact HFr]. vm_compute. reflexivity.
Qed.
Theorem tfib_usage : forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
(length (in_argv inp) <> 2)%nat ->
YP0l.st_ok tfibsegs (YP08.E0 sp (in_argv inp) (in_envp inp) xw xd) (ss_main false) (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa false sp (in_argv inp) (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp inp xw xd W ms md ly Hsp Hva Hve Hfit Hlen HS HR HAI HAR HTOP Hfs Hfds.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
set (EL := YP08.E0 sp argv envp xw xd) in *. set (usp := bv_unsigned sp) in *.
assert (EL0 : bv_unsigned (ew EL 0) = usp) by reflexivity.
assert (Hargc : (1 <= length argv)%nat) by (pose proof (proj1 Hva); lia).
pose proof US_checks as (TIDf & NEus & WF0 & TID0).
pose proof (tid_of_st_ok EL (ss_main false) _ HS TID0) as Htid.
apply (SRr_srealizes tfibsegs W _ _ _ (us_run sp argv envp xw xd W ms md Hsp Hva Hve Hlen HS) HAI).
intros Wb cb _ HAIb (-> & ms2 & mat2 & -> & HS2 & HFb & HFrb). cbn [cfg_model] in HAIb.
pose proof S_US_facts as (Ppc & Pra & Psp & Pa0 & Pa1 & Pa2 & Pgp & Ptp & Ps0 & Prv & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EL S_US ms2 HS2 Prv) as Hshape. rewrite Hshape, Ppc.
change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 0x4192c) (ms_mem ms2) (seg_rom tfibsegs)) _) with (cfg_at tfibsegs A_icpt_fprintf (ms_regs ms2) (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
pose proof (st_ok_mem_ok tfibsegs EL S_US _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (RG : forall r, getr (ms_regs ms2) r = sv_denot EL (sr_get (ss_regs S_US) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) EL S_US ms2 r HS2)).
set (regs := ms_regs ms2) in *. set (mem := ms_mem ms2) in *.
assert (HR2 : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa false sp argv envp)).
{ pose proof S_CO_ext as (_ & _ & _ & _ & WBu & WBp & _).
eapply (runs_at_frame EL (ss_facts S_US) (ss_mem (ss_main false))); [exact (st_ok_facts_ok tfibsegs EL S_US _ HS2) | | exact HFrb | rewrite EL0; lia | exact HR].
vm_compute. reflexivity. }
pose proof (runs_at_nth _ _ _ 1 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
pose proof S_US_mem as (Hhd & _ & _).
pose proof (win0_present EL (w_H W) mem (ss_mem S_US) JFR_chunks usp HM2 Hhd NEus EL0 (conj Ulo Uhi)) as Hwin2.
pose proof (jfr_of_region EL (w_H W) mem (ss_mem S_US) (-65536) 0 (-65536) 0 usp HM2 ltac:(rewrite <- Hhd; destruct (ss_mem S_US); [exact (NEus eq_refl) | left; reflexivity]) EL0) as HJ2.
pose proof (mem_ok_sub tfibsegs EL _ _ IMG_REGIONS img_sub_US img_regions_wf HM2) as HMR. pose proof (imgs_of_R EL (w_H W) mem HMR) as [HSO HSE].
assert (HAR2 : AR tfibsegs B ly init_state W mem (with_vm_backing (m_vm_lazy md) mat2 md)).
{ apply (AR_after_run B HB ARL ly init_state W EL (ss_mem (ss_main false)) (ms_mem ms) mem md mat2 HAR (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO_ext))))))); [rewrite EL0; exact Ulo | rewrite EL0; exact (top_ok_ceil _ _ HTOP) | exact HFb |].
rewrite EL0. intros a Ha. exact (apresent_some' _ _ _ (Hwin2 a Ha)). }
assert (Hsp2 : spZ regs = usp - 128) by (unfold spZ; rewrite (RG 2%bv), Psp; cbn [sv_denot]; rewrite EL0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = 0x801a4) by (unfold raZ; rewrite (RG 1%bv), Pra; reflexivity).
assert (E1z : bv_unsigned (ew EL 1) = z_argv usp argv envp 0).
{ subst EL usp. rewrite (YP08.ew1 sp argv envp Hsp Hva Hve). unfold z_argv. rewrite firstn_O. cbn [total_arg_bytes_nat fold_right]. lia. }
unfold diag, msg_usage.
apply (FPU ly init_state W regs mem _ EL (z_argv usp argv envp 0) (nth 0 argv []) (ex 2 (in_fs inp))).
- split; [exact HAR2|]. split; [rewrite (RG 1%bv), Pra; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ret_oks))))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp2, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp2; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp2; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp2; intros a Ha; apply Hwin2; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB), (RG 3%bv), (RG 4%bv), Pgp, Ptp. split; reflexivity.
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. cbn [sv_denot]. rewrite Z.add_0_r, E1z. reflexivity.
- exact (argv_str_len argv Hva 0 ltac:(lia)).
- exact (argv_no_nul argv Hva 0 ltac:(lia)).
- rewrite Hsp2. pose proof (YP08.z_argv_bounds sp argv envp 0 ltac:(lia)) as [Z1 _]. unfold z_strs in Z1. subst usp. lia.
- exact (argv_str_fits' sp argv envp 0 Hfit ltac:(lia)).
- exact HBr.
- subst usp. exact (argv_over_read sp (StackLayout.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) argv envp false _ 0 Hsp ltac:(lia) HR2).
- exact HMR.
- rewrite wvb_fds', Hfds. reflexivity.
- exact HAIb.
-
intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra.
assert (P2 : getr regs' 2%bv = getr regs 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs' 3%bv = getr regs 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs' 4%bv = getr regs 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs' 8%bv = getr regs 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (Hwin' : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem' a).
{ intros a Ha. pose proof (Hwin2 a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa]. }
assert (HMX : mem_ok tfibsegs EL (mrestrict (w_H W) mem') IMG_X).
{ apply (img_kept_site EL (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R EL _ HMR) Hfr). rewrite Hsp2. unfold DIAG_STK, sp_window_lo in *. lia. }
assert (HJ' : Forall (YP09.chunk_ok tfibsegs EL (mrestrict (w_H W) mem') usp) JFR_chunks).
{ apply (jfr_kept_site EL (w_H W) mem mem' usp (spZ regs - DIAG_STK) (spZ regs) HJ2 Hfr); [rewrite Hsp2; lia | exact (conj Ulo Uhi)]. }
pose proof (regs_ok_J EL regs' (-128) usp EL0 ltac:(unfold spZ; rewrite P2; fold (spZ regs); rewrite Hsp2; lia) Ulo ltac:(lia)
ltac:(rewrite P3, (RG 3%bv), Pgp; reflexivity) ltac:(rewrite P4, (RG 4%bv), Ptp; reflexivity)) as HRJ.
pose proof (regs_ok_ovr (E_J EL regs') (jregs (-128)) regs' 8%bv (SLit 2) HRJ eq_refl ltac:(rewrite P8, (RG 8%bv), Ps0; reflexivity)) as HRJ'.
pose proof (st_ok_J IMG_X EL regs' _ (-128) 0x801a4 usp true (w_H W) mem' (or_introl eq_refl) HRJ' EL0 Ulo ltac:(left; reflexivity) HMX Hwin' ltac:(intros _; exact HJ')) as HSJ.
rewrite <- (proj1 (proj2 (proj2 (proj2 S_J_defs)))), <- restrict_mkst_fx in HSJ.
set (E2 := E_J EL regs') in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact EL0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 (in_fs inp)))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _).
apply (run_to_exit 3%nat S_JU E2 W _ md' ly init_state usp (in_fs inp) 2 0%nat IMG_X (-128) true ltac:(lia)); [| | left; reflexivity | | right; reflexivity | ..].
+ cbn [nth XSTS]. rewrite MU. exact (ju_run E2 W _ md' HSJ).
+ exact MU.
+ left. reflexivity.
+ exact E2_0.
+ exact (conj Ulo Uhi).
+ exact U16.
+ subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
+ reflexivity.
+ right. reflexivity.
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ cbn. unfold EV_MAX. lia.
+ exact HE'.
+ left. split; [reflexivity|]. cbn [ms_mem mkst]. intros a Ha.
rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp2; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ intros Hk. exfalso. lia.
+ rewrite (sbm_fs_eq _ md' Hsbm), wvb_fs'. exact Hfs.
Qed.
Theorem tfib_exit_leaf : exit_leaf_tfa B xst.
Proof.
intros E W regs mem md ly S usp fs code k E0 [Ulo Uhi] U16 Htid Ra0 Hc02 Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev HSO Hfds Hfs.
pose proof (ESTI (w_H W) mem (stderr_of_L E (w_H W) mem HM)) as HE.
pose proof (regs_ok_J E regs (-48) usp E0 ltac:(lia) Ulo ltac:(lia) R3 R4) as HR.
pose proof (st_ok_J IMG_XL E regs (jregs (-48)) (-48) 0x8cf04 usp false (w_H W) mem (or_intror eq_refl) HR E0 Ulo ltac:(right; split; reflexivity) (mem_ok_XL_of_L E _ HM) Hwin ltac:(discriminate)) as HS.
rewrite <- (proj1 (proj2 (proj2 S_J_defs))), <- restrict_mkst_fx in HS. change (Z_to_bv 64 0x8cf04) with (w64 A_EXIT) in HS.
set (E2 := E_J E regs) in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact E0).
pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MX).
apply (run_to_exit 2%nat S_JX E2 W _ md ly S usp fs code k IMG_XL (-48) false ltac:(lia)); [| | right; reflexivity | | left; reflexivity | ..].
- cbn [nth XSTS]. rewrite MX. exact (jx_run E2 W _ md HS).
- exact MX.
- right. reflexivity.
- exact E2_0.
- exact (conj Ulo Uhi).
- exact U16.
- subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
- cbn [nth X_a0 sv_denot]. rewrite Z.add_0_r. subst E2. change 206%nat with (KJ + 6)%nat. rewrite (E_J_new E regs 6 10%bv) by (first [cbn; lia | reflexivity]). rewrite Z_to_bv_bv_unsigned. exact Ra0.
- exact Hc02.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact Hnev.
- exact HE.
- exact HSO.
- intros Hk. rewrite Hfds. reflexivity.
- exact Hfs.
Qed.
Lemma win2_present : forall E (H : word -> bool) mem rs cs usp,
mem_ok tfibsegs E (mrestrict H mem) rs -> hd R_errno rs = YP09.mkRegion (Some 0%nat) (-65536) (-128) (-65536) (-128) cs ->
hd R_errno (tl rs) = YP09.mkRegion (Some 0%nat) (-128) 0 (-128) 0 JFR_chunks -> (2 <= length rs)%nat ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi ->
forall a, usp - 65536 <= a < usp -> apresent H mem a.
Proof.
intros E H mem rs cs usp (_ & Hok & _) Hhd Hhd2 Hlen E0 [Ulo Uhi] a Ha. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range (ew E 0)).
destruct rs as [|r [|r' rs]]; [cbn in Hlen; lia | cbn in Hlen; lia |]. cbn [hd tl] in Hhd, Hhd2. subst r r'.
pose proof (Forall_inv Hok) as (_ & _ & Wr & _). pose proof (Forall_inv (Forall_inv_tail Hok)) as (_ & _ & Wr' & _).
cbn [r_base r_wlo r_whi base_val] in Wr, Wr'. rewrite E0 in Wr, Wr'.
apply apresent_of_writable; [lia|]. replace a with (usp + (a - usp)) by lia.
destruct (Z.lt_ge_cases a (usp - 128)); [apply Wr | apply Wr']; lia.
Qed.
Lemma fw_leaf : forall (b : bool) (E : YP0m.env) sp inp (a0 p data : list byte) (W : world tfibsegs) ms md ly S (pb : sptr) (cap : Z),
valid_sp sp -> bv_unsigned sp <= bv_unsigned (ew E 6) -> bv_unsigned (ew E 0) = bv_unsigned sp ->
tail_at B (if b then S_SHORT else S_OVR) E sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag (if b then msg_short else msg_overrun) (in_fs inp)).
Proof.
intros b E sp inp a0 p data W ms md ly S pb cap Hsp HU6 E0 HT.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HTOP & Hbl & Hnev & Hcap & Hdl & Hblk & Hfs & Hfds & Hminv & HFI).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (usp := bv_unsigned sp) in *. set (ss := if b then S_SHORT else S_OVR) in *.
pose proof (FW_facts b) as F. cbv zeta in F. fold ss in F. destruct F as (Ppc & Pa0 & Pa1 & Pa2 & Pa3 & Pra & Psp & Pgp & Ptp & Ps0 & Ps1 & Prv & TIDf & Hhd2 & Hlen2 & _).
destruct (FW_hd b) as (cs0 & Hhd). fold ss in Hhd.
pose proof msgs_img as (_ & IMs & IMo & _ & LMs & LMo).
set (msg := if b then msg_short else msg_overrun). set (msgp := if b then 0x1f889 else 0x1586a) in *.
assert (IM : img_msg_chk msgp msg = true /\ length msg = 31%nat) by (subst msg msgp; destruct b; split; assumption). destruct IM as [IM LM].
pose proof (tid_of_st_ok E ss _ HS TIDf) as Htid.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Prv) as Hshape.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as HM. cbn [restrict ms_mem] in HM.
assert (RG : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS)).
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof (win2_present E (w_H W) mem (ss_mem ss) cs0 usp HM Hhd Hhd2 Hlen2 E0 (conj Ulo Uhi)) as Hwin.
pose proof (jfr_of_region E (w_H W) mem (ss_mem ss) (-128) 0 (-128) 0 usp HM
ltac:(rewrite <- Hhd2; destruct (ss_mem ss) as [|r [|r' rs]]; [cbn in Hlen2; lia | cbn in Hlen2; lia | right; left; reflexivity]) E0) as HJ.
pose proof (mem_ok_sub tfibsegs E _ _ IMG_REGIONS (img_sub_FW b) img_regions_wf HM) as HMR. pose proof (imgs_of_R E (w_H W) mem HMR) as [HSO HSE].
assert (Hsp2 : spZ regs = usp - 128) by (unfold spZ; rewrite (RG 2%bv), Psp; cbn [sv_denot]; rewrite E0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = 0x801e4) by (unfold raZ; rewrite (RG 1%bv), Pra; reflexivity).
assert (Hin : In (sptr_addr B ly pb, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W mem md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (NIMG : forall a, sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha)))))). }
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
rewrite Hshape, Ppc. unfold diag.
change (mkCfg (mkst regs (Z_to_bv 64 A_icpt_fwrite) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_fwrite regs mem md).
apply (FWS ly S W regs mem md E msgp 31 msg (ex 2 (in_fs inp))).
- split; [exact HAR|]. split; [rewrite (RG 1%bv), Pra; exact (proj1 (proj2 (proj2 (proj2 (proj2 ret_oks)))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp2, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp2; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp2; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp2; intros a Ha; apply Hwin; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB), (RG 3%bv), (RG 4%bv), Pgp, Ptp. split; reflexivity.
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. reflexivity.
- rewrite (RG 13%bv), Pa3. reflexivity.
- rewrite LM. reflexivity.
- lia.
- subst msgp; destruct b; lia.
- subst msgp; destruct b; lia.
- subst msgp; destruct b; [right | left]; lia.
- intros i Hi. apply (img_msg_chk_sound _ _ IM i Hi).
- exact HMR.
- rewrite Hfds. reflexivity.
- exact HAI.
-
intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra.
assert (P2 : getr regs' 2%bv = getr regs 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs' 3%bv = getr regs 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs' 4%bv = getr regs 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs' 8%bv = getr regs 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs' 9%bv = getr regs 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (Hwin' : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem' a).
{ intros a Ha. pose proof (Hwin a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa]. }
assert (HMX : mem_ok tfibsegs E (mrestrict (w_H W) mem') IMG_X).
{ apply (img_kept_site E (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R E _ HMR) Hfr). rewrite Hsp2. unfold DIAG_STK, sp_window_lo in *. lia. }
assert (HJ' : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem') usp) JFR_chunks).
{ apply (jfr_kept_site E (w_H W) mem mem' usp (spZ regs - DIAG_STK) (spZ regs) HJ Hfr); [rewrite Hsp2; lia | exact (conj Ulo Uhi)]. }
assert (HSO' : stdout_img (w_H W) mem').
{ intros a Ha. rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp2; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia]. }
pose proof (regs_ok_J E regs' (-128) usp E0 ltac:(unfold spZ; rewrite P2; fold (spZ regs); rewrite Hsp2; lia) Ulo ltac:(lia)
ltac:(rewrite P3, (RG 3%bv), Pgp; reflexivity) ltac:(rewrite P4, (RG 4%bv), Ptp; reflexivity)) as HRJ.
pose proof (regs_ok_ovr (E_J E regs') (jregs (-128)) regs' 8%bv (SLit 2) HRJ eq_refl ltac:(rewrite P8, (RG 8%bv), Ps0; reflexivity)) as HRJ'.
pose proof (regs_ok_ovr (E_J E regs') _ regs' 9%bv (SOff A_BUF 0) HRJ' eq_refl ltac:(rewrite P9, (RG 9%bv), Ps1; cbn [sv_denot]; rewrite E_J_old by (unfold KJ, A_BUF; lia); reflexivity)) as HRJ''.
pose proof (st_ok_J IMG_X E regs' _ (-128) 0x801e4 usp true (w_H W) mem' (or_introl eq_refl) HRJ'' E0 Ulo ltac:(left; reflexivity) HMX Hwin' ltac:(intros _; exact HJ')) as HSJ.
rewrite <- (proj2 (proj2 (proj2 (proj2 S_J_defs)))), <- restrict_mkst_fx in HSJ.
set (E2 := E_J E regs') in *.
assert (E2old : forall j, (j < KJ)%nat -> ew E2 j = ew E j) by (intros j Hj; subst E2; apply E_J_old; exact Hj).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold KJ; lia); exact E0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold KJ; lia); exact HU6).
pose proof S_JFc_facts as (Qpc & Qa0 & Qra & Qsp & Qs0 & Qgp & Qtp & QM & Qrv & QMr & QMf & _).
apply (SRr_srealizes tfibsegs W _ _ _ (jf_run E2 W _ md' HSJ) HAI').
intros W1 c1 _ HAI1 (-> & msc & matc & -> & HSc & HFc & HFrc). cbn [cfg_model ms_mem mkst] in HAI1, HFc, HFrc.
set (md1 := with_vm_backing (m_vm_lazy md') matc md') in *.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 S_JFc msc HSc Qrv) as Hshape1.
pose proof (st_ok_mem_ok tfibsegs E2 S_JFc _ HSc) as HMc. cbn [restrict ms_mem] in HMc. rewrite QM in HMc.
assert (RG1 : forall r, getr (ms_regs msc) r = sv_denot E2 (sr_get (ss_regs S_JFc) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E2 S_JFc msc r HSc)).
pose proof (jmem_present (-128) true E2 (w_H W) (ms_mem msc) usp HMc E2_0 (conj Ulo Uhi) ltac:(left; reflexivity)) as Hwin1.
assert (HAR1 : AR tfibsegs B ly S W (ms_mem msc) md1).
{ apply (AR_after_run B HB ARL ly S W E2 (jmem (-128) true) mem' (ms_mem msc) md' matc HAR' (proj1 (jmem_checks (-128) true ltac:(left; reflexivity)))); [rewrite E2_0; exact Ulo | rewrite E2_0; exact (top_ok_ceil _ _ HTOP) | exact HFc |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin1 a Ha)). }
pose proof (jmem_checks (-128) true ltac:(left; reflexivity)) as (JWOK & JSEK & JSXK & _).
assert (HE1 : est (w_H W) (ms_mem msc)) by exact (est_frame_run (w_H W) E2 (jmem (-128) true) _ _ HFrc JSEK ltac:(rewrite E2_0; exact Ulo) HE').
assert (HSO1 : so_state xst 0%nat (w_H W) (ms_mem msc)) by exact (so_state_run 0%nat (w_H W) E2 (jmem (-128) true) _ _ HFrc JSXK ltac:(rewrite E2_0; exact Ulo) (or_introl (conj eq_refl HSO'))).
assert (HWF : Wf (as_universe B) S) by exact (am_wf _ _ _ _ (proj1 HAR1)).
assert (Hsp1 : spZ (ms_regs msc) = usp + -128) by (unfold spZ; rewrite (RG1 2%bv), Qsp; cbn [sv_denot]; rewrite E2_0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra1 : raZ (ms_regs msc) = RA_JF) by (unfold raZ; rewrite (RG1 1%bv), Qra; reflexivity).
rewrite Hshape1, Qpc.
replace (Z_to_bv 64 0x5292c) with (w64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); reflexivity).
change (mkCfg (mkst (ms_regs msc) (w64 (pc_wrap_free (as_code B))) (ms_mem msc) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs (pc_wrap_free (as_code B)) (ms_regs msc) (ms_mem msc) md1).
eapply (SRr_srealizes tfibsegs W (cfg_at tfibsegs (pc_wrap_free (as_code B)) (ms_regs msc) (ms_mem msc) md1)); [| exact HAI1 |].
{ apply (FREE ly S W (ms_regs msc) (ms_mem msc) md1 pb cap).
- split; [exact HAR1|]. split; [unfold top_ok in *; tauto|]. split; [unfold EV_MAX; lia|].
split; [rewrite (RG1 1%bv), Qra; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ret_oks))))))|]. split; [rewrite Hra1; unfold RA_JF; lia|].
split; [rewrite Hsp1; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp1; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp1; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp1; intros a Ha; apply Hwin1; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB), (RG1 3%bv), Qgp; reflexivity|]. split; [rewrite (ts_tp B HB), (RG1 4%bv), Qtp; reflexivity|].
split; [| exact (drv_minv_qtight _ _ _ Hminv)]. unfold s0Z. rewrite (RG1 8%bv), Qs0. cbn [sv_denot]. rewrite u64_lit by lia. lia.
- rewrite Hbl. left. reflexivity.
- rewrite (RG1 10%bv), Qa0. cbn [sv_denot]. rewrite Z.add_0_r, E2old by (unfold KJ, A_BUF; lia). unfold w64. rewrite <- E41, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (ts_code B HB), Hra1. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto. }
cbv beta. intros W2 c2 Hwle2 HAI2 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6). cbn [cfg_model] in HAI2.
unfold cfg_at. rewrite Hra1.
pose proof HPOST6 as (HAR6 & Hlyle6 & _ & HP6 & Hio6 & Hfr6 & Hsc6).
destruct (atok_apath _ _ _ tr6 _ (ml_free _ ML S pb cap trc6 HWF ltac:(unfold EV_MAX; lia) ltac:(right; rewrite Hbl; left; reflexivity) Htrc6) Hpath6) as (ns6 & HFP).
cbn [free_post snd] in HFP. destruct HFP as (HWF6 & Hnev6 & _). cbn [snd] in Hnev6.
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
assert (HEb : forall a, sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap -> a < alloc_ceiling /\ ~ in_img tfibsegs a) by (intros a Ha; split; [lia | exact (NIMG a Ha)]).
destruct (site_keep_free ly S W (ms_mem msc) md1 ly6 S6 W2 (ms_regs msc) regs6 mem6 md6 _ usp 0%nat HPOST6 HAR1 HEb ltac:(rewrite Hsp1; lia) Ulo HE1 HSO1) as [HE6 HSO6].
pose proof jf_checks as (FK1 & FK2 & FK3 & FK4 & FK5 & FKsub).
pose proof (drv_after_call B HB ARL K_JF E2 S_JFc msc ly S W md1 (fun a => sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap)
ly6 S6 W2 regs6 mem6 md6 (JFR :: IMG_X) RA_JF usp (-128) HSc Qrv FK1 FK2 FK3 FK4 FKsub Qra HPOST6 HAR1 HEb
FK5 E2_0 E2_6 Hsp1 ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin1; lia)) as HS7.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_Jx_eq)))))) in HS7.
set (E6 := havoc E2 K_JF (map (getr regs6) CLOB)) in *.
assert (E6old : forall j, (j < K_JF)%nat -> ew E6 j = ew E2 j) by (intros j Hj; subst E6; apply ew_havoc_old; exact Hj).
assert (E6_0 : bv_unsigned (ew E6 0) = usp) by (rewrite E6old by (unfold K_JF; lia); exact E2_0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 (in_fs inp)))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
apply (run_to_exit 4%nat S_JFr E6 W2 _ md6 ly6 S6 usp (in_fs inp) 2 0%nat IMG_X (-128) true ltac:(lia)); [| | left; reflexivity | | right; reflexivity | ..].
+ cbn [nth XSTS]. rewrite QMr. exact (jfx_run E6 W2 _ md6 HS7).
+ exact QMr.
+ left. reflexivity.
+ exact E6_0.
+ exact (conj Ulo Uhi).
+ exact U16.
+ rewrite E6old by (unfold K_JF; lia). rewrite E2old by (unfold KJ; lia). exact Htid.
+ reflexivity.
+ right. reflexivity.
+ exact HAI2.
+ exact HAR6.
+ exact (top_ok_le _ _ _ _ Hlyle6 HTOP).
+ rewrite Hnev6. unfold EV_MAX. lia.
+ exact HE6.
+ exact HSO6.
+ intros Hk. exfalso. lia.
+ rewrite Efs6. subst md1. rewrite wvb_fs', (sbm_fs_eq _ md' Hsbm). exact Hfs.
Qed.
Theorem tfib_short_leaf : short_leaf_tfa B.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hdl HT.
apply (fw_leaf true (havoc (YP08.E0 sp [a0; p] (in_envp inp) xw xd) K_M1 ws) sp inp a0 p data W ms md ly S pb cap Hsp).
- rewrite ew_havoc_old by (unfold K_M1; lia). exact (AD29.EL6 sp inp xw xd a0 p Hsp Hva Hve).
- rewrite ew_havoc_old by (unfold K_M1; lia). reflexivity.
- exact HT.
Qed.
Theorem tfib_overrun_leaf : overrun_leaf_tfa B.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hdl HT.
apply (fw_leaf false (edset (havoc (YP08.E0 sp [a0; p] (in_envp inp) xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap Hsp).
- cbn [ew edset]. rewrite ew_havoc_old by (unfold K_M1; lia). exact (AD29.EL6 sp inp xw xd a0 p Hsp Hva Hve).
- cbn [ew edset]. rewrite ew_havoc_old by (unfold K_M1; lia). reflexivity.
- exact HT.
Qed.
End f.
End d.
