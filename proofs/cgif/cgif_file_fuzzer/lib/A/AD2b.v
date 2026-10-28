(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma list_len2p {X} : forall (l : list X), (2 <= length l)%nat -> exists a b r, l = a :: b :: r.
Proof. intros [|a [|b r]] H; cbn in H; try lia. exists a, b, r. reflexivity. Qed.
Lemma nth_error_skipn_add {A} : forall (l : list A) n k, nth_error (skipn n l) k = nth_error l (n + k)%nat.
Proof. induction l as [|x l IH]; intros [|n] k; cbn; try reflexivity. - destruct k; reflexivity. - apply IH. Qed.
Lemma submem_app_r : forall rs l, submem rs (rs ++ l).
Proof. induction rs as [|r rs IH]; intros l; cbn; [constructor|]. apply submem_keep; [repeat split; try lia; auto | apply IH]. Qed.
Lemma S_Pm_hlo : forallb (fun r => match r_base r with None => (0x10000 <=? r_lo r) | _ => true end) (ss_mem S_Pm) = true.
Proof. vm_compute. reflexivity. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YP08.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma hdr_regions_ok : forall (E3 : YP0m.env) (H : word -> bool) m data buf pP h,
bv_unsigned (ew E3 A_BUF) = buf -> bv_unsigned (ew E3 161) = pP -> ed E3 2 = data -> ed E3 3 = skipn (Z.to_nat (2 + config_len data)) data ->
pP = buf + 2 + config_len data -> 6 + config_len data <= dlen data -> 2 <= h <= 3 -> 0 <= buf -> buf + dlen data <= 2 ^ 64 ->
blk H m buf (dlen data) data ->
Forall (region_ok tfibsegs E3 (mrestrict H m)) [RBh h; R161].
Proof.
intros E3 H m data buf pP h E41 E60 Ed2 Ed3 HpP Hok Hh Hb0 Hbhi HBLK. pose proof (config_len_bound data) as Hcl. unfold dlen in *.
constructor; [| constructor; [| constructor]].
- split; [cbn [base_val r_base r_lo RBh]; rewrite E41; lia|]. split; [cbn [base_val r_base r_hi RBh]; rewrite E41; lia|].
split; [cbn [r_wlo r_whi RBh]; intros o Ho; lia|].
constructor; [| constructor]. intros i Hi. cbn in Hi. cbn [YP09.c_off YP09.c_val c_len cv_len RBh base_val r_base r_chunks cbyte]. rewrite E41.
pose proof (HBLK i ltac:(lia)) as Hb.
destruct (nth_error data (Z.to_nat i)) as [b|] eqn:En; [| apply nth_error_None in En; lia].
exists b. split; [rewrite Ed2, ?Z.add_0_l; exact En|].
unfold mbyte. rewrite ?Z.add_0_r in Hb. rewrite ?Z.add_0_r. rewrite Hb. reflexivity.
- split; [cbn [base_val r_base r_lo R161]; rewrite E60; lia|]. split; [cbn [base_val r_base r_hi R161]; rewrite E60; lia|].
split; [cbn [r_wlo r_whi R161]; intros o Ho; lia|].
constructor; [| constructor]. intros i Hi. cbn in Hi. cbn [YP09.c_off YP09.c_val c_len cv_len R161 base_val r_base r_chunks cbyte]. rewrite E60.
pose proof (HBLK (2 + config_len data + i) ltac:(lia)) as Hb.
destruct (nth_error data (Z.to_nat (2 + config_len data + i))) as [b|] eqn:En; [| apply nth_error_None in En; lia].
exists b. split.
+ rewrite Ed3, ?Z.add_0_l, nth_error_skipn_add. rewrite <- En. f_equal. lia.
+ unfold mbyte. rewrite ?Z.add_0_r. replace (pP + i) with (buf + (2 + config_len data + i)) by lia. rewrite Hb. reflexivity.
Qed.
Theorem tfib_to_P : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
let E' := edset (havoc EL K_M1 ws) 2 data in
let buf := sptr_addr B ly pb in
6 + config_len data <= dlen data ->
tail_at B S_P E' sp inp a0 p data W ms md ly S pb cap ->
st_ok tfibsegs (E_P E' data (buf + 2 + config_len data)) (if config_len data =? 0 then ssP0 else ssP1) (restrict (w_H W) ms)
/\ bv_unsigned (ew (E_P E' data (buf + 2 + config_len data)) K_PP) = buf + 2 + config_len data.
Proof.
intros ws W ms md ly S data pb cap E' buf Hok (HS & E41 & E42 & HR & HAI & HAR & HTOP & Hbl & Hnev & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HFI).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (config_len_bound data) as Hcl. fold buf in E41, HBLK. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (al_client_img _ _ ARL ly S W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
set (pP := buf + 2 + config_len data). set (E3 := E_P E' data pP).
assert (HpP : 0 <= pP < 2 ^ 64) by (subst pP; lia).
assert (E3_60 : bv_unsigned (ew E3 161) = pP) by (subst E3; apply E_P_161; exact HpP).
assert (E3_41 : bv_unsigned (ew E3 A_BUF) = buf) by (subst E3; rewrite E_P_old by (unfold A_BUF; lia); exact E41).
assert (E3_42 : bv_unsigned (ew E3 A_LEN) = Z.of_nat (length data)) by (subst E3; rewrite E_P_old by (unfold A_LEN; lia); exact E42).
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3 E'; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Ed2 : ed E3 2 = data) by (subst E3 E'; rewrite E_P_ed by lia; reflexivity).
destruct (list_len2p data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hd : ed E3 2 = d0 :: d1 :: rest) by (rewrite Ed2; exact Ed).
split; [| exact E3_60].
pose proof S_Pm_facts as (Hmem & Hpc & Hrv & Hregs & Hfacts & Hwfm).
assert (HS1 : st_ok tfibsegs E' S_Pm (restrict (w_H W) ms)).
{ destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold st_ok. rewrite Hpc, Hrv, Hregs, Hfacts.
repeat (split; [assumption|]). split; [| exact H9].
apply (mem_ok_sub tfibsegs E' _ (ss_mem S_P)); [rewrite Hmem; apply submem_app_r | exact Hwfm | exact H8]. }
pose proof (st_ok_agree_pd tfibsegs _ _ E' E3 S_Pm _ HS1 (E_P_agree E' data pP) S_Pm_pd) as HS2. clear HS1.
destruct HS2 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (HS3 : st_ok tfibsegs E3 (mkSS (ss_pc S_Pm) (sr_set (ss_regs S_Pm) 10%bv (SOff 161 0)) (ss_mem S_Pm) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_Pm)) (f_conds (ss_facts S_Pm)) (f_alias (ss_facts S_Pm))))
(restrict (w_H W) ms)).
{ unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [| split; [exact H8|]].
- intros r. destruct (decide (r = 10%bv)) as [->|Hne].
+ rewrite sr_get_set_same by reflexivity. rewrite (H7 10%bv). rewrite Hregs, (proj1 (proj2 (proj2 (proj2 S_P_regs)))).
rewrite (denot_lit_U E3 (SOff 161 0)), (denot_lit_U E3 (SAlu ALU_ADD (SOff A_BUF 2) sv_cl)). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, (U_cl E3 d0 d1 rest Hd), E3_41, E3_60, <- Ed.
rewrite (zcanon_id (buf + 2)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). subst pP. lia.
+ rewrite sr_get_set_other by exact Hne. apply H7.
- apply facts_ok_add_atom; [exact H9|]. unfold afact_ok, fact_P. cbn [af_lo af_hi af_al2]. rewrite E3_60.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. subst pP. lia. }
set (h := if config_len data =? 0 then 2 else 3).
assert (Hh : 2 <= h <= 3) by (subst h; destruct (config_len data =? 0); lia).
assert (HS4 : st_ok tfibsegs E3 (mkSS (ss_pc S_Pm) (sr_set (ss_regs S_Pm) 10%bv (SOff 161 0)) (ss_mem S_Pm ++ [RBh h; R161]) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_Pm)) (f_conds (ss_facts S_Pm)) (f_alias (ss_facts S_Pm))))
(restrict (w_H W) ms)).
{ apply (st_ok_app_regions E3 _ (restrict (w_H W) ms) [RBh h; R161] HS3 (RBh_wf h Hh)).
- cbn [ms_mem restrict]. apply (hdr_regions_ok E3 (w_H W) (ms_mem ms) data buf pP h E3_41 E3_60 Ed2); try assumption; try (unfold dlen; lia).
subst E3. apply E_P_ed3.
- cbn. split; [| exact (conj I I)]. split; [| exact I].
unfold extent_disjoint. cbn [base_val r_base r_lo r_hi RBh R161]. rewrite E3_41, E3_60. left. subst pP h.
destruct (Z.eqb_spec (config_len data) 0); lia.
- intros r1 r2 Hr1 Hr2.
pose proof (proj1 (forallb_forall _ _) S_Pm_hext r1 Hr1) as Y. unfold hext_chk in Y.
pose proof (proj1 (forallb_forall _ _) S_Pm_hlo r1 Hr1) as Y2. cbn beta in Y2.
assert (LO : forall lo2 hi2, buf <= lo2 -> hi2 <= buf + cap ->
base_val E3 (r_base r1) + r_hi r1 <= lo2 \/ hi2 <= base_val E3 (r_base r1) + r_lo r1).
{ intros lo2 hi2 Hlo2 Hhi2. destruct (r_base r1) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate Y; cbn [base_val].
+ apply Z.leb_le in Y. rewrite E3_0. unfold sp_window_lo in Ulo. right. lia.
+ apply Z.leb_le in Y. subst E3 E'. rewrite E_P_old by lia. cbn [ew edset]. rewrite ew_havoc_old by (unfold K_M1; lia).
pose proof EL6 as R6. unfold sp_window_lo in Ulo. right. lia.
+ apply Z.leb_le in Y. apply Z.leb_le in Y2.
destruct (Z.le_gt_cases (r_hi r1) lo2) as [|Hgt]; [left; lia|]. destruct (Z.le_gt_cases hi2 (r_lo r1)) as [|Hgt2]; [right; lia|].
exfalso. apply (NIMG (Z.max buf 0x10000)); [lia|]. apply in_img_hull. lia. }
unfold extent_disjoint. destruct Hr2 as [<- | [<- | []]]; cbn [base_val r_base r_lo r_hi RBh R161]; [rewrite E3_41 | rewrite E3_60]; apply LO; subst pP; lia. }
subst h. rewrite Hpc, Hregs, Hfacts in HS4. pose proof ssP_eq as [Q2 Q3].
destruct (config_len data =? 0); [rewrite <- Q2 | rewrite <- Q3]; exact HS4.
Qed.
End d.
End c.
