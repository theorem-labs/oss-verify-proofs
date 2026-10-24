(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1j YK0v YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO14 YO0t YO0x YO0e YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z YO0v YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN02 YN2b YN31 YN25 YN26 YN29 YN28 YN2a YN27 YN0b YN07 YN09 YN0a YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma resume_ss_mem : forall ss rv rs G, ss_mem (resume ss rv rs G) = rs.
Proof. reflexivity. Qed.
Lemma chunk_ok_bytes xv m base off (w : N) e v :
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w e)) ->
bv_unsigned (sv_denot (EV xv) e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_are m (base + off) (N.to_nat w) v.
Proof.
intros Hc Hv Hr k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn [c_len cv_len c_val]; lia)) as (b & Eb & Mb).
cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word, le_byte. rewrite Hv, Z_to_bv8_mod. f_equal. rewrite N_nat_Z. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma raw_eq_of_mbyte m m' x :
present m x -> present m' x -> mbyte src0segs m' x = mbyte src0segs m x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof. intros [b Hb] [b' Hb'] E. unfold mbyte in E. rewrite Hb, Hb' in *. congruence. Qed.
Lemma bytes_are_present_eq m m' x0 w val x :
bytes_are m x0 w val -> bytes_are m' x0 w val -> x0 <= x < x0 + Z.of_nat w ->
present m x -> present m' x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
intros B B' Hx P P'. apply raw_eq_of_mbyte; [exact P | exact P' |].
replace x with (x0 + Z.of_nat (Z.to_nat (x - x0))) by lia. rewrite B, B' by lia. reflexivity.
Qed.
Lemma ret_ok_after_nt : YK0s.ret_ok (Z_to_bv 64 FREE_AFTER_NT).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma sr_get_nat sr n : (1 <= n <= 31)%nat -> sr_get sr (nat_to_reg n) = nth n sr (SLit 0).
Proof. intros Hn. do 32 (destruct n as [|n]; [reflexivity || lia|]). lia. Qed.
Lemma regs_ok_intro E sr (rg : bvmap 5 word) :
sr_get sr (nat_to_reg 0) = SLit 0 ->
(forall n, (1 <= n <= 31)%nat -> getr rg (nat_to_reg n) = sv_denot E (nth n sr (SLit 0))) -> regs_ok E sr rg.
Proof.
intros H0 H r. rewrite <- (nat_to_reg_ridx r). pose proof (u5_range r) as Hr.
destruct (Nat.eq_dec (Z.to_nat (bv_unsigned r)) 0) as [E0|NE].
- rewrite E0. rewrite H0. cbn [nat_to_reg sv_denot]. unfold getr. cbn. reflexivity.
- rewrite sr_get_nat by lia. apply H. lia.
Qed.
Definition ERRNO : Z := errno_addr B1.
Lemma errno_rom k : (k < 4)%nat -> seg_rom src0segs (Z_to_bv 64 (ERRNO + Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof.
intros Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma le_byte4 (v0 v1 v2 v3 : Z) k :
0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> (k < 4)%nat ->
le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 k = nth k [v0; v1; v2; v3] 0.
Proof.
intros H0 H1 H2 H3 Hk. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth Z.of_nat Z.mul Pos.of_succ_nat Pos.mul Pos.succ].
- change (2 ^ 0) with 1. rewrite Z.div_1_r.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with (v0 + (v1 + 256 * v2 + 65536 * v3) * 256) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- change (2 ^ 8) with 256.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with (v0 + (v1 + (v2 + 256 * v3) * 256) * 256) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l, Z_mod_plus_full by lia. apply Z.mod_small. lia.
- change (2 ^ 16) with 65536.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with ((v0 + 256 * v1) + (v2 + v3 * 256) * 65536) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l, Z_mod_plus_full by lia. apply Z.mod_small. lia.
- change (2 ^ 24) with 16777216.
replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with ((v0 + 256 * v1 + 65536 * v2) + v3 * 16777216) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. apply Z.mod_small. lia.
Qed.
Lemma errno_bytes_any m : exists err, 0 <= err < 2 ^ 32 /\ bytes_are m ERRNO 4 err.
Proof.
assert (B : forall k, (k < 4)%nat -> exists b : byte, mbyte src0segs m (ERRNO + Z.of_nat k) = Some b).
{ intros k Hk. unfold mbyte. destruct (m (Z_to_bv 64 (ERRNO + Z.of_nat k))) as [b|]; [exists b; reflexivity|].
rewrite (errno_rom k Hk). eexists; reflexivity. }
destruct (B 0%nat ltac:(lia)) as [b0 H0]. destruct (B 1%nat ltac:(lia)) as [b1 H1].
destruct (B 2%nat ltac:(lia)) as [b2 H2]. destruct (B 3%nat ltac:(lia)) as [b3 H3].
pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
exists (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
split; [lia|]. intros k Hk. rewrite le_byte4 by assumption.
destruct k as [|[|[|[|k]]]]; [rewrite H0 | rewrite H1 | rewrite H2 | rewrite H3 | lia]; cbn [nth]; rewrite Z_to_bv_bv_unsigned; reflexivity.
Qed.
Lemma areas_cells_ext s s' l : st_metas s' = st_metas s -> areas_cells s' l = areas_cells s l.
Proof. intros E. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. f_equal. unfold area_cells. rewrite E. reflexivity. Qed.
Lemma image_set_regions f s : image (set_regions f s) = image s.
Proof. unfold image. rewrite (areas_cells_ext s (set_regions f s)) by reflexivity. reflexivity. Qed.
Section h.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame).
Variables (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : free_ctx L A regs mem md g am idx fr a ka rg.
Let PRE : call_pre B1 (MRx B1) L A regs mem md := fc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hu : usedX [] A g am := fc_used _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hidx : 0 <= idx <= am_last am := fc_idx _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hfr : ss_fr (nth_slot am idx) = Some fr := fc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hk : fr_kind fr = FUser := fc_kind _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hin : In (frame_ptr am idx fr, fr_n fr) (user_blocks A) := fc_in _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Ha0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am idx fr)) := fc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Harea : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka) := fc_area _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hrg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg := fc_rg _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let p := frame_ptr am idx fr.
Let P := ptr_addr L p.
Let G := ptr_addr L g.
Let SP := spZ regs.
Let kc' := kc am.
Let rc' := rcv am fr.
Let v := vv L regs g am idx fr a rg.
Let FPv : free_pre kc' rc' v mem := FP L A regs mem md g am idx fr a ka rg HC.
Let XR := xvf_range _ _ _ _ FPv.
Let am1 := am_rel idx am.
Let A1 := upd_meta g (MUsed am1) A.
Let M : MRc B1 L A mem md := M L A regs mem md g am idx fr a ka rg HC.
Let HWA : WF A := HW L A regs mem md g am idx fr a ka rg HC.
Let Mg' : MT A g = Some (MUsed am) := Mg L A regs mem md g am idx fr a ka rg HC.
Lemma HI1 : Inv [] (Some (g, idx)) U0 A1.
Proof.
unfold A1, am1, am_rel. eapply drop_frame_Inv; [exact HWA | exact Hu | exact Hidx | exact Hfr | | |].
- intros HG. rewrite Hk in HG. discriminate.
- apply released_slot_fr. rewrite Hfr. discriminate.
- unfold released_slot. rewrite Hfr. destruct (fr_off fr =? 0); cbn; auto.
Qed.
Lemma Hu1 : usedX [] A1 g am1.
Proof. unfold A1. apply usedX_upd. left. auto. Qed.
Lemma ND_A : List.NoDup (keys A). Proof. exact (proj1 (inv_keys HWA)). Qed.
Lemma ND_A1 : List.NoDup (keys A1). Proof. exact (proj1 (inv_keys HI1)). Qed.
Lemma blocks_A1 : exists l1 l2, user_blocks A = l1 ++ (p, fr_n fr) :: l2 /\ user_blocks A1 = l1 ++ l2.
Proof.
pose proof (inv_groups HWA g am Hu) as ((_ & _ & Glen & _) & _).
destruct (ublist_upd_slot A g am idx (released_slot idx am) ND_A Mg' Hidx Glen) as (l1 & l2 & E1 & E2).
exists (map fst l1), (map fst l2).
rewrite (user_blocks_ublist A ND_A), (user_blocks_ublist A1 ND_A1). unfold A1, am1, am_rel. rewrite E1, E2, !map_app.
unfold slot_block, slotst_block. rewrite Hfr, Hk. rewrite (released_slot_fr idx am) by (rewrite Hfr; discriminate).
cbn [map fst app]. split; reflexivity.
Qed.
Lemma owned_A1 x : alloc_owned L A1 x -> alloc_owned L A x \/ (P <= x < P + fr_n fr).
Proof.
intros [Hf Hnb]. destruct (Z_le_dec P x); [destruct (Z_lt_dec x (P + fr_n fr)); [right; lia|]|]; left; split; try exact Hf;
intros (b & Hb & Hxb); apply Hnb; destruct blocks_A1 as (l1 & l2 & E1 & E2);
rewrite E1 in Hb; apply in_app_iff in Hb;
(destruct Hb as [Hb | [<- | Hb]]; [exists b; rewrite E2; split; [apply in_app_iff; left; exact Hb | exact Hxb]
| exfalso; change (loc_addr L (LMem (fst (p, fr_n fr)))) with P in Hxb; cbn [snd] in Hxb; lia
| exists b; rewrite E2; split; [apply in_app_iff; right; exact Hb | exact Hxb]]).
Qed.
Lemma ring_cond : fast_cond idx am = false ->
(am_prev am1, am_next am1) <> (None, None) -> active_hd A1 (am_sc am1) <> Some g -> am_freed am1 <> 0.
Proof.
intros FC. pose proof (inv_groups HWA g am Hu) as GG. pose proof GG as ((Glast & _) & _ & Gsl & Gcl & _).
assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
replace (am_prev am1, am_next am1) with (am_prev am, am_next am) by (unfold am1, am_rel, upd_slot; destruct am; reflexivity).
replace (am_freed am1) with (am_freed am) by (unfold am1, am_rel, upd_slot; destruct am; reflexivity).
replace (am_sc am1) with (am_sc am) by (unfold am1, am_rel, upd_slot; destruct am; reflexivity).
replace (active_hd A1 (am_sc am)) with (active_hd A (am_sc am)) by reflexivity.
intros HL Hnh. destruct Hscr as [H63|Hsc].
{ exfalso. destruct (inv_rings HWA) as (_ & _ & D). destruct (D g am Hu H63) as [P0 N0]. apply HL. rewrite P0, N0. reflexivity. }
destruct (ring_facts [] None U0 A g am HWA Hu ltac:(lia) ltac:(lia)) as (_ & _ & RF3). apply RF3; [exact HL | exact Hnh | intros; discriminate].
Qed.
Lemma fneed_ok : (fneed (am_sc am1) <= NEST_FUEL)%nat.
Proof.
pose proof (inv_groups HWA g am Hu) as (_ & _ & _ & Gcl & _).
replace (am_sc am1) with (am_sc am) by (unfold am1, am_rel, upd_slot; destruct am; reflexivity).
apply fneed_le. destruct Gcl as [(C & _) | (C & _)]; lia.
Qed.
Lemma slow_cases : fast_cond idx am = false ->
fv_fr v = 0 \/ (fv_fr v <> 0 /\ Z.lor (fv_av v) (fv_fr v) + 2 ^ fv_idx v = ones (fv_last v)).
Proof.
intros FC. unfold fast_cond, mask0, bit in FC.
change (fv_fr v) with (am_freed am). change (fv_av v) with (am_avail am). change (fv_idx v) with idx. change (fv_last v) with (am_last am).
destruct (Z.eq_dec (am_freed am) 0) as [E|E]; [left; exact E | right]. split; [exact E|].
replace (am_freed am =? 0) with false in FC by (symmetry; apply Z.eqb_neq; exact E). cbn [negb andb] in FC.
apply negb_false_iff in FC. apply Z.eqb_eq in FC. rewrite Z.lor_comm. exact FC.
Qed.
Definition NTS (ms1 : machine_state) : Prop :=
exists ss, (ss = SSNA kc' rc' \/ ss = SSNB kc' rc') /\ st_ok src0segs (EV (xvf v)) ss ms1 /\
frame_of (EV (xvf v)) (free_mem kc' rc') mem (ms_mem ms1).
Lemma nts_shape ss : ss = SSNA kc' rc' \/ ss = SSNB kc' rc' ->
ss_pc ss = src0_A_nontrivial_free /\ ss_resv ss = None /\ nt_view ss = nt_view0 /\ ss_mem ss = mem_at_nt kc' rc'.
Proof. intros [-> | ->]; [apply SSNA_shape | apply SSNB_shape]. Qed.
Lemma to_nt : fast_cond idx am = false ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs)) md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ NTS ms1).
Proof.
intros FC. destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
pose proof (HS0 L A regs mem md g am idx fr a ka rg HC) as HS. change (st_ok src0segs (EV (xvf v)) (ss_free kc' rc') (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs))) in HS.
destruct (slow_cases FC) as [Z0 | [NZ EQ]].
- assert (HSA : st_ok src0segs (EV (xvf v)) (ss_slowA kc' rc') (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs))).
{ unfold ss_slowA, cond_slowA. apply st_ok_add_cond; [exact HS | exact (taken_slowA _ _ _ _ FPv Z0)]. }
eapply SR_mono; [exact (free_slowA_run kc' rc' _ _ md HSA Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. exists (SSNA kc' rc'). split; [left; reflexivity|]. split; [exact HS1 | exact HF].
- assert (HSB : st_ok src0segs (EV (xvf v)) (ss_slowB kc' rc') (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs))).
{ unfold ss_slowB, cond_fastA, cond_slowB. apply st_ok_add_cond; [apply st_ok_add_cond; [exact HS | exact (taken_fastA _ _ _ _ FPv NZ)] | exact (taken_slowB _ _ _ _ FPv EQ)]. }
eapply SR_mono; [exact (free_slowB_run kc' rc' _ _ md HSB Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. exists (SSNB kc' rc'). split; [right; reflexivity|]. split; [exact HS1 | exact HF].
Qed.
Let E_Pv : fv_p v = P := E_P L A regs mem md g am idx fr a ka rg HC.
Lemma XV2 : xvf v 2 = SP. Proof. reflexivity. Qed.
Lemma XVP : xvf v aP = P. Proof. exact E_Pv. Qed.
Lemma XVG : xvf v aG = G. Proof. reflexivity. Qed.
Lemma XVIDX : xvf v aIDX = idx. Proof. reflexivity. Qed.
Lemma XVFR : xvf v aFR = am_freed am. Proof. reflexivity. Qed.
Lemma SPf : alloc_ceiling + 8192 <= SP /\ SP < 2 ^ 63 /\ SP mod 16 = 0.
Proof. pose proof PRE as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). unfold ALLOC_STACK in Hceil. unfold SP. repeat split; lia. Qed.
Lemma Pf : 4096 <= P /\ P + fr_n fr <= alloc_ceiling /\ 0 <= fr_n fr.
Proof. exact (P_range L A regs mem md g am idx fr a ka rg HC). Qed.
Lemma block_off_img x : P <= x < P + fr_n fr -> ~ in_img1 x.
Proof.
intros Hx Hi. destruct (block_region A p (fr_n fr) HWA Hin) as (kr & o & rg0 & Ep & Hrg0 & _ & Hl0 & Ho & Hn & Hon & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) kr rg0 Hrg0 Hl0) as (_ & _ & _ & Himg).
apply (Himg x); [| apply in_img1_in_img; exact Hi]. unfold P, ptr_addr in Hx. rewrite Ep in Hx. cbn [loc_addr] in Hx. lia.
Qed.
Lemma Gf : 4096 <= G /\ G + 40 <= alloc_ceiling.
Proof.
pose proof (fp_ar _ _ _ _ FPv) as (A1' & A2 & _ & A4 & A5 & _). change (fv_g v) with G in A4, A5. unfold CEIL in A2. pose proof (proj1 alloc_ceiling_val). lia.
Qed.
Lemma nt_regs ms1 : NTS ms1 ->
ms1 = mkst (ms_regs ms1) (Z_to_bv 64 src0_A_nontrivial_free) (ms_mem ms1) (seg_rom src0segs) /\
getr (ms_regs ms1) 1 = Z_to_bv 64 FREE_AFTER_NT /\ getr (ms_regs ms1) 2 = Z_to_bv 64 (SP - 48) /\
getr (ms_regs ms1) 3 = getr regs 3 /\ getr (ms_regs ms1) 4 = getr regs 4 /\
getr (ms_regs ms1) 8 = Z_to_bv 64 idx /\ getr (ms_regs ms1) 9 = Z_to_bv 64 P /\
getr (ms_regs ms1) 10 = Z_to_bv 64 G /\ getr (ms_regs ms1) 11 = Z_to_bv 64 idx /\
(forall i, In i [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr (ms_regs ms1) (nat_to_reg i) = getr regs (nat_to_reg i)).
Proof.
intros (ss & Hss & HS1 & _). destruct (nts_shape ss Hss) as (Hpc & Hrv & Hview & _).
split; [rewrite (st_ok_mkst src0segs _ ss ms1 HS1 Hrv), Hpc; reflexivity|].
pose proof (fun r => st_ok_reg src0segs _ ss ms1 r HS1) as R.
unfold nt_view, nt_view0 in Hview. cbn [map] in Hview.
injection Hview as V1 V2 V3 V4 V8 V9 V10 V11 V18 V19 V20 V21 V22 V23 V24 V25 V26 V27.
pose proof SPf as (S1 & S2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
Ltac greg R k n V := rewrite (R k); replace k with (Z_to_bv 5 (Z.of_nat n)) by (apply bv_eq; reflexivity); rewrite V.
repeat match goal with |- _ /\ _ => split end.
- greg R (1%bv : bv 5) 1%nat V1. reflexivity.
- greg R (2%bv : bv 5) 2%nat V2. rewrite (den_off _ XR) by (rewrite XV2; lia). rewrite XV2. reflexivity.
- greg R (3%bv : bv 5) 3%nat V3. rewrite (den_off0 _ XR). rewrite xvf_reg by lia. apply Z_to_bv_bv_unsigned.
- greg R (4%bv : bv 5) 4%nat V4. rewrite (den_off0 _ XR). rewrite xvf_reg by lia. apply Z_to_bv_bv_unsigned.
- greg R (8%bv : bv 5) 8%nat V8. rewrite (den_off0 _ XR). reflexivity.
- greg R (9%bv : bv 5) 9%nat V9. rewrite (den_off0 _ XR), XVP. reflexivity.
- greg R (10%bv : bv 5) 10%nat V10. rewrite (den_off0 _ XR). reflexivity.
- greg R (11%bv : bv 5) 11%nat V11. rewrite (den_off0 _ XR). reflexivity.
- intros i Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [nat_to_reg];
[ greg R (18%bv : bv 5) 18%nat V18 | greg R (19%bv : bv 5) 19%nat V19 | greg R (20%bv : bv 5) 20%nat V20 | greg R (21%bv : bv 5) 21%nat V21
| greg R (22%bv : bv 5) 22%nat V22 | greg R (23%bv : bv 5) 23%nat V23 | greg R (24%bv : bv 5) 24%nat V24 | greg R (25%bv : bv 5) 25%nat V25
| greg R (26%bv : bv 5) 26%nat V26 | greg R (27%bv : bv 5) 27%nat V27 ];
rewrite (den_off0 _ XR); rewrite xvf_reg by lia; apply Z_to_bv_bv_unsigned.
Qed.
Lemma nt_mem ms1 : NTS ms1 ->
let m1 := ms_mem ms1 in
(forall x, 0 <= x < 2 ^ 64 -> ~ (P - 3 <= x < P) -> ~ (SP - 8192 <= x < SP) -> m1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(mbyte src0segs m1 (P - 3) = Some (Z_to_bv 8 255) /\ mbyte src0segs m1 (P - 2) = Some (Z_to_bv 8 0) /\ mbyte src0segs m1 (P - 1) = Some (Z_to_bv 8 0)) /\
(forall x, P - 3 <= x < P -> present m1 x) /\
(forall x, SP - 8192 <= x < SP -> writable_at src0segs m1 x) /\
(bytes_are m1 (SP - 40) 8 (bv_unsigned (getr regs 19)) /\ bytes_are m1 (SP - 32) 8 (bv_unsigned (getr regs 18)) /\
bytes_are m1 (SP - 24) 8 (bv_unsigned (getr regs 9)) /\ bytes_are m1 (SP - 16) 8 (bv_unsigned (getr regs 8)) /\
bytes_are m1 (SP - 8) 8 (bv_unsigned (getr regs 1))).
Proof.
intros (ss & Hss & HS1 & HF). destruct (nts_shape ss Hss) as (_ & _ & _ & Hsm). cbn zeta.
pose proof (st_ok_mem_ok _ _ _ _ HS1) as (_ & ROK & _). rewrite Hsm in ROK. unfold mem_at_nt in ROK.
apply Forall_cons_iff in ROK as [Rhdr ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rmeta ROK].
apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rstk _].
destruct Rhdr as (_ & _ & Wh & Chdr). destruct Rmeta as (_ & _ & Wm & Cmeta). destruct Rstk as (_ & _ & Wstk & Cstk).
cbn [r_base r_chunks r_wlo r_whi reg_meta] in *. rewrite !(base_val_EV (xvf v) XR) in *.
rewrite !XVP in *. change (xvf v aG) with G in *. change (xvf v aSP) with SP in *.
apply Forall_cons_iff in Chdr as [C2 Chdr]. apply Forall_cons_iff in Chdr as [C3 _].
apply Forall_cons_iff in Cmeta as [_ Cmeta]. apply Forall_cons_iff in Cmeta as [_ Cmeta]. apply Forall_cons_iff in Cmeta as [C28 _].
apply Forall_cons_iff in Cstk as [S40 Cstk]. apply Forall_cons_iff in Cstk as [S32 Cstk]. apply Forall_cons_iff in Cstk as [S24 Cstk].
apply Forall_cons_iff in Cstk as [S16 Cstk]. apply Forall_cons_iff in Cstk as [S8 _].
pose proof Pf as (P1 & P2 & P3). pose proof Gf as [G1 G2]. pose proof SPf as (S1 & S2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (WOI : forall x, (P - 3 <= x < P) \/ (G + 28 <= x < G + 32) -> ~ in_img1 x /\ 0 <= x < alloc_ceiling) by exact (win_off_img L A regs mem md g am idx fr a ka rg HC).
assert (B2 : bytes_are (ms_mem ms1) (P - 2) 2 0).
{ replace (P - 2) with (P + -2) by lia. apply (chunk_ok_bytes _ _ _ _ 2%N (SLit 0) 0 C2); [reflexivity | cbn; lia]. }
assert (B3 : mbyte src0segs (ms_mem ms1) (P - 3) = Some (Z_to_bv 8 255)).
{ destruct (C3 0 ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb.
replace (P - 3) with (P + -3 + 0) by lia. rewrite Mb. injection Eb as <-. f_equal. apply bv_eq. vm_compute. reflexivity. }
assert (B28 : bytes_are (ms_mem ms1) (G + 28) 4 (am_freed am)).
{ apply (chunk_ok_bytes _ _ _ _ 4%N (SOff aFR 0) _ C28); [rewrite (U_off0 _ XR), XVFR; reflexivity|].
pose proof (lin_facts _ _ _ _ FPv) as LF; cbn zeta in LF. change (fv_fr v) with (am_freed am) in LF. cbn. lia. }
assert (STK : forall off n, chunk_ok src0segs (EV (xvf v)) (ms_mem ms1) SP (mkChunk off (CVal 8 (SOff n 0))) -> (n <= 31)%nat ->
bytes_are (ms_mem ms1) (SP + off) 8 (bv_unsigned (getr regs (nat_to_reg n)))).
{ intros off n C Hn. apply (chunk_ok_bytes _ _ _ _ 8%N (SOff n 0) _ C); [rewrite (U_off0 _ XR), xvf_reg by lia; reflexivity|].
cbn. apply (u64_range (getr regs (nat_to_reg n))). }
split; [|split; [split; [|split]|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
-   intros x Hx N1 N2.
destruct (Z_lt_dec x (G + 28)) as [L1|L1]; [| destruct (Z_lt_dec x (G + 32)) as [L2|L2]].
2:{
pose proof (fp_c_g28 _ _ _ _ FPv) as OLD. change (fv_g v) with G in OLD. change (fv_fr v) with (am_freed am) in OLD.
apply (bytes_are_present_eq mem (ms_mem ms1) (G + 28) 4 (am_freed am) x OLD B28 ltac:(change (Z.of_nat 4) with 4; lia)).
- assert (Wx : G + 28 <= x < G + 32) by lia.
apply writable_off_img_present; [lia | apply (proj1 (WOI x (or_intror Wx))) |].
apply (fp_w_meta _ _ _ _ FPv). change (fv_g v) with G. lia.
- assert (Wx : G + 28 <= x < G + 32) by lia.
apply writable_off_img_present; [lia | apply (proj1 (WOI x (or_intror Wx))) |].
replace x with (G + (x - G)) by lia. apply Wm. lia. }
all: apply HF; rewrite lit64_small by lia; intros W; apply (in_wrange_free _ _ _ _ FPv) in W;
rewrite E_Pv in W; change (fv_g v) with G in W; change (fv_sp v) with SP in W; lia.
- exact B3.
- replace (P - 2) with (P - 2 + Z.of_nat 0) by lia. rewrite (B2 0%nat) by lia. f_equal.
- replace (P - 1) with (P - 2 + Z.of_nat 1) by lia. rewrite (B2 1%nat) by lia. f_equal.
- intros x Hx. apply writable_off_img_present; [lia | apply (proj1 (WOI x (or_introl Hx))) |].
replace x with (P + (x - P)) by lia. apply Wh. lia.
- intros x Hx. replace x with (SP + (x - SP)) by lia. apply Wstk. lia.
- replace (SP - 40) with (SP + -40) by lia. apply (STK _ 19%nat S40). lia.
- replace (SP - 32) with (SP + -32) by lia. apply (STK _ 18%nat S32). lia.
- replace (SP - 24) with (SP + -24) by lia. apply (STK _ 9%nat S24). lia.
- replace (SP - 16) with (SP + -16) by lia. apply (STK _ 8%nat S16). lia.
- replace (SP - 8) with (SP + -8) by lia. apply (STK _ 1%nat S8). lia.
Qed.
Lemma mk_nt_pre ms1 : NTS ms1 -> nt_pre B1 [] NEST_FUEL L A1 (ms_regs ms1) (ms_mem ms1) md g idx.
Proof.
intros HN. pose proof (nt_regs ms1 HN) as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & Rs).
pose proof (nt_mem ms1 HN) as (F1 & F2 & F4 & WSTK & _).
pose proof PRE as (_ & _ & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _).
destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat). pose proof SPf as (S1 & S2 & S3). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof Pf as (P1 & P2 & P3).
destruct (memrep_rel B1 L A mem md g am idx fr (ms_mem ms1) SP M Hu Hidx Hfr HI1 ltac:(lia) F1 F2 F4) as [MREP TG].
apply (proj2 (memrepX_nil B1 L A1 (ms_mem ms1))) in MREP.
assert (ESP : spZ (ms_regs ms1) = SP - 48) by (unfold spZ; rewrite R2; apply lit64_small; lia).
unfold nt_pre. rewrite ESP. unfold NT_FRAME, NEST_FUEL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. change (Z.pow_pos 2 63) with (2 ^ 63).
repeat match goal with |- _ /\ _ => split end; try assumption.
- exact (mc_syms _ _ _ _ _ M).
- unfold A1. apply (proj2 (layout_ok_upd_meta _ _ _ _)). exact (mc_layout _ _ _ _ _ M).
- exact (mc_ctx _ _ _ _ _ M).
- exact (proj1 (mc_sec _ _ _ _ _ M)).
- exact (proj2 (mc_sec _ _ _ _ _ M)).
- apply (statics_ok_ext B1 mem (ms_mem ms1) (mc_statics _ _ _ _ _ M)). intros x Hs.
pose proof (B1_img_range x (so_statics_img _ (mc_syms _ _ _ _ _ M) x Hs)) as Hxi.
apply same_byte_views. apply F1; [lia | | lia].
intros W. apply (proj1 (win_off_img L A regs mem md g am idx fr a ka rg HC x (or_introl W))). unfold in_img1. unfold P in W. lia.
- unfold A1. apply ledger_ok_upd_meta. exact (mc_ledger _ _ _ _ _ M).
- rewrite R1. apply ret_ok_after_nt.
- rewrite <- Zminus_mod_idemp_l, S3. reflexivity.
- lia.
- lia.
- intros x Hx. apply WSTK. lia.
- rewrite R4. exact Htp.
Qed.
Hypothesis NT : ntfree_hyp B1.
Definition NTQ (ms1 : machine_state) (r : option (nat * Z) * astate) (c2 : config) : Prop :=
(nt_post B1 [] NEST_FUEL L A1 (ms_regs ms1) (ms_mem ms1) md r c2 /\ nf_post [] U0 A1 r) /\ ntrel A1 (snd r).
Lemma nt_call ms1 : fast_cond idx am = false -> NTS ms1 ->
mreal src0segs (mkCfg ms1 md) (nontrivial_free NEST_FUEL g idx A1) (NTQ ms1).
Proof.
intros FC HN. pose proof (nt_regs ms1 HN) as (Ems & _). pose proof PRE as (_ & _ & HB & _).
unfold NTQ. apply mreal_tall; [apply mreal_conj; [| apply (nontrivial_free_spec NEST_FUEL [] U0 A1 g idx am1); [exact HI1 | exact Hu1 | apply U0_nonneg | apply (ring_cond FC) | apply fneed_ok | intros r Hr; exact Hr]] | apply nontrivial_free_ntrel].
rewrite Ems at 1. apply (NT NEST_FUEL [] U0 L A1 g idx am1); [exact HI1 | exact Hu1 | apply U0_nonneg | apply (ring_cond FC) | apply fneed_ok | exact HB | apply mk_nt_pre; exact HN].
Qed.
Definition xva (regs2 : bvmap 5 word) (base len err : Z) (n : nat) : Z :=
if (n =? 60)%nat then base else if (n =? 61)%nat then len else if (n =? 62)%nat then err
else if (64 <=? n)%nat && (n <? 96)%nat then bv_unsigned (getr regs2 (nat_to_reg (n - 64))) else xvf v n.
Section u.
Variables (ms1 : machine_state) (mi : option (nat * Z)) (A' : astate) (regs2 : bvmap 5 word) (mem2 : word -> option byte).
Hypothesis FC : fast_cond idx am = false.
Hypothesis HN : NTS ms1.
Hypothesis NP : memrep B1 L A' mem2 /\ statics_ok B1 mem2 /\ regs_preserved (ms_regs ms1) regs2 /\
getr regs2 10 = Z_to_bv 64 (match mi with Some (k, _) => ly_reg L k | None => 0 end) /\
getr regs2 11 = Z_to_bv 64 (match mi with Some (_, len) => len | None => 0 end) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ alloc_owned L A1 x -> ~ (SP - 48 - NT_FRAME * Z.of_nat NEST_FUEL <= x < SP - 48) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem ms1) x /\ (writable_at src0segs (ms_mem ms1) x <-> writable_at src0segs mem2 x)) /\
(forall x, SP - 48 - NT_FRAME * Z.of_nat NEST_FUEL <= x < SP - 48 -> writable_at src0segs mem2 x).
Hypothesis NF : nf_post [] U0 A1 (mi, A').
Hypothesis NR : ntrel A1 A'.
Let base := match mi with Some (k, _) => ly_reg L k | None => 0 end.
Let len := match mi with Some (_, l) => l | None => 0 end.
Let lenz := match mi with Some _ => false | None => true end.
Lemma HW' : WF A'. Proof. exact (proj1 NF). Qed.
Lemma EERR' : ERRNO = 195084. Proof. reflexivity. Qed.
Lemma ETPv : xvf v aTP = 195248.
Proof. pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & _). change (xvf v aTP) with (bv_unsigned (getr regs 4)). rewrite Htp. reflexivity. Qed.
Lemma unch x : 0 <= x < 2 ^ 64 -> ~ alloc_owned L A x -> ~ (P <= x < P + fr_n fr) -> ~ (SP - 8192 <= x < SP) ->
mbyte src0segs mem2 x = mbyte src0segs mem x /\ (writable_at src0segs mem x <-> writable_at src0segs mem2 x).
Proof.
intros Hx NO NE NS. pose proof (nt_mem ms1 HN) as (F1 & _). destruct NP as (_ & _ & _ & _ & _ & FR & _).
assert (NO1 : ~ alloc_owned L A1 x) by (intros O1; destruct (owned_A1 x O1); tauto).
destruct (FR x Hx NO1 ltac:(unfold NT_FRAME, NEST_FUEL; lia)) as [E1 W1].
assert (E0 : ms_mem ms1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ apply F1; [exact Hx | | exact NS]. intros W. apply NO. apply (win_owned L A regs mem md g am idx fr a ka rg HC). left. exact W. }
destruct (same_byte_views mem (ms_mem ms1) x E0) as [E2 W2]. rewrite E1, E2. tauto.
Qed.
Lemma errno_stack_not_owned x : (ERRNO <= x < ERRNO + 4) \/ (SP - 8192 <= x < SP) -> ~ alloc_owned L A x.
Proof.
intros Hx [(e & He & Hin0) Hnb]. pose proof SPf as (S1 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (footprint_low B1 L A mem md e x M He Hin0) as LOW.
destruct Hx as [Hx|Hx]; [|lia].
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk' & Hl & ->)]]; cbn [fst snd loc_addr] in Hin0.
- rewrite (mc_ctx _ _ _ _ _ M) in Hin0. assert (Hlt : ERRNO + 4 <= ms_ctx B1) by (cbv; discriminate). lia.
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg0 & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hin0.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg0 Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold PGSZ in *; lia|]. apply in_img1_in_img, B1_errno_img. exact Hx.
- destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k r Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [lia|]. apply in_img1_in_img, B1_errno_img. exact Hx.
Qed.
Lemma base_len :
match mi with
| None => True
| Some (k, l) => exists rgk, region_of A k = Some rgk /\ rg_kind rgk = RkMap /\ rg_live rgk = true /\ rg_len rgk = page_round l /\
4096 <= ly_reg L k /\ ly_reg L k + rg_len rgk <= alloc_ceiling /\ ly_reg L k mod 4096 = 0 /\ 0 < l <= rg_len rgk /\
In (w64 (ly_reg L k), w64 (rg_len rgk)) (vm_maps (m_vmmaps md)) /\
(forall x, ly_reg L k <= x < ly_reg L k + rg_len rgk -> ~ in_img B1 x) /\
(forall q a', usedX [] A' q a' -> 0 < am_maplen a' -> prid (am_mem a') <> k)
end.
Proof.
destruct mi as [[k l]|]; [| exact I]. destruct NF as (HI' & _ & _ & (rgk & Hr' & Hkd & Hl & Hlen & Hl0 & Hno)). cbn [fst snd] in *.
pose proof (proj1 alloc_ceiling_val) as HCV.
assert (Hr : region_of A k = Some rgk).
{ rewrite <- Hr'. rewrite (ntrel_region_of A1 A' NR k). reflexivity. }
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rgk Hr Hl) as (Hal & H4096 & Hceil & Himg).
pose proof (lg_maps _ _ _ _ (mc_ledger _ _ _ _ _ M) k rgk Hr Hl ltac:(rewrite Hkd; discriminate)) as Hin0.
pose proof (lx_maps _ _ _ (MRx_ledger_x _ _ _ _ _ (MX L A regs mem md g am idx fr a ka rg HC)) _ Hin0) as [LEN _].
pose proof (YO0q.page_round_ge l) as PG.
unfold iv_len, w64 in LEN. cbn [snd] in LEN. rewrite lit64_small in LEN by lia.
exists rgk. repeat match goal with |- _ /\ _ => split end; auto; try (unfold PGSZ in *; lia).
assert (page_round 0 = 0) by reflexivity. destruct (Z.eq_dec l 0) as [->|]; lia.
Qed.
Lemma XRA err : 0 <= err < 2 ^ 32 -> forall n, 0 <= xva regs2 base len err n < 2 ^ 64.
Proof.
intros Herr n. pose proof base_len as BL. pose proof (proj1 alloc_ceiling_val) as HCV. unfold xva.
destruct (Nat.eqb_spec n 60); [destruct mi as [[k l]|]; [destruct BL as (rgk & B1' & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9); unfold base; lia | unfold base; lia]|].
destruct (Nat.eqb_spec n 61); [destruct mi as [[k l]|]; [destruct BL as (rgk & B1' & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9); unfold len; lia | unfold len; lia]|].
destruct (Nat.eqb_spec n 62); [lia|].
destruct ((64 <=? n)%nat && (n <? 96)%nat); [apply u64_range | apply XR].
Qed.
Lemma st_ok_after : exists err, 0 <= err < 2 ^ 32 /\
st_ok src0segs (EV (xva regs2 base len err)) (ss_after lenz) (mkst regs2 (Z_to_bv 64 FREE_AFTER_NT) mem2 (seg_rom src0segs)).
Proof.
destruct (errno_bytes_any mem2) as (err & Herr & Berr). exists err. split; [exact Herr|].
pose proof (nt_regs ms1 HN) as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & Rs).
pose proof (nt_mem ms1 HN) as (F1 & _ & _ & WSTK & S40 & S32 & S24 & S16 & S8).
pose proof NP as (MREP & STAT & RP & Ha0' & Ha1' & FR & WNT).
pose proof PRE as (_ & _ & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
pose proof SPf as (S1 & S2 & S3). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof Pf as (P1 & P2 & P3).
pose proof (XRA err Herr) as XRA'.
assert (ETP4 : xvf v 4 = 0x2fab0) by (rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; rewrite Htp; reflexivity).
assert (ETP : xvf v aTP = 0x2fab0) by exact ETP4.
assert (EERR : ERRNO = 195084) by reflexivity.
assert (KEEP : forall x, (SP - 48 <= x < SP) \/ (ERRNO <= x < ERRNO + 4) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem ms1) x /\ (writable_at src0segs (ms_mem ms1) x <-> writable_at src0segs mem2 x)).
{ intros x Hx. apply FR; [rewrite EERR in Hx; clear -Hx S1 S2 S3 HCV; lia | | unfold NT_FRAME, NEST_FUEL; lia].
intros O1. destruct (owned_A1 x O1) as [O | Bx].
- apply (errno_stack_not_owned x); [| exact O]. lia.
- destruct Hx as [Hx|Hx]; [lia|]. apply (block_off_img x Bx). apply B1_errno_img. exact Hx. }
assert (SB : forall off n, bytes_are (ms_mem ms1) (SP + off) 8 n -> -48 <= off -> off + 8 <= 0 -> bytes_are mem2 (SP + off) 8 n).
{ intros off n B Ho1 Ho2 kk Hkk. rewrite (proj1 (KEEP (SP + off + Z.of_nat kk) ltac:(left; lia))). apply B. exact Hkk. }
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_after resv_denot].
repeat (split; [reflexivity|]). split; [|split].
-
apply regs_ok_intro; [unfold lenz; destruct mi; reflexivity|]. intros n Hn. cbn [nth regs_after junk Nat.add].
destruct n as [|n]; [ lia
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off _ XRA') by (unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; change (xvf v aSP) with SP; lia); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; change (xvf v aSP) with SP; replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); rewrite (RP 2 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite R2; f_equal; lia
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (3%bv : bv 5) with (Z_to_bv 5 3) by (apply bv_eq; reflexivity); rewrite (RP 3 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); rewrite R3; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (4%bv : bv 5) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity); rewrite (RP 4 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); rewrite R4; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; change (xvf v aIDX) with idx; replace (8%bv : bv 5) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity); rewrite (RP 8 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact R8
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; rewrite XVP; replace (9%bv : bv 5) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); rewrite (RP 9 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact R9
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; unfold lenz, base in *; destruct mi as [[k0 l0]|]; [rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb aBASE]; exact Ha0' | cbn [sv_denot]; exact Ha0']
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; unfold lenz, len in *; destruct mi as [[k0 l0]|]; [rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb aLEN]; exact Ha1' | cbn [sv_denot]; exact Ha1']
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (18%bv : bv 5) with (Z_to_bv 5 18) by (apply bv_eq; reflexivity); rewrite (RP 18 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 18) with (nat_to_reg 18) by (apply bv_eq; reflexivity); rewrite (Rs 18%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (19%bv : bv 5) with (Z_to_bv 5 19) by (apply bv_eq; reflexivity); rewrite (RP 19 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 19) with (nat_to_reg 19) by (apply bv_eq; reflexivity); rewrite (Rs 19%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (20%bv : bv 5) with (Z_to_bv 5 20) by (apply bv_eq; reflexivity); rewrite (RP 20 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 20) with (nat_to_reg 20) by (apply bv_eq; reflexivity); rewrite (Rs 20%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (21%bv : bv 5) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity); rewrite (RP 21 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 21) with (nat_to_reg 21) by (apply bv_eq; reflexivity); rewrite (Rs 21%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (22%bv : bv 5) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); rewrite (RP 22 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 22) with (nat_to_reg 22) by (apply bv_eq; reflexivity); rewrite (Rs 22%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (23%bv : bv 5) with (Z_to_bv 5 23) by (apply bv_eq; reflexivity); rewrite (RP 23 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 23) with (nat_to_reg 23) by (apply bv_eq; reflexivity); rewrite (Rs 23%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (24%bv : bv 5) with (Z_to_bv 5 24) by (apply bv_eq; reflexivity); rewrite (RP 24 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 24) with (nat_to_reg 24) by (apply bv_eq; reflexivity); rewrite (Rs 24%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (25%bv : bv 5) with (Z_to_bv 5 25) by (apply bv_eq; reflexivity); rewrite (RP 25 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 25) with (nat_to_reg 25) by (apply bv_eq; reflexivity); rewrite (Rs 25%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (26%bv : bv 5) with (Z_to_bv 5 26) by (apply bv_eq; reflexivity); rewrite (RP 26 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 26) with (nat_to_reg 26) by (apply bv_eq; reflexivity); rewrite (Rs 26%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aP aIDX aBASE aLEN]; replace (27%bv : bv 5) with (Z_to_bv 5 27) by (apply bv_eq; reflexivity); rewrite (RP 27 ltac:(unfold callee_saved; lia)); replace (Z_to_bv 5 27) with (nat_to_reg 27) by (apply bv_eq; reflexivity); rewrite (Rs 27%nat ltac:(cbn; tauto)); cbn [nat_to_reg]; unfold aTP; rewrite xvf_reg by lia; cbn [nat_to_reg]; change (fv_regs v) with regs; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| destruct n as [|n]; [ cbn [nth regs_after nat_to_reg]; unfold junk; cbn [Nat.add]; rewrite (den_off0 _ XRA'); unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.sub nat_to_reg aSP aTP aP aIDX aBASE aLEN]; symmetry; apply Z_to_bv_bv_unsigned
| lia ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
-
assert (BV : forall n, base_val (EV (xva regs2 base len err)) (Some n) = xva regs2 base len err n) by (intros n; apply (base_val_EV _ XRA')).
assert (ELOCK : ms_lock B1 = src0_D_malloc_lock) by reflexivity.
assert (WST : forall x, SP - 8192 <= x < SP -> writable_at src0segs mem2 x).
{ intros x Hx. destruct (Z_lt_dec x (SP - 48 - NT_FRAME * Z.of_nat NEST_FUEL)) as [Lx|Lx]; [| destruct (Z_lt_dec x (SP - 48)) as [Lx2|Lx2]; [apply WNT; lia|]].
- apply (proj1 (proj2 (FR x ltac:(lia) ltac:(intros O1; destruct (owned_A1 x O1) as [O|Bx]; [apply (errno_stack_not_owned x); [right; lia | exact O] | lia]) ltac:(lia)))).
apply WSTK. exact Hx.
- apply (proj1 (proj2 (KEEP x ltac:(left; lia)))). apply WSTK. exact Hx. }
split; [vm_compute; reflexivity|]. split.
+ unfold after_mem. repeat apply Forall_cons; [| | | apply Forall_nil].
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_lock base_val]; unfold src0_D_malloc_lock; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply chunk_ok_lit0. intros kk Hkk. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hkk.
rewrite <- (st_lock _ _ STAT kk Hkk). rewrite ELOCK. unfold src0_D_malloc_lock. first [reflexivity | f_equal; lia].
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_errno]; rewrite BV; unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aTP]; rewrite ?ETP, ?ETP4; [lia | lia | |].
-- intros o Ho.
assert (N1 : ~ alloc_owned L A (195248 + o)) by (apply errno_stack_not_owned; left; lia).
assert (N2 : ~ (P <= 195248 + o < P + fr_n fr)) by (intros Bx; apply (block_off_img _ Bx); apply B1_errno_img; change (errno_addr B1) with (195248 + -164); lia).
assert (N3 : ~ (SP - 8192 <= 195248 + o < SP)) by lia.
apply (proj1 (proj2 (unch (195248 + o) ltac:(lia) N1 N2 N3))). apply Herrw. change (errno_addr B1) with (195248 + -164). lia.
-- apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 4%N (SOff aERR 0) err); [rewrite (U_off0 _ XRA'); reflexivity | cbn; lia |].
replace (195248 + -164) with ERRNO by (rewrite EERR; reflexivity). exact Berr.
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_stk_after]; rewrite BV; unfold xva; cbn [Nat.eqb Nat.leb Nat.ltb andb aSP]; change (xvf v aSP) with SP; [lia | lia | intros o Ho; apply WST; lia |].
assert (CH : forall off n, (n <= 31)%nat -> (n < 60)%nat -> bytes_are (ms_mem ms1) (SP + off) 8 (bv_unsigned (getr regs (nat_to_reg n))) -> -48 <= off -> off + 8 <= 0 ->
chunk_ok src0segs (EV (xva regs2 base len err)) mem2 SP (mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n Hn Hn60 B Ho1 Ho2. apply (chunk_ok_val _ _ _ _ 8%N (SOff n 0) (bv_unsigned (getr regs (nat_to_reg n)))).
- rewrite (U_off0 _ XRA'). unfold xva.
replace (n =? 60)%nat with false by (symmetry; apply Nat.eqb_neq; lia). replace (n =? 61)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (n =? 62)%nat with false by (symmetry; apply Nat.eqb_neq; lia). replace (64 <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia).
cbn [andb]. apply xvf_reg. exact Hn.
- cbn. apply u64_range.
- apply SB; assumption. }
repeat apply Forall_cons; [apply (CH _ 19%nat) | apply (CH _ 18%nat) | apply (CH _ 9%nat) | apply (CH _ 8%nat) | apply (CH _ 1%nat) | apply Forall_nil]; try lia;
first [exact S40 | exact S32 | exact S24 | exact S16 | exact S8].
+ unfold after_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [r_base r_lo r_hi reg_lock reg_errno reg_stk_after]. rewrite !BV. unfold xva. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP base_val].
rewrite ?ETP, ?ETP4. change (xvf v aSP) with SP. unfold src0_D_malloc_lock. repeat split; lia.
-
split; [| split; exact I]. pose proof base_len as BL. unfold after_atoms, lenz, base, len in *.
assert (A3 : afact_ok (EV (xva regs2 base len err)) aSP (mkAF (CEIL_MIN + 8192) (2 ^ 63 - 1) 4) /\
afact_ok (EV (xva regs2 base len err)) aTP (mkAF 4096 (2 ^ 63 - 1) 0) /\
afact_ok (EV (xva regs2 base len err)) aERR (mkAF 0 (2 ^ 32 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2 ew EV]. rewrite !lit64_small by apply XRA'. unfold xva. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP aTP aERR].
rewrite ?ETP, ?ETP4. change (xvf v aSP) with SP. unfold CEIL. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. repeat split; try lia. }
destruct A3 as (F1' & F2' & F3').
destruct mi as [[k l]|]; cbn [atoms_ok app]; [| split; [exact F1'|]; split; [exact F2'|]; split; [exact F3'| exact I]].
destruct BL as (rgk & B1' & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
split; [exact F1'|]; split; [exact F2'|]; split; [exact F3'|].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2 ew EV]. rewrite !lit64_small by apply XRA'. unfold xva. cbn [Nat.eqb Nat.leb Nat.ltb andb aBASE aLEN].
change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. pose proof (proj1 alloc_ceiling_val). repeat split; lia.
Qed.
Definition Af : astate :=
match mi with
| None => A'
| Some (k, _) => set_regions (lupd (st_regions A') k (mkRegion RkMap (rg_len (nth k (st_regions A') (mkRegion RkMap 0 [] false))) [] false)) A'
end.
Definition mdf : Model :=
match mi with
| None => md
| Some (k, l) => munmap_model (w64 (ly_reg L k)) (page_round_up (w64 l)) md
end.
Lemma free_K_shape :
free_K (mi, A') = match mi with
| None => IRet (tt, A')
| Some (k, l) => IAsk (KMunmap k l) A' (fun _ => IRet (tt, Af))
end.
Proof. unfold free_K, Af. cbn [fst snd]. destruct mi as [[k l]|]; reflexivity. Qed.
Lemma Af_same : st_metas Af = st_metas A' /\ st_areas Af = st_areas A /\ st_meta_alloc_shift Af = st_meta_alloc_shift A /\
st_avail_meta_areas Af = st_avail_meta_areas A /\ st_brk Af = st_brk A /\ st_init_done Af = st_init_done A /\
length (st_regions Af) = length (st_regions A) /\
image Af = image A' /\ frames Af = frames A' /\ user_blocks Af = user_blocks A' /\ tail_cells Af = tail_cells A'.
Proof.
destruct NR as [_ (K1 & K2 & K3 & K4 & K5 & K6 & _)]. unfold A1 in *. unfold upd_meta in K1, K2, K3, K4, K5, K6. cbn in K1, K2, K3, K4, K5, K6.
unfold Af. destruct mi as [[k l]|]; rewrite ?image_set_regions; cbn -[image frames user_blocks tail_cells]; rewrite ?length_lupd; repeat split; try reflexivity; try congruence.
Qed.
Lemma blocks_A' : user_blocks A' = user_blocks A1.
Proof. apply ub_same_user_blocks; [exact ND_A1 | exact (proj1 (inv_keys HW')) | exact (proj1 (proj2 (proj2 NF)))]. Qed.
Lemma kreg : match mi with
| None => True
| Some (k, l) => exists rgk, region_of A' k = Some rgk /\ region_of A k = Some rgk /\ rg_kind rgk = RkMap /\ rg_live rgk = true /\
rg_len rgk = page_round l /\ 0 < l <= rg_len rgk /\
nth k (st_regions A') (mkRegion RkMap 0 [] false) = rgk /\
(forall k', region_of (set_regions (lupd (st_regions A') k (mkRegion RkMap (rg_len rgk) [] false)) A') k' =
if Nat.eqb k' k then Some (mkRegion RkMap (rg_len rgk) [] false) else region_of A' k') /\
(forall q a', usedX [] A' q a' -> 0 < am_maplen a' -> prid (am_mem a') <> k) /\
page_round_up (w64 l) = w64 (rg_len rgk) /\
4096 <= ly_reg L k /\ ly_reg L k + rg_len rgk <= alloc_ceiling /\ ly_reg L k mod 4096 = 0 /\
In (w64 (ly_reg L k), w64 (rg_len rgk)) (vm_maps (m_vmmaps md)) /\
(forall x, ly_reg L k <= x < ly_reg L k + rg_len rgk -> ~ in_img B1 x)
end.
Proof.
pose proof base_len as BL. destruct mi as [[k l]|]; [| exact I].
destruct NF as (HI' & _ & _ & (rgk & Hr' & Hkd & Hl & Hlen & Hl0 & Hno)). cbn [fst snd] in *.
destruct BL as (rgk2 & HrA & _ & _ & Hlen2 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
assert (E : rgk2 = rgk).
{ pose proof (ntrel_region_of A1 A' NR k) as ER. change (region_of A1 k) with (region_of A k) in ER. rewrite ER, HrA in Hr'. injection Hr' as E. exact E. }
subst rgk2. pose proof (proj1 alloc_ceiling_val) as HCV.
exists rgk. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- unfold region_of in Hr'. exact (nth_error_nth _ _ _ Hr').
- intros k'. rewrite region_of_upd.
replace (Nat.ltb k (length (st_regions A'))) with true by (symmetry; apply Nat.ltb_lt; apply (region_of_lt _ _ _ Hr')).
rewrite andb_true_r. reflexivity.
- unfold page_round_up, w64. f_equal. rewrite lit64_small by lia. rewrite Hlen. reflexivity.
Qed.
Lemma WFf : WF Af.
Proof.
pose proof kreg as KR. pose proof HW' as W. unfold Af in *. destruct mi as [[k l]|]; [| exact W].
destruct KR as (rgk & Hr' & HrA & Hkd & Hl & Hlen & Hl0 & Hnth & HAf & Hno & _). rewrite Hnth.
exact (Inv_kill_map [] None U0 A' k rgk W Hr' Hkd Hno).
Qed.
Lemma footprint_A' : footprint A' = footprint A.
Proof. rewrite (ntrel_footprint A1 A' NR). reflexivity. Qed.
Lemma footprint_f :
match mi with
| None => footprint Af = footprint A
| Some (k, _) => exists l1 l2 e, footprint A = l1 ++ e :: l2 /\ footprint Af = l1 ++ l2 /\
(exists rgk, region_of A k = Some rgk /\ e = (LMem (YO0i.SP k 0), rg_len rgk))
end.
Proof.
pose proof kreg as KR. pose proof footprint_A' as FA. unfold Af in *. destruct mi as [[k l]|]; [| exact FA].
destruct KR as (rgk & Hr' & HrA & Hkd & Hl & Hlen & Hl0 & Hnth & HAf & Hno & _). rewrite Hnth in *.
rewrite <- FA. set (A3 := set_regions _ A') in *.
pose proof (region_of_lt _ _ _ Hr') as LT.
set (F := fun s kk => match region_of s kk with
| Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (YO0i.SP kk 0), rg_len rg)] else [] | _ => [] end
| None => [] end).
assert (EF : forall s, footprint s = (LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas s) ++ flat_map (F s) (seq 0 (length (st_regions s)))) by reflexivity.
rewrite !EF. change (st_areas A3) with (st_areas A'). change (length (st_regions A3)) with (length (lupd (st_regions A') k (mkRegion RkMap (rg_len rgk) [] false))). rewrite length_lupd.
replace (length (st_regions A')) with (k + (1 + (length (st_regions A') - k - 1)))%nat by lia.
rewrite !seq_app, !flat_map_app. cbn [seq].
assert (FS1 : forall (f : nat -> list (loc * Z)) x, flat_map f [x] = f x) by (intros; cbn; apply app_nil_r). rewrite !FS1.
cbn [Nat.add].
assert (Fk : F A' k = [(LMem (YO0i.SP k 0), rg_len rgk)]) by (unfold F; rewrite Hr', Hkd, Hl; reflexivity).
assert (Fk3 : F A3 k = []) by (unfold F; rewrite HAf, Nat.eqb_refl; reflexivity).
assert (Fo : forall j, j <> k -> F A3 j = F A' j).
{ intros j Hj. unfold F. rewrite HAf. replace (Nat.eqb j k) with false by (symmetry; apply Nat.eqb_neq; exact Hj). reflexivity. }
assert (FM : forall lo n, (forall j, In j (seq lo n) -> j <> k) -> flat_map (F A3) (seq lo n) = flat_map (F A') (seq lo n)).
{ intros lo n Hj. apply flat_map_ext_In. intros j Hjn. apply Fo. apply Hj. exact Hjn. }
rewrite Fk, Fk3. rewrite (FM 0%nat k) by (intros j Hj; apply in_seq in Hj; lia). rewrite (FM (k + 1)%nat) by (intros j Hj; apply in_seq in Hj; lia).
eexists ((LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas A') ++ flat_map (F A') (seq 0 k)), _, _.
split; [| split; [| exists rgk; split; [exact HrA | reflexivity]]].
- cbn [app]. rewrite <- app_assoc. reflexivity.
- cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma footprint_sub e : In e (footprint Af) -> In e (footprint A).
Proof.
pose proof footprint_f as FF. unfold Af in *. destruct mi as [[k l]|]; [| rewrite <- FF; tauto].
destruct FF as (l1 & l2 & e0 & E1 & E2 & _). rewrite E1, E2. intros H. apply in_app_iff in H. apply in_app_iff. cbn [In]. tauto.
Qed.
Lemma layout_f : layout_ok L Af.
Proof.
pose proof (mc_layout _ _ _ _ _ M) as (L1 & L2 & L3 & L4). pose proof kreg as KR. pose proof footprint_f as FF. pose proof footprint_sub as FS. unfold Af in *.
assert (REG : forall k' rg', region_of (match mi with
| Some (k, _) => set_regions (lupd (st_regions A') k {| rg_kind := RkMap; rg_len := rg_len (nth k (st_regions A') {| rg_kind := RkMap; rg_len := 0; rg_rw := []; rg_live := false |}); rg_rw := []; rg_live := false |}) A'
| None => A' end) k' = Some rg' -> rg_live rg' = true -> region_of A k' = Some rg').
{ intros k' rg' Hk' Hl'. destruct mi as [[k l]|].
- destruct KR as (rgk & Hr' & HrA & Hkd & Hl & Hlen & Hl0 & Hnth & HAf & _). rewrite Hnth in Hk'. rewrite HAf in Hk'.
destruct (Nat.eqb k' k); [injection Hk' as <-; discriminate|]. rewrite <- Hk'. rewrite (ntrel_region_of A1 A' NR k'). reflexivity.
- rewrite <- Hk'. rewrite (ntrel_region_of A1 A' NR k'). reflexivity. }
split; [exact L1|]. split; [intros k' rg' Hk' Hl'; exact (L2 k' rg' (REG k' rg' Hk' Hl') Hl')|]. split.
- destruct mi as [[k l]|]; [| rewrite FF; exact L3].
destruct FF as (l1 & l2 & e0 & E1 & E2 & _). rewrite E2. rewrite E1 in L3. rewrite map_app in *. cbn [map] in L3.
clear - L3. induction (map (crange L) l1) as [|x t IH]; cbn in *; [exact (proj2 L3)|].
destruct L3 as [H1 H2]. split; [| apply IH; exact H2]. intros y Hy. apply H1. apply in_app_iff in Hy. apply in_app_iff. cbn [In]. tauto.
- intros e He. apply L4. apply FS. exact He.
Qed.
Lemma ledger_ok_A' : ledger_ok B1 L A' md.
Proof.
pose proof (mc_ledger _ _ _ _ _ M) as LG. destruct NR as [_ (K1 & K2 & _)].
assert (ER : forall k, region_of A' k = region_of A k) by (intros k; unfold region_of; rewrite K1; reflexivity).
assert (EL : live_bytes A' = live_bytes A) by (unfold live_bytes; rewrite K1; reflexivity).
assert (EN : nslots A' = nslots A) by (unfold nslots; rewrite K1; reflexivity).
split; rewrite ?ER, ?EL, ?EN; try apply LG.
- intros k rg0 Hk0. rewrite ER in Hk0. exact (lg_maps _ _ _ _ LG k rg0 Hk0).
- intros k rg0 off Hk0. rewrite ER in Hk0. exact (lg_noaccess _ _ _ _ LG k rg0 off Hk0).
- rewrite K2. exact (lg_brk _ _ _ _ LG).
- intros k rg0 Hk0. rewrite ER in Hk0. exact (lg_placed _ _ _ _ LG k rg0 Hk0).
Qed.
Lemma ledger_f : ledger_ok B1 L Af mdf /\ ledger_x L Af mdf /\
m_halted mdf = None /\ m_vm_lazy mdf = [] /\ m_vm_materialized mdf = [] /\ (exists vm', mdf = with_vmmaps vm' md).
Proof.
pose proof kreg as KR. destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
pose proof (MRx_ledger_x _ _ _ _ _ (MX L A regs mem md g am idx fr a ka rg HC)) as LXA.
pose proof ledger_ok_A' as LGA'. pose proof HW' as W. pose proof layout_f as LF.
destruct NR as [NR1 (K1 & K2 & _)].
assert (LXA' : ledger_x L A' md) by (eapply ledger_x_same_regions; [exact LXA | exact K1 | reflexivity | reflexivity]).
unfold mdf, Af in *. destruct mi as [[k l]|].
- destruct KR as (rgk & Hr' & HrA & Hkd & Hl & Hlen & Hl0 & Hnth & HAf & Hno & EPR & B5 & B6 & B7 & B8 & B9). rewrite EPR.
pose proof (inv_areas W) as (_&_&_&_&_&_&_&_&A9).
assert (HlensA' : forall j rg', region_of A' j = Some rg' -> rg_live rg' = true -> 0 <= rg_len rg') by (intros j rg' Hj _; exact (A9 j rg' Hj)).
rewrite Hnth. set (A3 := set_regions _ A') in *.
pose proof (md_kill_facts B1 L A' md k rgk LGA' LXA' Hr' Hl Hkd (conj Hlz Hmat) HlensA') as (F1 & F2 & F3 & F4).
change (munmap_model (w64 (ly_reg L k)) (w64 (rg_len rgk)) md) with (md_kill L md k rgk).
split; [| split; [| rewrite F1; auto]].
+ apply (ledger_ok_munmap B1 L A' A3 md k rgk LGA' LXA' Hr' Hl Hkd HAf eq_refl (conj Hlz Hmat) HlensA').
+ unfold md_kill. pose proof (YO0q.page_round_ge l). pose proof (proj1 alloc_ceiling_val).
eapply (ledger_x_munmap L A' A3 md k rgk LXA' Hr' Hl Hkd); try assumption; try lia.
- split; [exact LGA'|]. split; [exact LXA'|]. repeat split; auto. exists (m_vmmaps md). apply with_vmmaps_self; assumption.
Qed.
Lemma ND_A' : List.NoDup (keys A'). Proof. exact (proj1 (inv_keys HW')). Qed.
Lemma MRx_final memf : memrep B1 L Af memf -> statics_ok B1 memf -> MRx B1 L Af memf mdf.
Proof.
intros MR ST. pose proof (Af_same) as (Em & Ear & Esh & Eav & Ebrk & Eini & Elen & Eimg & Efr & Eub & Etl).
pose proof ledger_f as (LG & LX & Hh & Hlz & Hmat & _). pose proof WFf as W. pose proof layout_f as LF.
pose proof PRE as (MXA & _ & HB & _).
apply MRx_intro.
- apply MRc_intro; try assumption.
+ exact (mc_syms _ _ _ _ _ M).
+ apply (bounded_of_WF Af W); rewrite ?Ear, ?Esh; apply HB.
+ exact (mc_ctx _ _ _ _ _ M).
+ exact (mc_sec _ _ _ _ _ M).
+ apply tail_geom_of_WF; assumption.
- exact LX.
- intros q a0 i f Hinf Hkf. rewrite Efr in Hinf.
destruct (ntrel_frames A1 A' NR ND_A1 ND_A' q a0 i f Hinf) as (a1 & Hin1 & SS).
destruct (shape2 L A regs mem md g am idx fr a ka rg HC) as [SE Hnone].
destruct (frames_upd A g am am1 idx q a1 i f Mg' SE Hnone Hin1) as (a2 & Hin2 & Hst).
unfold reserved_of. rewrite (same_shape_stride _ _ SS), <- Hst. exact (MRx_rsv _ _ _ _ _ MXA q a2 i f Hin2 Hkf).
- intros Hne. rewrite Eav, Elen. apply (MRx_ama _ _ _ _ _ MXA). rewrite <- Ear. exact Hne.
-
apply (span_ok_same_metas A'); [| exact Em]. apply (ntrel_span_ok A1 A' NR).
unfold A1. apply (span_ok_upd_same3 A g am); [exact (MRx_span _ _ _ _ _ MXA) | exact Mg' | reflexivity | reflexivity | reflexivity].
Qed.
Definition in_foot (s : astate) (x : Z) : Prop :=
exists e, In e (footprint s) /\ loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e.
Lemma foot_low x : in_foot Af x -> 4096 <= x < alloc_ceiling.
Proof. intros (e & He & Hx). exact (footprint_low B1 L A mem md e x M (footprint_sub e He) Hx). Qed.
Lemma memrep_final memf :
(forall x, 0 <= x < 2 ^ 64 -> in_foot Af x -> memf (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)) ->
memrep B1 L Af memf.
Proof.
intros RAW. pose proof (Af_same) as (Em & Ear & Esh & Eav & Ebrk & Eini & Elen & Eimg & Efr & Eub & Etl).
pose proof WFf as W. pose proof layout_f as LF. destruct NP as (MREP & _). pose proof MREP as (MI & MTL & MF).
pose proof (proj1 alloc_ceiling_val) as HCV.
assert (RAW' : forall x, in_foot Af x -> memf (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)).
{ intros x Hx. apply RAW; [pose proof (foot_low x Hx); lia | exact Hx]. }
split; [|split].
- apply Forall_forall. intros c Hc. rewrite Eimg in Hc.
apply (cell_keep B1 L mem2 memf c (proj1 (Forall_forall _ _) MI c Hc)). intros kk Hkk. apply RAW'.
destruct (image_in_footprint Af L c W LF ltac:(rewrite Eimg; exact Hc)) as (e & He & Hincl).
exists e. split; [exact He|]. unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. lia.
- apply Forall_forall. intros c Hc. rewrite Etl in Hc.
apply (cell_keep B1 L mem2 memf c (proj1 (Forall_forall _ _) MTL c Hc)). intros kk Hkk. apply RAW'.
destruct (tail_cell_in_region Af L c kk W ltac:(rewrite Etl; exact Hc) Hkk) as (r & rg0 & Hr & Hk0 & Hl0 & Hx).
exists (LMem (YO0i.SP r 0), rg_len rg0). split; [apply footprint_region_In; assumption|]. cbn [fst snd loc_addr]. lia.
- apply Forall_forall. intros e He.
pose proof (footprint_sub e He) as HeA. rewrite <- footprint_A' in HeA.
pose proof (proj1 (Forall_forall _ _) MF e HeA) as Fe. unfold foot_ok in *.
destruct e as [[o|q] n]; cbn [fst snd] in *; [exact I|]. intros x Hx.
destruct (Fe x Hx) as [b Hb]. exists b. rewrite RAW'; [exact Hb|]. exists (LMem q, n). split; [exact He|]. cbn [fst snd]. exact Hx.
Qed.
Lemma leaf_final regsf memf :
memrep B1 L Af memf -> statics_ok B1 memf -> regs_preserved regs regsf ->
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B1 x) -> ~ owned B1 L A x -> ~ scratch B1 regs x -> ~ (P <= x < P + fr_n fr) ->
mbyte src0segs memf x = mbyte src0segs mem x /\ (writable_at src0segs mem x <-> writable_at src0segs memf x)) ->
(forall q n i, In (q, n) (user_blocks A) -> In (q, n) (user_blocks Af) -> 0 <= i < n ->
mbyte src0segs memf (ptr_addr L q + i) = mbyte src0segs mem (ptr_addr L q + i)) ->
(forall x, scratch B1 regs x -> writable_at src0segs memf x) ->
free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr) (tt, Af) (mkCfg (mkst regsf (getr regs 1) memf (seg_rom src0segs)) mdf).
Proof.
intros MR ST RP FR BL SW. pose proof (Af_same) as (Em & Ear & Esh & Eav & Ebrk & Eini & Elen & Eimg & Efr & Eub & Etl).
pose proof ledger_f as (LG & LX & Hh & Hlz & Hmat & VM). pose proof WFf as W. pose proof PRE as (MXA & _ & HB & _).
exists L, regsf, memf, mdf. split; [reflexivity|]. split.
- split; [apply MRx_final; assumption|]. split; [exact W|]. split; [apply (bounded_of_WF Af W); rewrite ?Ear, ?Esh; apply HB|].
split; [apply layout_le_refl|]. split; [intros; reflexivity|]. split; [exact RP|]. split; [exact VM|].
split; [intros x Hx NO _ NS NE; apply FR; assumption|]. split; [exact BL | exact SW].
- cbn [snd]. rewrite Eub, blocks_A'. exact blocks_A1.
Qed.
Lemma leaf_final' regsf memf md' : md' = mdf ->
memrep B1 L Af memf -> statics_ok B1 memf -> regs_preserved regs regsf ->
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B1 x) -> ~ owned B1 L A x -> ~ scratch B1 regs x -> ~ (P <= x < P + fr_n fr) ->
mbyte src0segs memf x = mbyte src0segs mem x /\ (writable_at src0segs mem x <-> writable_at src0segs memf x)) ->
(forall q n i, In (q, n) (user_blocks A) -> In (q, n) (user_blocks Af) -> 0 <= i < n ->
mbyte src0segs memf (ptr_addr L q + i) = mbyte src0segs mem (ptr_addr L q + i)) ->
(forall x, scratch B1 regs x -> writable_at src0segs memf x) ->
free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr) (tt, Af) (mkCfg (mkst regsf (getr regs 1) memf (seg_rom src0segs)) md').
Proof. intros ->. apply leaf_final. Qed.
Lemma foot_facts x : in_foot Af x -> 4096 <= x < alloc_ceiling /\ ~ (ERRNO <= x < ERRNO + 4) /\ ~ (SP - 8192 <= x < SP).
Proof.
intros Hx. pose proof (foot_low x Hx) as LOW. pose proof SPf as (S1 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
split; [exact LOW|]. split; [| lia]. destruct Hx as (e & He & Hin0). apply footprint_sub in He. intros Hx.
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk' & Hl & ->)]]; cbn [fst snd loc_addr] in Hin0.
- rewrite (mc_ctx _ _ _ _ _ M) in Hin0. assert (Hlt : ERRNO + 4 <= ms_ctx B1) by (cbv; discriminate). lia.
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg0 & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hin0.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg0 Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold PGSZ in *; lia|]. apply in_img1_in_img, B1_errno_img. exact Hx.
- destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k r Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [lia|]. apply in_img1_in_img, B1_errno_img. exact Hx.
Qed.
Lemma static_facts x : static_owned B1 x -> 0 <= x < 0x51000 /\ ~ (ERRNO <= x < ERRNO + 4) /\ ~ (SP - 8192 <= x < SP).
Proof.
intros Hs. pose proof (B1_img_range x (so_statics_img _ (mc_syms _ _ _ _ _ M) x Hs)) as Hxi. pose proof SPf as (S1 & _). pose proof (proj1 alloc_ceiling_val).
split; [lia|]. split; [| lia]. unfold static_owned in Hs. cbn in Hs. rewrite EERR'. unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard,
src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs. lia.
Qed.
Lemma anyblock_off_img q n x : In (q, n) (user_blocks A) -> ptr_addr L q <= x < ptr_addr L q + n -> ~ in_img1 x.
Proof.
intros Hq Hx Hi. destruct (block_region A q n HWA Hq) as (kr & o & rg0 & Ep & Hrg0 & _ & Hl0 & Ho & Hn & Hon & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) kr rg0 Hrg0 Hl0) as (_ & _ & _ & Himg).
apply (Himg x); [| apply in_img1_in_img; exact Hi]. unfold ptr_addr in Hx. rewrite Ep in Hx. cbn [loc_addr] in Hx. lia.
Qed.
Lemma survivor_not_E q n i : In (q, n) (user_blocks Af) -> 0 <= i < n -> ~ (P <= ptr_addr L q + i < P + fr_n fr).
Proof.
intros Hq Hi HE. pose proof (Af_same) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eub & _). rewrite Eub, blocks_A' in Hq.
destruct blocks_A1 as (l1 & l2 & E1 & E2). rewrite E2 in Hq.
pose proof (mr_blocks_disjoint _ _ (MRc_laws B1) L A mem md M) as PW. unfold blocks in PW. rewrite E1 in PW.
change (l1 ++ (p, fr_n fr) :: l2) with (l1 ++ [(p, fr_n fr)] ++ l2) in PW.
destruct (pairwise_app_mid ranges_disjoint (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l1 [(p, fr_n fr)] l2 (p, fr_n fr) (q, n) PW ltac:(left; reflexivity) Hq) as [D|D];
unfold ranges_disjoint in D; cbn [fst snd] in D; unfold P in *; lia.
Qed.
Lemma view_regs E ss ms :
st_ok src0segs E ss ms -> callee_view ss = callee_view0 -> (forall n, (n < 60)%nat -> ew E n = Z_to_bv 64 (xvf v n)) ->
regs_preserved regs (ms_regs ms) /\ ew E 1 = getr regs 1 /\ sr_get (ss_regs ss) 1 = SOff 1 0.
Proof.
intros HS Hview XA.
unfold callee_view, callee_view0 in Hview. cbn [map] in Hview.
injection Hview as V1 V2 V3 V4 V8 V9 V18 V19 V20 V21 V22 V23 V24 V25 V26 V27.
split; [| split; [| replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity); exact V1]].
assert (GR : forall i, In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
getr (ms_regs ms) (nat_to_reg i) = getr regs (nat_to_reg i)).
{ intros i Hi. rewrite (st_ok_regs_ok _ _ _ _ HS (nat_to_reg i)).
assert (ESR : sr_get (ss_regs ss) (nat_to_reg i) = SOff i 0 /\ (i <= 31)%nat).
{ repeat (destruct Hi as [<-|Hi];
[split; [match goal with |- sr_get _ (nat_to_reg ?n) = _ => replace (nat_to_reg n) with (Z_to_bv 5 (Z.of_nat n)) by (apply bv_eq; reflexivity) end;
first [exact V1 | exact V2 | exact V3 | exact V4 | exact V8 | exact V9 | exact V18 | exact V19 | exact V20 | exact V21
| exact V22 | exact V23 | exact V24 | exact V25 | exact V26 | exact V27] | lia] |]).
destruct Hi. }
destruct ESR as [ESR Hi31]. rewrite ESR. cbn [sv_denot]. rewrite XA by lia. rewrite lit64_small by apply XR. rewrite Z.add_0_r.
rewrite xvf_reg by lia. apply Z_to_bv_bv_unsigned. }
- intros r0 Hr0. destruct (callee_saved_cases r0 Hr0) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r0 Rr). apply GR. exact RI.
- rewrite XA by lia. rewrite xvf_reg by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma tail_none : mi = None ->
SR src0segs (mkCfg (mkst regs2 (Z_to_bv 64 FREE_AFTER_NT) mem2 (seg_rom src0segs)) md)
(free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr) (tt, Af)).
Proof.
intros Hmi. destruct st_ok_after as (err & Herr & HS). pose proof (XRA err Herr) as XRA'.
destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat). pose proof PRE as (_ & _ & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
pose proof SPf as (S1 & S2 & S3). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof Pf as (P1 & P2 & P3).
destruct NP as (MREP & STAT & _).
assert (XA : forall n, (n < 60)%nat -> ew (EV (xva regs2 base len err)) n = Z_to_bv 64 (xvf v n)).
{ intros n Hn. cbn [ew EV]. unfold xva.
replace (n =? 60)%nat with false by (symmetry; apply Nat.eqb_neq; lia). replace (n =? 61)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (n =? 62)%nat with false by (symmetry; apply Nat.eqb_neq; lia). replace (64 <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. }
unfold lenz in HS. rewrite Hmi in HS.
eapply SR_bind; [exact (free_tail0_run _ _ md HS Hh Hlz)|].
intros c3 (ms3 & -> & HS3 & HF3). cbn [ms_mem] in HF3.
destruct SST0_shape as (Hpc & Hrv & Hview & Hsm).
destruct (view_regs _ _ _ HS3 Hview XA) as (RP3 & ERA & V1).
eapply (SR_free_ret (EV (xva regs2 base len err)) SST0 ms3 md); [exact HS3 | exact Hrv | exact Hpc | exact V1 | rewrite ERA; exact Hret | exact Hh | exact Hlz |].
rewrite ERA.
assert (RAW : forall x, 0 <= x < 2 ^ 64 -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (SP - 8192 <= x < SP) -> ms_mem ms3 (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)).
{ intros x Hx N1 N2. apply HF3. rewrite lit64_small by lia. intros (r & Hir & Hxr). unfold after_mem in Hir.
pose proof ETPv as ET. assert (ET4 : xvf v 4 = 195248) by exact ETPv. pose proof EERR' as EE.
destruct Hir as [<-|[<-|[<-|[]]]]; cbn [r_base r_wlo r_whi reg_lock reg_errno reg_stk_after] in Hxr.
- cbn [base_val] in Hxr. lia.
- rewrite (base_val_EV _ XRA') in Hxr. unfold xva in Hxr. cbn [Nat.eqb Nat.leb Nat.ltb andb aTP] in Hxr. rewrite ?ET, ?ET4 in Hxr. lia.
- rewrite (base_val_EV _ XRA') in Hxr. unfold xva in Hxr. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP] in Hxr.
change (xvf v aSP) with SP in Hxr. lia. }
pose proof (st_ok_mem_ok _ _ _ _ HS3) as (_ & ROK & _). rewrite Hsm in ROK. unfold after_mem in ROK.
apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rerr ROK]. apply Forall_cons_iff in ROK as [Rstk _].
destruct Rerr as (_ & _ & Werr & _). destruct Rstk as (_ & _ & Wstk & _).
cbn [r_base r_wlo r_whi reg_errno reg_stk_after] in Werr, Wstk. rewrite (base_val_EV _ XRA') in Werr. rewrite (base_val_EV _ XRA') in Wstk.
unfold xva in Werr, Wstk. cbn [Nat.eqb Nat.leb Nat.ltb andb aTP] in Werr. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP] in Wstk.
assert (ET4 : xvf v 4 = 195248) by exact ETPv. rewrite ?ETPv, ?ET4 in Werr. change (xvf v aSP) with SP in Wstk.
apply leaf_final'.
- unfold mdf. rewrite Hmi. reflexivity.
- apply memrep_final. intros x Hx HF. destruct (foot_facts x HF) as (F1 & F2 & F3). apply RAW; assumption.
- apply (statics_ok_ext B1 mem2 (ms_mem ms3) STAT). intros x Hs. destruct (static_facts x Hs) as (F1 & F2 & F3).
apply same_byte_views. apply RAW; [lia | exact F2 | exact F3].
- exact RP3.
- intros x Hhi NO NS NE. pose proof EERR' as EE.
assert (Hx : 0 <= x < 2 ^ 64) by (destruct Hhi as [Hhi|Hhi]; [lia | apply B1_img_range in Hhi; lia]).
assert (N1 : ~ (ERRNO <= x < ERRNO + 4)) by (intros W; apply NS; right; change (errno_addr B1) with ERRNO; lia).
assert (N2 : ~ (SP - 8192 <= x < SP)) by (intros W; apply NS; left; unfold ALLOC_STACK; change (spZ regs) with SP; lia).
destruct (unch x Hx ltac:(intros O; apply NO; left; exact O) NE N2) as [E1 W1].
destruct (same_byte_views mem2 (ms_mem ms3) x (RAW x Hx N1 N2)) as [E2 W2]. rewrite E2, E1. tauto.
- intros q n i Hq Hqf Hi. pose proof EERR' as EE.
destruct (blocks_facts B1 L A mem md q n i M Hq Hi) as (_ & Hlo & Hhi & HNO).
assert (N1 : ~ (ERRNO <= ptr_addr L q + i < ERRNO + 4)).
{ intros W. apply (anyblock_off_img q n (ptr_addr L q + i) Hq ltac:(lia)). apply B1_errno_img. change (errno_addr B1) with ERRNO. lia. }
assert (N2 : ~ (SP - 8192 <= ptr_addr L q + i < SP)) by lia.
destruct (unch (ptr_addr L q + i) ltac:(lia) ltac:(intros O; apply HNO; left; exact O) (survivor_not_E q n i Hqf Hi) N2) as [E1 _].
destruct (same_byte_views mem2 (ms_mem ms3) _ (RAW (ptr_addr L q + i) ltac:(lia) N1 N2)) as [E2 _]. rewrite E2, E1. reflexivity.
- intros x [Hs|Hs].
+ unfold ALLOC_STACK in Hs. change (spZ regs) with SP in Hs. replace x with (SP + (x - SP)) by lia. apply Wstk. lia.
+ change (errno_addr B1) with ERRNO in Hs. pose proof EERR' as EE. replace x with (195248 + (x - 195248)) by lia. apply Werr. lia.
Qed.
Lemma img_interval_disjoint lo n a0 ln :
(forall x, lo <= x < lo + n -> in_img1 x) -> 0 < n ->
(forall x, a0 <= x < a0 + ln -> ~ in_img B1 x) -> 0 < ln ->
lo + n <= a0 \/ a0 + ln <= lo.
Proof.
intros Hi Hn Ho Hln. destruct (Z_le_dec (lo + n) a0); [left; lia|]. destruct (Z_le_dec (a0 + ln) lo); [right; lia|]. exfalso.
destruct (Z_le_dec lo a0).
- apply (Ho a0); [lia|]. apply in_img1_in_img. apply Hi. lia.
- apply (Ho lo); [lia|]. apply in_img1_in_img. apply Hi. lia.
Qed.
Lemma tail_some k l : mi = Some (k, l) ->
SR src0segs (mkCfg (mkst regs2 (Z_to_bv 64 FREE_AFTER_NT) mem2 (seg_rom src0segs)) md)
(fun c3 => knode src0segs c3 (KMunmap k l) A'
(fun z c4 => mreal src0segs c4 (IRet (tt, Af)) (free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr)))).
Proof.
intros Hmi. destruct st_ok_after as (err & Herr & HS). pose proof (XRA err Herr) as XRA'.
destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat). pose proof PRE as (_ & _ & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
pose proof SPf as (S1 & S2 & S3). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof Pf as (P1 & P2 & P3).
pose proof NP as (MREP & STAT & _). pose proof ledger_f as (_ & _ & Hhf & Hlzf & Hmatf & _).
pose proof kreg as KR. pose proof footprint_f as FF. pose proof WFf as Wf. pose proof EERR' as EE.
pose proof foot_facts as FOOT. pose proof static_facts as STF. pose proof survivor_not_E as SNE. pose proof anyblock_off_img as ABO.
pose proof unch as UNCH. pose proof leaf_final' as LEAF. pose proof memrep_final as MF. pose proof view_regs as VR.
pose proof (mc_layout _ _ _ _ _ M) as (_ & _ & PWA & _).
assert (Eb : base = ly_reg L k) by (unfold base; rewrite Hmi; reflexivity).
assert (El : len = l) by (unfold len; rewrite Hmi; reflexivity).
assert (Emdf : mdf = munmap_model (w64 (ly_reg L k)) (page_round_up (w64 l)) md) by (unfold mdf; rewrite Hmi; reflexivity).
unfold lenz in HS. unfold Af in *. rewrite Hmi in HS, KR, FF, Wf, FOOT, SNE, LEAF, MF. rewrite Hmi.
destruct KR as (rgk & Hr' & HrA & Hkd & Hl & Hlen & Hl0 & Hnth & HAf & Hno & EPR & B5 & B6 & B7 & B8 & B9).
rewrite Hnth in *. set (A3 := set_regions _ A') in *.
assert (XA : forall n, (n < 60)%nat -> ew (EV (xva regs2 base len err)) n = Z_to_bv 64 (xvf v n)).
{ intros n Hn. cbn [ew EV]. unfold xva.
replace (n =? 60)%nat with false by (symmetry; apply Nat.eqb_neq; lia). replace (n =? 61)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (n =? 62)%nat with false by (symmetry; apply Nat.eqb_neq; lia). replace (64 <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. }
eapply SR_bind; [exact (free_tail1_run _ _ md HS Hh Hlz)|].
intros c3 (ms3 & -> & HS3 & HF3). cbn [ms_mem] in HF3.
destruct SST1_shape as (Hpc1 & Hrv1 & H17 & H10 & H11 & Hsm1).
destruct (st_ok_ecall_shape src0segs _ SST1 ms3 HS3 Hrv1) as (regs3 & mem3 & Ems3 & Hregs3 & Hmem3 & HG3).
rewrite Ems3 in HF3 |- *. cbn [ms_mem pend_at] in HF3. rewrite Hpc1.
assert (E10 : getr regs3 10 = w64 (ly_reg L k)).
{ rewrite (Hregs3 10%bv), H10, (den_off0 _ XRA'). unfold xva. cbn [Nat.eqb aBASE]. rewrite Eb. reflexivity. }
assert (E11 : getr regs3 11 = w64 l).
{ rewrite (Hregs3 11%bv), H11, (den_off0 _ XRA'). unfold xva. cbn [Nat.eqb aLEN]. rewrite El. reflexivity. }
assert (E17 : bv_unsigned (getr regs3 17) = 215) by (rewrite (Hregs3 17%bv), H17; reflexivity).
assert (Ebase : bv_unsigned (w64 (ly_reg L k)) = ly_reg L k) by (apply lit64_small; lia).
assert (Elen' : bv_unsigned (w64 l) = l) by (apply lit64_small; lia).
assert (EPRZ : page_round_up_Z l = rg_len rgk) by (rewrite Hlen; reflexivity).
apply SR_ret.
eapply (knode_munmap src0segs regs3 (Z_to_bv 64 MUNMAP_ECALL) mem3 (seg_rom src0segs) md A' k l);
[exact Hh | exact Hlz | exact E17 | rewrite E10, Ebase; unfold page_size; exact B7
| rewrite E11; intros E0; apply (f_equal bv_unsigned) in E0; rewrite Elen' in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; lia
| rewrite E10, E11, Ebase, Elen', EPRZ; unfold TASK_SIZE; pose proof (proj1 alloc_ceiling_val); lia
| rewrite E10, E11, EPR; apply map_has_In; exact B8 |].
unfold munmap_nx. rewrite E10, E11, EPR. cbn beta.
change (munmap_model (w64 (ly_reg L k)) (w64 (rg_len rgk)) md) with (md_kill L md k rgk).
assert (Emdf' : mdf = md_kill L md k rgk) by (rewrite Emdf, EPR; reflexivity). rewrite <- Emdf'.
apply mreal_IRet.
set (mem4 := apply_unmaps mem3 [(w64 (ly_reg L k), w64 (rg_len rgk))]).
assert (HS4 : st_ok src0segs (EV (xva regs2 base len err)) ss_post_ecall
(mkst (regupd regs3 10 (Z_to_bv 64 0)) (v_addi (Z_to_bv 64 MUNMAP_ECALL) 4) mem4 (seg_rom src0segs))).
{ rewrite <- Hpc1. unfold ss_post_ecall.
eapply (st_ok_resume_mem src0segs 200%nat); [exact Hregs3 | apply env_agree_refl | vm_compute; reflexivity | reflexivity | | exact HG3].
subst mem4. apply mem_ok_unmap; [exact Hmem3 | lia | lia | lia |].
rewrite Hsm1. intros r Hr. pose proof ETPv as ET. assert (ET4 : xvf v 4 = 195248) by exact ETPv.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [r_base r_lo r_hi reg_lock reg_errno].
- cbn [base_val]. unfold src0_D_malloc_lock.
apply (img_interval_disjoint src0_D_malloc_lock 4 (ly_reg L k) (rg_len rgk)); [intros x Hx; unfold in_img1, src0_D_malloc_lock in *; lia | unfold src0_D_malloc_lock; lia | exact B9 | unfold src0_D_malloc_lock in *; lia].
- rewrite (base_val_EV _ XRA'). unfold xva. cbn [Nat.eqb Nat.leb Nat.ltb andb aTP]. rewrite ?ET, ?ET4.
pose proof (img_interval_disjoint 195084 4 (ly_reg L k) (rg_len rgk) ltac:(intros x Hx; unfold in_img1; lia) ltac:(lia) B9 ltac:(lia)). lia.
- rewrite (base_val_EV _ XRA'). unfold xva. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP]. change (xvf v aSP) with SP. lia. }
eapply SR_bind; [exact (free_tail2_run _ _ mdf HS4 Hhf Hlzf)|].
clear HS HS3 Hmem3 HG3 Hregs3 HS4.
intros c5 (ms5 & -> & HS5 & HF5). unfold ss_post_ecall in HF5. rewrite resume_ss_mem in HF5.   rewrite Hsm1 in HF5.
destruct SST2_shape as (Hpc2 & Hrv2 & Hview2 & Hsm2).
destruct (VR _ _ _ HS5 Hview2 XA) as (RP5 & ERA & V1).
eapply (SR_free_ret (EV (xva regs2 base len err)) SST2 ms5 mdf); [exact HS5 | exact Hrv2 | exact Hpc2 | exact V1 | rewrite ERA; exact Hret | exact Hhf | exact Hlzf |].
rewrite ERA.
assert (RAW : forall x, 0 <= x < 2 ^ 64 -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (SP - 8192 <= x < SP) ->
~ (ly_reg L k <= x < ly_reg L k + rg_len rgk) -> ms_mem ms5 (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)).
{ intros x Hx N1 N2 N3. pose proof ETPv as ET. assert (ET4 : xvf v 4 = 195248) by exact ETPv.
transitivity (mem4 (Z_to_bv 64 x)); [| transitivity (mem3 (Z_to_bv 64 x))].
- apply HF5. rewrite lit64_small by lia. intros (r & Hir & Hxr).
destruct Hir as [<-|[<-|[<-|[]]]]; cbn [r_base r_wlo r_whi reg_lock reg_errno] in Hxr.
+ cbn [base_val] in Hxr. lia.
+ rewrite (base_val_EV _ XRA') in Hxr. unfold xva in Hxr. cbn [Nat.eqb Nat.leb Nat.ltb andb aTP] in Hxr. rewrite ?ET, ?ET4 in Hxr. lia.
+ rewrite (base_val_EV _ XRA') in Hxr. unfold xva in Hxr. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP] in Hxr. change (xvf v aSP) with SP in Hxr. lia.
- subst mem4. apply apply_unmaps1_out. unfold w64. rewrite !lit64_small by lia. lia.
- apply HF3. rewrite lit64_small by lia. intros (r & Hir & Hxr). unfold after_mem in Hir.
destruct Hir as [<-|[<-|[<-|[]]]]; cbn [r_base r_wlo r_whi reg_lock reg_errno reg_stk_after] in Hxr.
+ cbn [base_val] in Hxr. lia.
+ rewrite (base_val_EV _ XRA') in Hxr. unfold xva in Hxr. cbn [Nat.eqb Nat.leb Nat.ltb andb aTP] in Hxr. rewrite ?ET, ?ET4 in Hxr. lia.
+ rewrite (base_val_EV _ XRA') in Hxr. unfold xva in Hxr. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP] in Hxr. change (xvf v aSP) with SP in Hxr. lia. }
pose proof (st_ok_mem_ok _ _ _ _ HS5) as (_ & ROK & _). rewrite Hsm2 in ROK.
apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rerr ROK]. apply Forall_cons_iff in ROK as [Rstk _].
destruct Rerr as (_ & _ & Werr & _). destruct Rstk as (_ & _ & Wstk & _).
cbn [r_base r_wlo r_whi] in Werr, Wstk. rewrite (base_val_EV _ XRA') in Werr. rewrite (base_val_EV _ XRA') in Wstk.
unfold xva in Werr, Wstk. cbn [Nat.eqb Nat.leb Nat.ltb andb aTP] in Werr. cbn [Nat.eqb Nat.leb Nat.ltb andb aSP] in Wstk.
assert (ET4 : xvf v 4 = 195248) by exact ETPv. rewrite ?ETPv, ?ET4 in Werr. change (xvf v aSP) with SP in Wstk.
destruct FF as (l1 & l2 & e0 & EF1 & EF2 & (rgk' & HrA' & ->)). rewrite HrA in HrA'. injection HrA' as <-.
assert (NOTK : forall x e, In e (l1 ++ l2) -> loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rgk)).
{ intros x e He Hxe HK. rewrite EF1 in PWA. change (l1 ++ (LMem (YO0i.SP k 0), rg_len rgk) :: l2) with (l1 ++ [(LMem (YO0i.SP k 0), rg_len rgk)] ++ l2) in PWA.
destruct (pairwise_app_mid ranges_disjoint (crange L) l1 [(LMem (YO0i.SP k 0), rg_len rgk)] l2 _ e PWA ltac:(left; reflexivity) He) as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; lia. }
apply LEAF.
- reflexivity.
- apply MF. intros x Hx HFx. destruct (FOOT x HFx) as (F1 & F2 & F3). apply RAW; try assumption.
destruct HFx as (e & He & Hxe). rewrite EF2 in He. exact (NOTK x e He Hxe).
- apply (statics_ok_ext B1 mem2 (ms_mem ms5) STAT). intros x Hs. destruct (STF x Hs) as (F1 & F2 & F3).
apply same_byte_views. apply RAW; [lia | exact F2 | exact F3 |].
intros W. apply (B9 x W). apply (so_statics_img _ (mc_syms _ _ _ _ _ M)). exact Hs.
- exact RP5.
- intros x Hhi NO NS NE.
assert (Hx : 0 <= x < 2 ^ 64) by (destruct Hhi as [Hhi|Hhi]; [lia | apply B1_img_range in Hhi; lia]).
assert (N1 : ~ (ERRNO <= x < ERRNO + 4)) by (intros W; apply NS; right; change (errno_addr B1) with ERRNO; lia).
assert (N2 : ~ (SP - 8192 <= x < SP)) by (intros W; apply NS; left; unfold ALLOC_STACK; change (spZ regs) with SP; lia).
assert (N3 : ~ (ly_reg L k <= x < ly_reg L k + rg_len rgk)) by (intros W; destruct Hhi as [Hhi|Hhi]; [lia | exact (B9 x W Hhi)]).
destruct (UNCH x Hx ltac:(intros O; apply NO; left; exact O) NE N2) as [E1 W1].
destruct (same_byte_views mem2 (ms_mem ms5) x (RAW x Hx N1 N2 N3)) as [E2 W2]. rewrite E2, E1. tauto.
- intros q n i Hq Hqf Hi.
destruct (blocks_facts B1 L A mem md q n i M Hq Hi) as (_ & Hlo & Hhi & HNO).
assert (N1 : ~ (ERRNO <= ptr_addr L q + i < ERRNO + 4)).
{ intros W. apply (ABO q n (ptr_addr L q + i) Hq ltac:(lia)). apply B1_errno_img. change (errno_addr B1) with ERRNO. lia. }
assert (N2 : ~ (SP - 8192 <= ptr_addr L q + i < SP)) by lia.
assert (N3 : ~ (ly_reg L k <= ptr_addr L q + i < ly_reg L k + rg_len rgk)).
{ destruct (block_region A3 q n Wf Hqf) as (kr & o & rgq & Eq & Hrq & Hkq & Hlq & Ho & Hn & Hon & _).
assert (Hne : kr <> k) by (intros ->; rewrite HAf, Nat.eqb_refl in Hrq; injection Hrq as <-; discriminate).
assert (HrqA : region_of A kr = Some rgq).
{ rewrite HAf in Hrq. replace (Nat.eqb kr k) with false in Hrq by (symmetry; apply Nat.eqb_neq; exact Hne).
rewrite <- Hrq. rewrite (ntrel_region_of A1 A' NR kr). reflexivity. }
apply (NOTK (ptr_addr L q + i) (LMem (YO0i.SP kr 0), rg_len rgq)).
- assert (InA : In (LMem (YO0i.SP kr 0), rg_len rgq) (footprint A)) by (apply footprint_region_In; assumption).
rewrite EF1 in InA. apply in_app_iff in InA. apply in_app_iff. destruct InA as [H|[H|H]]; [left; exact H | exfalso | right; exact H].
injection H as E1' E2'; apply Hne; congruence.
- cbn [fst snd loc_addr]. unfold ptr_addr. rewrite Eq. cbn [loc_addr]. lia. }
destruct (UNCH (ptr_addr L q + i) ltac:(lia) ltac:(intros O; apply HNO; left; exact O) (SNE q n i Hqf Hi) N2) as [E1 _].
destruct (same_byte_views mem2 (ms_mem ms5) _ (RAW (ptr_addr L q + i) ltac:(lia) N1 N2 N3)) as [E2 _]. rewrite E2, E1. reflexivity.
- intros x [Hs|Hs].
+ unfold ALLOC_STACK in Hs. change (spZ regs) with SP in Hs. replace x with (SP + (x - SP)) by lia. apply Wstk. lia.
+ change (errno_addr B1) with ERRNO in Hs. replace x with (195248 + (x - 195248)) by lia. apply Werr. lia.
Qed.
End u.
Theorem slow_mreal : fast_cond idx am = false ->
mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs)) md)
(ibind (nontrivial_free NEST_FUEL g idx A1) free_K)
(free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr)).
Proof.
intros FC. destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
eapply mreal_SR_pre; [apply (to_nt FC)|]. intros c1 (ms1 & -> & HN).
eapply mreal_ibind; [apply (nt_call ms1 FC HN)|].
intros [mi A'] c2 [[NPOST NF] NR]. cbn [fst snd] in NR.
destruct NPOST as (regs2 & mem2 & -> & NP').
assert (NP : memrep B1 L A' mem2 /\ statics_ok B1 mem2 /\ regs_preserved (ms_regs ms1) regs2 /\
getr regs2 10 = Z_to_bv 64 (match mi with Some (k, _) => ly_reg L k | None => 0 end) /\
getr regs2 11 = Z_to_bv 64 (match mi with Some (_, len) => len | None => 0 end) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ alloc_owned L A1 x -> ~ (SP - 48 - NT_FRAME * Z.of_nat NEST_FUEL <= x < SP - 48) ->
mbyte src0segs mem2 x = mbyte src0segs (ms_mem ms1) x /\ (writable_at src0segs (ms_mem ms1) x <-> writable_at src0segs mem2 x)) /\
(forall x, SP - 48 - NT_FRAME * Z.of_nat NEST_FUEL <= x < SP - 48 -> writable_at src0segs mem2 x)).
{ pose proof (nt_regs ms1 HN) as (_ & _ & R2 & _).
assert (ESP : spZ (ms_regs ms1) = SP - 48) by (unfold spZ; rewrite R2; apply lit64_small; pose proof SPf as (S1 & S2 & _); pose proof alloc_ceiling_val; lia).
rewrite ESP in NP'. cbn [fst snd] in NP'. destruct NP' as [MR' NP']. split; [apply (proj1 (memrepX_nil B1 L A' mem2)); exact MR' | exact NP']. }
pose proof (nt_regs ms1 HN) as (_ & R1 & _). rewrite R1.
erewrite (free_K_shape ms1 mi A' regs2 mem2) by eassumption.
destruct mi as [[k l]|].
- eapply (tail_some ms1 (Some (k, l)) A' regs2 mem2); first [eassumption | reflexivity].
- eapply (tail_none ms1 None A' regs2 mem2); first [eassumption | reflexivity].
Qed.
End h.
Theorem src0_free_realizes : ntfree_hyp B1 -> free_realizes B1 (MRx B1).
Proof.
intros NT L A regs mem md p n PRE Hin Ha0.
pose proof (MRx_MRc _ _ _ _ _ (proj1 PRE)) as M. pose proof (mc_wf _ _ _ _ _ M) as HW.
destruct (user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & Hidx & Hfr & Hk & Hn & Hp). subst p n.
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (meta_in_area A g (MUsed am) HW (In_of_mlookup _ _ _ Mg)) as (a & ka & Hain & Hka & Eg).
destruct (used_group_region [] None U0 A g am HW Hu) as (rg & Hrg & Hkd & Hl & Ho & Hext & _).
assert (HC : free_ctx L A regs mem md g am idx fr a ka rg) by (split; auto; repeat split; auto).
pose proof (get_meta_ok A g am idx fr HW (frames_intro A g am idx fr HW Mg Hidx Hfr)) as GM. cbn zeta in GM.
destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hff).
pose proof (inv_groups HW g am Hu) as GG. destruct GG as (_ & _ & Gsl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _).
assert (Hmask : Z.land (mask0 am) (bit idx) = 0).
{ unfold allocated in Hal. unfold mask0, bit. apply Z.bits_inj'. intros j Hj.
rewrite Z.land_spec, Z.lor_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx j); [subst | apply andb_false_r].
rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) j), (Z.testbit (am_freed am) j); cbn in Hal |- *; try discriminate; reflexivity. }
change (ms_segs B1) with src0segs. change (ms_free B1) with src0_A_free.
rewrite (free_tree A (frame_ptr am idx fr) g idx am Hff Mg Hmask).
destruct (fast_cond idx am) eqn:FC.
- rewrite A_fast_eq. exact (fast_mreal L A regs mem md g am idx fr a ka rg HC FC).
- exact (slow_mreal L A regs mem md g am idx fr a ka rg HC NT FC).
Qed.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
