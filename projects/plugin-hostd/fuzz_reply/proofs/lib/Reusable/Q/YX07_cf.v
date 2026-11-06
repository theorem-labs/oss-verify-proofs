From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN03 YN02_cf YN2b YN08_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN0b_cf YN07_cf YN0a_cf YN1y_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW04_cf YW0e_cf YW07_cf YW0b_cf YW09_cf YW0f_cf YX00_cf YX01_cf YX06_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RSS (am : ameta) (fr : frame) (n : Z) : Z := avail_of am fr - n.
Definition RCS (am : ameta) (fr : frame) (n : Z) : Z := if 5 <=? RSS am fr n then 5 else RSS am fr n.
Lemma lor_low5 c i : 0 <= c -> 0 <= i < 32 -> Z.lor (32 * c) i = 32 * c + i.
Proof.
intros Hc Hi. assert (L0 : Z.land (32 * c) i = 0).
{ apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec k 5) as [Hk'|Hk'].
- replace (32 * c) with (c * 2 ^ 5) by (change (2 ^ 5) with 32; lia). rewrite Z.mul_pow2_bits by lia.
rewrite (Z.testbit_neg_r _ (k - 5)) by lia. reflexivity.
- destruct (Z.eq_dec i 0) as [->|Hi0]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
rewrite (Z.bits_above_log2 i k); [apply Bool.andb_false_r | lia |].
assert (Z.log2 i < 5) by (apply Z.log2_lt_pow2; [lia | change (2 ^ 5) with 32; lia]). lia. }
rewrite <- Z.lxor_lor by exact L0. rewrite <- Z.add_nocarry_lxor by exact L0. reflexivity.
Qed.
Lemma in_wrange_app7 E rs1 rs2 x : in_wrange E (rs1 ++ rs2) x -> in_wrange E rs1 x \/ in_wrange E rs2 x.
Proof. intros (r & Hin & Hr). apply in_app_iff in Hin as [H|H]; [left | right]; exists r; auto. Qed.
Lemma wr_exit_split k r nc t : k <> K3b -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) ->
ss_mem (exitS (SIP k r nc) t) = drop_bases [aP; aEND; aPN] (mem_at r nc) ++ reg_hdr :: t_memS t /\
forallb wr_stk (drop_bases [aP; aEND; aPN] (mem_at r nc)) = true.
Proof.
intros Hk Hnc. destruct (SI_shape k r nc Hk Hnc) as (_ & _ & Hm). cbn [exitS ss_mem]. rewrite Hm. split; [reflexivity|].
destruct Hnc as [->|[b1 ->]]; destruct r; vm_compute; reflexivity.
Qed.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation E := (ES L regs g am idx fr a rg n).
Local Abbreviation XV := (xvS L regs g am idx fr a rg n).
Local Abbreviation PP := (ptr_addr L (frame_ptr am idx fr)).
Local Abbreviation EE := (ptr_addr L (slot_end am idx)).
Local Abbreviation RR := (RSS am fr n).
Lemma XR7 : forall k, 0 <= XV k < 2 ^ 64.
Proof using HC. exact (XS L A regs mem md g am idx fr n a ka rg HC). Qed.
Lemma vals7 : XV aEND = EE /\ XV aNPN = PP + n /\ XV aIDX = idx /\ XV aOFF = hdr_off16 am idx fr /\ XV aP = PP /\ XV aN = n.
Proof using HC.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (XS_P L A regs mem md g am idx fr n a ka rg HC) | exact (XS_N L A regs mem md g am idx fr n a ka rg HC)].
Qed.
Lemma END_eq : EE = PP + avail_of am fr.
Proof using. unfold slot_end, frame_ptr, avail_of. rewrite !ptr_addr_padd'. lia. Qed.
Lemma geom7 : 4096 <= PP /\ EE + 1 <= alloc_ceiling /\ PP <= EE /\ 0 <= idx < 32 /\
(forall x, PP - 4 <= x <= EE -> ~ in_img1 x) /\ 16 <= stride_of am < 2 ^ 20 /\ 0 <= fr_off fr.
Proof using HC.
pose proof (FPS L A regs mem md g am idx fr n a ka rg HC) as FP. pose proof (fp_grp _ _ _ _ FP) as GR.
pose proof (lin_facts _ _ _ _ FP) as LF. cbn zeta in LF.
pose proof (P_range L A regs mem md g am idx fr n a ka rg HC) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof (inv_groups (HWS L A regs mem md g am idx fr n a ka rg HC) g am (sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & Gcl & _).
pose proof (sx_sc _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsc. pose proof (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hidx.
assert (Hst : stride_of am < 2 ^ 20) by (destruct Gcl as [(C1 & _) | (C1 & _ & _ & C4)]; [lia | nia]).
assert (EP : fv_p (vS L regs g am idx fr a rg) = PP).
{ pose proof (vals7) as (_ & _ & _ & _ & V & _). rewrite <- V. unfold xvS. cbn. reflexivity. }
change (fv_end (vS L regs g am idx fr a rg)) with EE in GR, LF. rewrite EP in GR, LF.
change (fv_idx (vS L regs g am idx fr a rg)) with idx in LF.
destruct GR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
pose proof END_eq as EQ. unfold avail_of in EQ. unfold UNIT, IB, CEIL in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split; lia].
intros x Hx. apply G9. change (fv_glo (vS L regs g am idx fr a rg)) with (ly_reg L (prid (am_mem am))) in *.
change (fv_mem (vS L regs g am idx fr a rg)) with (ptr_addr L (am_mem am)) in *. lia.
Qed.
Lemma RSS_range nc : nc_ok am fr n nc -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) -> 0 <= RR < 2 ^ 20.
Proof using HC.
intros Hok Hnc. pose proof geom7 as (_ & _ & _ & _ & _ & S1 & S2). pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
assert (Hav : n <= avail_of am fr) by (destruct Hnc as [->|[b1 ->]]; cbn in Hok; tauto).
unfold RSS, avail_of, UNIT, IB in *. lia.
Qed.
Lemma WRSVR_val : 0 <= RR < 2 ^ 20 -> bv_unsigned (sv_denot E WRSVR) = RR.
Proof using HC.
intros HR. pose proof vals7 as (V1 & V2 & _). pose proof geom7 as (G1 & G2 & G3 & _). pose proof END_eq as EQ.
pose proof YM05.alloc_ceiling_lt as HCL. pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
unfold WRSVR. cbn [sv_denot]. rewrite subw_rr_unsigned. unfold ES. rewrite !(ew_EV _ XR7), !Z.add_0_r, V1, V2, !lit64_small by lia.
rewrite subw_small by (unfold RSS in HR; lia). unfold RSS in *. lia.
Qed.
Lemma H3F_val t : 0 <= RR < 2 ^ 20 -> t = rcase_of RR -> bv_unsigned (sv_denot E (H3F t)) = idx + 32 * RCS am fr n.
Proof using HC.
intros HR Ht. pose proof vals7 as (_ & _ & V3 & _). pose proof geom7 as (_ & _ & _ & GI & _).
pose proof WRSVR_val HR as W. unfold RCS. unfold rcase_of in Ht.
destruct (RR =? 0) eqn:E0; [|destruct (RR <? 5) eqn:E1; [|destruct (RR =? 5) eqn:E2]]; subst t.
- apply Z.eqb_eq in E0. cbn [sv_denot H3F]. rewrite alu64_or. unfold ES. rewrite (ew_EV _ XR7), Z.add_0_r, V3, !lit64_small by lia.
rewrite E0. cbn. rewrite Z.lor_0_l. lia.
- apply Z.eqb_neq in E0. apply Z.ltb_lt in E1. cbn [sv_denot H3F]. fold (sv_denot E WRSVR).
change (sext 64 (alu32 ALU_SUB (low32 (sv_denot E (SOff aEND 0))) (low32 (sv_denot E (SOff aNPN 0))))) with (sv_denot E WRSVR).
rewrite alu64_or, alu64_sll, alu64_add, W. unfold ES. rewrite (ew_EV _ XR7), Z.add_0_r, V3, !lit64_small by lia.
unfold add64, sll64. rewrite Z.add_0_r, (Z.mod_small RR) by lia. change (5 mod 64) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
rewrite (Z.mod_small (RR * 32)) by lia. replace (RR * 32) with (32 * RR) by lia. rewrite lor_low5 by lia.
destruct (Z.leb_spec 5 RR); lia.
- apply Z.eqb_eq in E2. cbn [sv_denot H3F]. rewrite alu64_or. unfold ES. rewrite (ew_EV _ XR7), Z.add_0_r, V3, !lit64_small by lia.
change 160 with (32 * 5). rewrite lor_low5 by lia. rewrite E2. cbn. lia.
- apply Z.ltb_ge in E1. apply Z.eqb_neq in E2. cbn [sv_denot H3F]. rewrite alu64_or. unfold ES. rewrite (ew_EV _ XR7), Z.add_0_r, V3, !lit64_small by lia.
change 160 with (32 * 5). rewrite lor_low5 by lia. destruct (Z.leb_spec 5 RR); lia.
Qed.
Definition TWS (x : Z) : Prop := (0 < RR /\ x = PP + n) \/ (5 <= RR /\ EE - 5 <= x < EE).
Theorem fin_frameS nc t mi mf : nc_ok am fr n nc -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) -> t = rcase_of RR ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8256 <= x < spZ regs) -> mi (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
frame_of E (ss_mem (exitS (SIP (kcase_of am) (rcase_of (reserved_of am fr)) nc) t)) mi mf ->
forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8256 <= x < spZ regs) -> ~ (PP - 3 <= x < PP) -> ~ TWS x ->
mf (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof using HC.
intros Hok Hnc Ht RAW HF x Hx N1 N2 N3. rewrite <- (RAW x Hx N1). apply HF. rewrite lit64_small by exact Hx.
intros W. destruct (wr_exit_split _ (rcase_of (reserved_of am fr)) nc t (kc_small L A regs mem md g am idx fr n a ka rg HC) Hnc) as [Hm Hw].
rewrite Hm in W. apply in_wrange_app7 in W as [W|W].
- apply (wr_stack_only _ _ _ Hw) in W. rewrite (base_SPS L A regs mem md g am idx fr n a ka rg HC) in W. lia.
- pose proof (RSS_range nc Hok Hnc) as HR. pose proof vals7 as (V1 & V2 & _ & _ & V5 & _). pose proof END_eq as EQ.
destruct W as (rr & Hin & Hr). unfold ES in Hr.
unfold rcase_of in Ht. unfold TWS in N3.
destruct Hin as [<-|Hin].
+ cbn [r_base r_wlo r_whi reg_hdr base_val] in Hr. rewrite (ew_EV _ XR7), V5 in Hr. lia.
+ destruct (RR =? 0) eqn:E0; [|destruct (RR <? 5) eqn:E1; [|destruct (RR =? 5) eqn:E2]]; subst t; cbn [t_memS In] in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn [r_base r_wlo r_whi reg_npn reg_end5w base_val] in Hr; rewrite (ew_EV _ XR7) in Hr;
first [rewrite V1 in Hr | rewrite V2 in Hr];
try apply Z.eqb_neq in E0; try apply Z.ltb_lt in E1; try apply Z.ltb_ge in E1; try apply Z.eqb_eq in E2; try apply Z.eqb_neq in E2;
unfold RSS, avail_of in *; lia|]); destruct Hin.
Qed.
Theorem fin_readS nc t msf : nc_ok am fr n nc -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) -> t = rcase_of RR ->
st_ok src0segs E (SX (kcase_of am) (rcase_of (reserved_of am fr)) nc t) msf ->
let mF := ms_mem msf in
bytes_at src0_msyms mF (PP - 4) 1 0 /\ bytes_at src0_msyms mF (PP - 3) 1 (idx + 32 * RCS am fr n) /\
bytes_at src0_msyms mF (PP - 2) 2 (hdr_off16 am idx fr) /\
(0 < RR -> bytes_at src0_msyms mF (PP + n) 1 0) /\
(5 <= RR -> bytes_at src0_msyms mF (EE - 4) 4 RR /\ bytes_at src0_msyms mF (EE - 5) 1 0) /\
(forall x, spZ regs - 8256 <= x < spZ regs -> writable_at src0segs mF x) /\
(forall x, (PP - 3 <= x < PP) \/ TWS x -> present mF x) /\
regs_preserved regs (ms_regs msf) /\ getr (ms_regs msf) 10 = Z_to_bv 64 PP /\ ew E 1 = getr regs 1 /\
ms_pc_val msf = Z_to_bv 64 REALLOC_RET /\ ss_resv (SX (kcase_of am) (rcase_of (reserved_of am fr)) nc t) = None.
Proof using HC.
intros Hok Hnc Ht HS. cbv zeta.
pose proof (kc_small L A regs mem md g am idx fr n a ka rg HC) as Hk.
destruct (SX_shape _ (rcase_of (reserved_of am fr)) nc t Hk Hnc) as (Hpc & Hrv & Hcv & Ha0 & Hsm).
pose proof (RSS_range nc Hok Hnc) as HR. pose proof (H3F_val t HR Ht) as NH. pose proof (WRSVR_val HR) as W.
pose proof vals7 as (V1 & V2 & V3 & V4 & V5 & V6). pose proof END_eq as EQ. pose proof geom7 as (G1 & G2 & G3 & GI & GN & GS & GO).
pose proof YM05.alloc_ceiling_lt as HCL.
pose proof (st_ok_mem_ok src0segs E _ _ HS) as (_ & ROK & _). rewrite Hsm in ROK. unfold fin_mem in ROK.
apply Forall_app in ROK as [R6 RT]. apply Forall_app in RT as [_ RT].
apply Forall_cons_iff in R6 as [_ R6]. apply Forall_cons_iff in R6 as [_ R6]. apply Forall_cons_iff in R6 as [_ R6].
apply Forall_cons_iff in R6 as [_ R6]. apply Forall_cons_iff in R6 as [_ R6]. apply Forall_cons_iff in R6 as [Rstk _].
apply Forall_cons_iff in RT as [Rhdr RT].
destruct Rstk as (_ & _ & Wstk & _). cbn [r_base r_wlo r_whi stk1] in Wstk. rewrite (base_SPS L A regs mem md g am idx fr n a ka rg HC) in Wstk.
destruct Rhdr as (_ & _ & Whdr & Khdr). cbn [r_base r_wlo r_whi r_chunks hdr_fin] in Whdr, Khdr. unfold ES in Whdr, Khdr.
rewrite (base_val_EV _ XR7), V5 in Whdr, Khdr.
apply Forall_cons_iff in Khdr as [Kh3 Khdr]. apply Forall_cons_iff in Khdr as [Kh4 Khdr]. apply Forall_cons_iff in Khdr as [Kh2 _].
assert (TT : (forall x, TWS x -> writable_at src0segs (ms_mem msf) x) /\
(0 < RR -> bytes_at src0_msyms (ms_mem msf) (PP + n) 1 0) /\
(5 <= RR -> bytes_at src0_msyms (ms_mem msf) (EE - 4) 4 RR /\ bytes_at src0_msyms (ms_mem msf) (EE - 5) 1 0)).
{ unfold TWS. unfold rcase_of in Ht.
destruct (RR =? 0) eqn:E0; [|destruct (RR <? 5) eqn:E1; [|destruct (RR =? 5) eqn:E2]]; subst t; cbn [t_fin] in RT.
- apply Z.eqb_eq in E0. split; [intros x Hx; lia|]. split; intros; lia.
- apply Z.eqb_neq in E0. apply Z.ltb_lt in E1.
apply Forall_cons_iff in RT as [(_ & _ & W2 & KC2) _]. cbn [r_base r_wlo r_whi r_chunks npn_fin] in W2, KC2. unfold ES in W2, KC2.
rewrite (base_val_EV _ XR7), V2 in W2, KC2. apply Forall_cons_iff in KC2 as [KC2 _].
split; [intros x Hx; destruct Hx as [[_ ->]|Hx]; [replace (PP + n) with (PP + n + 0) by lia; apply W2; lia | lia]|].
split; [intros _; replace (PP + n) with (PP + n + 0) by lia; eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ KC2); [reflexivity | cbn; lia] | intros; lia].
- apply Z.eqb_eq in E2. apply Z.ltb_ge in E1.
apply Forall_cons_iff in RT as [(_ & _ & W1 & KC1) _]. cbn [r_base r_wlo r_whi r_chunks end5_fin] in W1, KC1. unfold ES in W1, KC1.
rewrite (base_val_EV _ XR7), V1 in W1, KC1. apply Forall_cons_iff in KC1 as [K14 KC1]. apply Forall_cons_iff in KC1 as [K15 _].
split; [intros x Hx; replace x with (EE + (x - EE)) by lia; apply W1; unfold RSS, avail_of in *; lia|].
split; [intros _; replace (PP + n) with (EE + -5) by (unfold RSS, avail_of in *; lia); eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ K15); [reflexivity | cbn; lia]|].
intros _. split; [replace (EE - 4) with (EE + -4) by lia; eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ K14); [cbn [sv_denot]; rewrite lit64_small by lia; lia | cbn; lia]|].
replace (EE - 5) with (EE + -5) by lia. eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ K15); [reflexivity | cbn; lia].
- apply Z.eqb_neq in E0. apply Z.ltb_ge in E1. apply Z.eqb_neq in E2.
apply Forall_cons_iff in RT as [(_ & _ & W2 & KC2) RT]. apply Forall_cons_iff in RT as [(_ & _ & W1 & KC1) _].
cbn [r_base r_wlo r_whi r_chunks npn_fin end5_fin] in W1, KC1, W2, KC2. unfold ES in W1, KC1, W2, KC2.
rewrite (base_val_EV _ XR7), V1 in W1, KC1. rewrite (base_val_EV _ XR7), V2 in W2, KC2.
apply Forall_cons_iff in KC1 as [K14 KC1]. apply Forall_cons_iff in KC1 as [K15 _]. apply Forall_cons_iff in KC2 as [KC2 _].
split; [intros x Hx; destruct Hx as [[_ ->]|Hx]; [replace (PP + n) with (PP + n + 0) by lia; apply W2; lia | replace x with (EE + (x - EE)) by lia; apply W1; lia]|].
split; [intros _; replace (PP + n) with (PP + n + 0) by lia; eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ KC2); [reflexivity | cbn; lia]|].
intros _. split; [replace (EE - 4) with (EE + -4) by lia; eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ K14); [exact W | cbn; lia]|].
replace (EE - 5) with (EE + -5) by lia. eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ K15); [reflexivity | cbn; lia]. }
destruct TT as (TW1 & TB2 & TB3).
assert (RCr : 0 <= RCS am fr n <= 5) by (unfold RCS; destruct (Z.leb_spec 5 RR); lia).
repeat match goal with |- _ /\ _ => split end.
- replace (PP - 4) with (PP + -4) by lia. eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ Kh4); [reflexivity | cbn; lia].
- replace (PP - 3) with (PP + -3) by lia. eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ Kh3); [exact NH | cbn; lia].
- replace (PP - 2) with (PP + -2) by lia. eapply (YW0f_cf.chunk_bytes _ _ _ _ _ _ _ Kh2); [rewrite (U_off0 _ XR7), V4; reflexivity |].
pose proof (lin_facts _ _ _ _ (FPS L A regs mem md g am idx fr n a ka rg HC)) as LF. cbn zeta in LF.
change (fv_off (vS L regs g am idx fr a rg)) with (hdr_off16 am idx fr) in LF. cbn. lia.
- exact TB2.
- exact TB3.
- intros x Hx. replace x with (spZ regs + (x - spZ regs)) by lia. apply Wstk. lia.
- intros x [Hx|Hx].
+ apply writable_off_img_present2; [lia | apply GN; lia |].
specialize (Whdr (x - PP) ltac:(lia)). replace (PP + (x - PP)) with x in Whdr by lia. exact Whdr.
+ pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn0.
apply writable_off_img_present2; [unfold TWS, RSS, avail_of in *; lia | apply GN; unfold TWS, RSS, avail_of in *; lia | apply TW1; exact Hx].
- intros r0 Hr0. destruct (callee_saved_cases r0 Hr0) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r0 Rr).
pose proof (st_ok_regs_ok src0segs E _ _ HS) as RG.
unfold callee_view, callee_view0, view in Hcv.
assert (GR : forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> sr_get (ss_regs (SX (kcase_of am) (rcase_of (reserved_of am fr)) nc t)) (nat_to_reg i) = SOff i 0).
{ intros i Hi. cbn [map] in Hcv.
repeat (destruct Hi as [<-|Hi]; [
match goal with |- sr_get _ (nat_to_reg ?k) = _ =>
exact (f_equal (fun l => List.nth (match k with 2 => 1 | 3 => 2 | 4 => 3 | 8 => 4 | 9 => 5 | 18 => 6 | 19 => 7 | 20 => 8 | 21 => 9 | 22 => 10 | 23 => 11 | 24 => 12 | 25 => 13 | 26 => 14 | _ => 15 end)%nat l (SLit 0)) Hcv) end |]).
destruct Hi. }
rewrite (RG (nat_to_reg (Z.to_nat r0))), (GR _ RI).
apply (den_regS L A regs mem md g am idx fr n a ka rg HC). cbn in RI. repeat (destruct RI as [<-|RI]; [lia|]); destruct RI.
- rewrite (st_ok_regs_ok src0segs E _ _ HS 10%bv), Ha0. unfold ES. rewrite (den_off0 _ XR7), V5. reflexivity.
- unfold ES, EV. cbn [ew]. rewrite XS_reg by lia. apply Z_to_bv_bv_unsigned.
- rewrite (st_ok_pc src0segs E _ _ HS), Hpc. reflexivity.
- exact Hrv.
Qed.
End b.
End a.
