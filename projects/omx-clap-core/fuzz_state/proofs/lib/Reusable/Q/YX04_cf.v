From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0h YK0i YK15 YM06 YM02 YP09 YK0v YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0x YO0z YO0s YO0u YO15 YO0v YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN03 YN2b YN31 YN2e YN2g YN26_cf YN28_cf YN2a_cf YN27 YN2c YN2d_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW03_cf YW00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0t YN25_cf YN2p_cf YN30_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW04_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition A_ip (A : astate) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) : astate :=
upd_meta g (MUsed (rs_am am idx (fr_off fr) n)) A.
Definition PI (L : layout) (am : ameta) (idx : Z) (fr : frame) : Z := ptr_addr L (frame_ptr am idx fr).
Definition ENDI (L : layout) (am : ameta) (idx : Z) : Z := ptr_addr L (slot_end am idx).
Definition RSVI (am : ameta) (fr : frame) (n : Z) : Z := stride_of am - IB - UNIT * fr_off fr - n.
Definition RCI (am : ameta) (fr : frame) (n : Z) : Z := if 5 <=? RSVI am fr n then 5 else RSVI am fr n.
Definition TWI (L : layout) (am : ameta) (idx : Z) (fr : frame) (n : Z) (x : Z) : Prop :=
(0 < RSVI am fr n /\ x = PI L am idx fr + n) \/ (5 <= RSVI am fr n /\ ENDI L am idx - 5 <= x < ENDI L am idx).
Record ip_memspec (B : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z)
(mem' : word -> option byte) (SCR : Z -> Prop) : Prop := IPM {
im_scr : forall x, SCR x -> alloc_ceiling <= x \/ (in_img B x /\ ~ static_owned B x /\ ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE));
im_p3 : bytes_at B mem' (PI L am idx fr - 3) 1 (idx + 32 * RCI am fr n);
im_pn : 0 < RSVI am fr n -> bytes_at B mem' (PI L am idx fr + n) 1 0;
im_e45 : 5 <= RSVI am fr n -> bytes_at B mem' (ENDI L am idx - 4) 4 (RSVI am fr n) /\ bytes_at B mem' (ENDI L am idx - 5) 1 0;
im_pres : forall x, x = PI L am idx fr - 3 \/ TWI L am idx fr n x -> present mem' x;
im_frame : forall x, 0 <= x < 2 ^ 64 -> x <> PI L am idx fr - 3 -> ~ TWI L am idx fr n x -> ~ SCR x -> mem' (w64 x) = mem (w64 x) }.
Lemma ENDI_eq L am idx fr : ENDI L am idx = PI L am idx fr + fr_n fr + reserved_of am fr.
Proof using. unfold ENDI, PI, slot_end, frame_ptr, reserved_of. rewrite !ptr_addr_padd_. lia. Qed.
Lemma slot_present B L A mem md g am idx fr : MRc B L A mem md -> usedX [] A g am -> 0 <= idx <= am_last am ->
ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
forall x, PI L am idx fr - 4 <= x <= ENDI L am idx -> present mem x.
Proof using.
intros M Hu Hidx Hfr Hk x Hx. pose proof (mc_wf _ _ _ _ _ M) as HW.
pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as (_ & _ & Gsl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
destruct (used_group_region [] None U0 A g am HW Hu) as (rg & Hr & Hrk & Hrl & Ho & Hext & _).
pose proof (slot_in_span [] None U0 A HW g am idx Hu Hidx) as [S1 S2].
apply (memrep_present B L A mem (prid (am_mem am)) rg x (MRc_memrep B L A mem md M) Hr Hrk Hrl).
unfold PI, ENDI, frame_ptr, slot_end in Hx. rewrite !ptr_addr_padd_ in Hx. unfold ptr_addr in Hx. rewrite loc_addr_LMem, prid_slot_start in Hx.
unfold group_extent, UNIT, IB in *. lia.
Qed.
Definition ix_am0 (am : ameta) (idx : Z) : ameta := upd_slot am idx (mkSlot (ss_hdr (nth_slot am idx)) None).
Definition ix_A0 (A : astate) (g : sptr) (am : ameta) (idx : Z) : astate := upd_meta g (MUsed (ix_am0 am idx)) A.
Lemma ix_mem0 am idx : am_mem (ix_am0 am idx) = am_mem am.
Proof using. unfold ix_am0. pose proof (upd_slot_fields am idx (mkSlot (ss_hdr (nth_slot am idx)) None)) as (E & _). exact E. Qed.
Lemma ix_last0 am idx : am_last (ix_am0 am idx) = am_last am.
Proof using. unfold ix_am0. pose proof (upd_slot_fields am idx (mkSlot (ss_hdr (nth_slot am idx)) None)) as (_ & E & _). exact E. Qed.
Lemma ix_st0 am idx : stride_of (ix_am0 am idx) = stride_of am.
Proof using. unfold ix_am0. pose proof (upd_slot_fields am idx (mkSlot (ss_hdr (nth_slot am idx)) None)) as (_ & _ & _ & _ & E & _). exact E. Qed.
Lemma ix_ss0 am idx j : slot_start (ix_am0 am idx) j = slot_start am j.
Proof using. unfold ix_am0. pose proof (upd_slot_fields am idx (mkSlot (ss_hdr (nth_slot am idx)) None)) as (_ & _ & _ & _ & _ & _ & E). exact (E j). Qed.
Lemma ix_TWI_dec L am idx fr n x : TWI L am idx fr n x \/ ~ TWI L am idx fr n x.
Proof using.
unfold TWI. set (p := PI L am idx fr). set (e := ENDI L am idx). set (r := RSVI am fr n).
destruct (Z_lt_le_dec 0 r); destruct (Z.eq_dec x (p + n)); destruct (Z_lt_le_dec r 5); destruct (Z_lt_le_dec x (e - 5)); destruct (Z_lt_le_dec x e);
first [left; left; lia | left; right; lia | right; lia].
Qed.
Lemma ix_cell_bytes B L m c a z : loc_addr L (mc_loc c) = a -> mc_val c = VZ z -> bytes_at B m a (mc_w c) z -> cell_mem B L m c.
Proof using. intros Ea Ev Hb. destruct c as [l w v]. cbn [mc_loc mc_val mc_w] in *. subst v. unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite Ea. exact Hb. Qed.
Record ipc (B : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
(g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) : Prop := IPC {
ic_mx : MRx B L A mem md;
ic_used : usedX [] A g am;
ic_idx : 0 <= idx <= am_last am;
ic_fr : ss_fr (nth_slot am idx) = Some fr;
ic_kind : fr_kind fr = FUser;
ic_n : 0 <= n;
ic_c1 : ra_c1 am (fr_off fr) n = true }.
Section ip.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z).
Hypothesis HC : ipc B L A mem md g am idx fr n.
Lemma ix_geo : exists kr ko rg,
am_mem am = SP kr ko /\
ptr_addr L (slot_start am idx) = ly_reg L kr + ko + 16 + stride_of am * idx /\
PI L am idx fr = ly_reg L kr + ko + 16 + stride_of am * idx + 16 * fr_off fr /\
ENDI L am idx = ly_reg L kr + ko + 16 + stride_of am * idx + stride_of am - 4 /\
16 <= stride_of am /\ 0 <= stride_of am * idx /\ stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1) /\
stride_of am * (am_last am + 1) < 2 ^ 20 /\
region_of A kr = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ 0 <= ko /\
ko + 16 + stride_of am * (am_last am + 1) <= rg_len rg /\
4096 <= ly_reg L kr /\ ly_reg L kr + rg_len rg <= alloc_ceiling /\
(forall a, ly_reg L kr <= a < ly_reg L kr + rg_len rg -> ~ in_img B a) /\
In (LMem (SP kr 0), rg_len rg) (footprint A) /\
0 <= fr_off fr /\ 0 <= fr_n fr /\ 16 * fr_off fr + fr_n fr <= stride_of am - 4 /\ 16 * fr_off fr + n <= stride_of am - 4 /\ 0 <= n.
Proof using HC.
pose proof HC as [MX Hu Hidx Hfr Hk Hn Hc1].
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (mc_wf _ _ _ _ _ M) as HW.
pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & _) & _ & Gsl & Gcl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
pose proof (ip_of_c1 A g am idx fr n HW Hu Hidx Hfr Hk Hn Hc1) as (_ & _ & _ & _ & _ & _ & Hav & Hcl).
assert (Hsc : am_sc am < 48).
{ destruct Hcl as [Hlt | (_ & Hbig & _)]; [exact Hlt|]. unfold ra_c1 in Hc1. apply andb_prop in Hc1 as [Hc1 _].
apply andb_prop in Hc1 as [_ H2]. apply Z.ltb_lt in H2. lia. }
assert (C4 : stride_of am * (am_last am + 1) < 2 ^ 20) by (destruct Gcl as [(C1 & _) | (_ & _ & _ & C4)]; [lia | exact C4]).
destruct (used_group_region [] None U0 A g am HW Hu) as (rg & Hr & Hrk & Hrl & Ho & Hext & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) _ _ Hr Hrl) as (_ & R4096 & Rceil & Rimg).
pose proof (footprint_region_In A _ _ Hr Hrk Hrl) as InR.
assert (P1 : 0 <= stride_of am * idx) by nia.
assert (P2 : stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
unfold group_extent, UNIT, IB in Hext. unfold UNIT, IB in Bf, Hav.
assert (ES : ptr_addr L (slot_start am idx) = ly_reg L (prid (am_mem am)) + poff (am_mem am) + 16 + stride_of am * idx).
{ unfold ptr_addr. rewrite loc_addr_LMem, prid_slot_start, poff_slot_start. unfold UNIT. lia. }
destruct (am_mem am) as [kr ko] eqn:Emem. cbn [prid poff] in *.
exists kr, ko, rg.
split; [reflexivity|]. split; [exact ES|].
split; [unfold PI, frame_ptr; rewrite ptr_addr_padd_, ES; unfold UNIT; lia|].
split; [unfold ENDI, slot_end; rewrite ptr_addr_padd_, ES; unfold IB; lia|].
split; [exact Sp|]. split; [exact P1|]. split; [exact P2|]. split; [exact C4|].
split; [exact Hr|]. split; [exact Hrk|]. split; [exact Hrl|]. split; [exact Ho|]. split; [lia|].
split; [exact R4096|]. split; [exact Rceil|]. split; [exact Rimg|]. split; [exact InR|].
split; [lia|]. split; [exact Nf|]. split; [lia|]. split; [lia|]. exact Hn.
Qed.
Lemma ix_TW x : TWI L am idx fr n x -> PI L am idx fr <= x < ENDI L am idx.
Proof using HC.
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
unfold TWI, RSVI. rewrite EP, EE. unfold UNIT, IB. lia.
Qed.
Lemma ix_reg x : ptr_addr L (slot_start am idx) - 4 <= x < ENDI L am idx ->
4096 <= x < alloc_ceiling /\ ~ in_img B x /\
exists k rg, region_of A k = Some rg /\ rg_live rg = true /\ ly_reg L k <= x < ly_reg L k + rg_len rg.
Proof using HC.
intros Hx.
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
rewrite ES, EE in Hx.
assert (Hin : ly_reg L kr <= x < ly_reg L kr + rg_len rg) by lia.
split; [lia|]. split; [exact (Rimg x Hin)|]. exists kr, rg. auto.
Qed.
Lemma ix_IPH : IPH A g am idx fr n.
Proof using HC.
pose proof HC as [MX Hu Hidx Hfr Hk Hn Hc1].
exact (ip_of_c1 A g am idx fr n (mc_wf _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) Hu Hidx Hfr Hk Hn Hc1).
Qed.
Lemma ix_WF2 : WF (A_ip A g am idx fr n).
Proof using HC. exact (ip_wf A g am idx fr n ix_IPH). Qed.
Lemma ix_bounded : bounded (A_ip A g am idx fr n).
Proof using HC.
pose proof HC as [MX _ _ _ _ _ _]. unfold A_ip. apply (proj2 (bounded_upd_meta _ _ _)).
exact (mc_bounded _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)).
Qed.
Lemma ix_blocks : exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am idx fr, fr_n fr) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks (A_ip A g am idx fr n) = m1 ++ (frame_ptr am idx fr, n) :: m2.
Proof using HC.
destruct (ip_blocks A g am idx fr n ix_IPH) as (l1 & l2 & E1 & E2).
exists l1, l2, l1, l2. split; [exact E1|]. split; [reflexivity | exact E2].
Qed.
Lemma ix_PI_nz : PI L am idx fr <> 0.
Proof using HC.
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
rewrite EP. lia.
Qed.
Lemma ix_len : length (am_slots am) = Z.to_nat (am_last am + 1).
Proof using HC.
pose proof HC as [MX Hu _ _ _ _ _].
pose proof (inv_groups (mc_wf _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) g am Hu) as ((_ & _ & Glen & _) & _). exact Glen.
Qed.
Lemma ix_ns0 : nth_slot (ix_am0 am idx) idx = mkSlot (ss_hdr (nth_slot am idx)) None.
Proof using HC.
pose proof HC as [_ _ Hidx _ _ _ _]. unfold ix_am0.
rewrite YO0s.nth_slot_upd_slot by (try lia; rewrite ix_len; lia). rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma ix_none0 : ss_fr (nth_slot (ix_am0 am idx) idx) = None.
Proof using HC. rewrite ix_ns0. reflexivity. Qed.
Lemma ix_ns' : nth_slot (rs_am am idx (fr_off fr) n) idx = resize_slot (stride_of am) idx (nth_slot am idx) (fr_off fr) n.
Proof using HC.
pose proof HC as [_ _ Hidx _ _ _ _]. rewrite (ip_ns A g am idx fr n idx ix_IPH ltac:(lia)). rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma ix_fr' : ss_fr (nth_slot (rs_am am idx (fr_off fr) n) idx) = Some (mkFrame (fr_off fr) n FUser).
Proof using HC. exact (ip_fr1 A g am idx fr n ix_IPH). Qed.
Lemma ix_SE0 : YN26_cf.shape_eq am (ix_am0 am idx) idx.
Proof using HC. pose proof HC as [_ _ Hidx _ _ _ _]. apply shape_eq_upd_slot; [lia | rewrite ix_len; lia]. Qed.
Lemma ix_SE' : YN26_cf.shape_eq am (rs_am am idx (fr_off fr) n) idx.
Proof using HC. pose proof HC as [_ _ Hidx _ _ _ _]. unfold rs_am. apply shape_eq_upd_slot; [lia | rewrite ix_len; lia]. Qed.
Lemma ix_SE0' : YN26_cf.shape_eq (ix_am0 am idx) (rs_am am idx (fr_off fr) n) idx.
Proof using HC.
pose proof ix_SE0 as (A1 & A2 & A3 & A4 & A5 & A6). pose proof ix_SE' as (B1 & B2 & B3 & B4 & B5 & B6).
split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
intros j Hj Hne. rewrite (A6 j Hj Hne), (B6 j Hj Hne). reflexivity.
Qed.
Lemma ix_HI0 : Inv [] (Some (g, idx)) U0 (ix_A0 A g am idx).
Proof using HC.
pose proof HC as [MX Hu Hidx Hfr Hk _ _].
unfold ix_A0, ix_am0. eapply drop_frame_Inv; [exact (mc_wf _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) | exact Hu | exact Hidx | exact Hfr | | reflexivity | left; reflexivity].
intros HG. rewrite Hk in HG. discriminate.
Qed.
Lemma ix_Mg0 : MT (ix_A0 A g am idx) g = Some (MUsed (ix_am0 am idx)).
Proof using. unfold ix_A0. apply MT_upd_same. Qed.
Lemma ix_Hu0 : usedX [] (ix_A0 A g am idx) g (ix_am0 am idx).
Proof using. apply usedX_intro; [reflexivity | apply ix_Mg0]. Qed.
Lemma ix_EA : A_ip A g am idx fr n = upd_meta g (MUsed (rs_am am idx (fr_off fr) n)) (ix_A0 A g am idx).
Proof using. unfold A_ip, ix_A0. symmetry. apply upd_meta_twice. Qed.
Lemma ix_img0 c : In c (image (ix_A0 A g am idx)) -> In c (image A).
Proof using HC.
pose proof HC as [MX Hu Hidx _ _ _ _]. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (image_upd_slot_eq A g am (ix_am0 am idx) idx Mg Hidx ix_SE0 (meta_slot_cells_upd_slot g am idx _)) as (l1 & l2 & E1 & E2 & _).
unfold ix_A0. rewrite E2, E1. intros Hc.
rewrite !in_app_iff in Hc |- *. destruct Hc as [Hc | [Hc | Hc]]; [left; exact Hc | right; left | right; right; exact Hc].
unfold slot_rest in Hc |- *. rewrite ix_ns0 in Hc. cbn [ss_hdr ss_fr] in Hc. rewrite app_nil_r, ix_ss0 in Hc.
apply in_app_iff. left. exact Hc.
Qed.
Lemma ix_rest' c : In c (slot_rest (rs_am am idx (fr_off fr) n) idx) ->
(In c (image A) /\ forall k, (k < mc_w c)%nat ->
ptr_addr L (slot_start am idx) - 4 <= loc_addr L (mc_loc c) + Z.of_nat k < PI L am idx fr /\
loc_addr L (mc_loc c) + Z.of_nat k <> PI L am idx fr - 3) \/
(loc_addr L (mc_loc c) = PI L am idx fr - 3 /\ mc_w c = 1%nat /\ mc_val c = VZ (idx + 32 * RCI am fr n)).
Proof using HC.
pose proof HC as [MX Hu Hidx Hfr Hk Hn Hc1].
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (mc_wf _ _ _ _ _ M) as HW. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _). pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & _ & Hhdr0).
destruct (image_upd_slot A g am idx Mg Hidx) as (l1 & l2 & Eim & _).
assert (IN : forall c0, In c0 (slot_rest am idx) -> In c0 (image A)) by (intros c0 H0; rewrite Eim; apply in_app_iff; right; apply in_app_iff; left; exact H0).
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn').
pose proof (rs_fields am idx (fr_off fr) n) as (_ & _ & _ & _ & Est & Ess).
intros Hc. unfold slot_rest in Hc. rewrite ix_ns', Ess in Hc. unfold resize_slot in Hc. cbv zeta in Hc. cbn [ss_hdr ss_fr fr_off] in Hc.
destruct (Z.eq_dec (fr_off fr) 0) as [E0|E0].
- rewrite E0, Z.eqb_refl in Hc. cbn [app] in Hc. destruct Hc as [<-|[<-|[]]].
+ right. cbn [mc_loc mc_w mc_val]. split; [rewrite loc_addr_padd_, ES, EP, E0; lia|]. split; [reflexivity|].
unfold RCI, RSVI. rewrite E0. f_equal. ring.
+ left. split.
* apply IN. unfold slot_rest. rewrite (Hhdr0 E0). apply in_app_iff. left. right. left. unfold hdr_off16. rewrite E0, Z.add_0_r. reflexivity.
* cbn [mc_loc mc_w]. intros k Hk'. rewrite loc_addr_padd_, ES, EP, E0. lia.
- replace (fr_off fr =? 0) with false in Hc by (symmetry; apply Z.eqb_neq; exact E0). cbn [app] in Hc.
apply in_app_iff in Hc as [Hc|Hc].
+ left. destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Eh; [|destruct Hc]. split.
* apply IN. unfold slot_rest. rewrite Eh. apply in_app_iff. left. exact Hc.
* destruct Hc as [<-|[<-|[]]]; cbn [mc_loc mc_w]; intros k Hk'; rewrite loc_addr_padd_, ES, EP; unfold UNIT in *; lia.
+ destruct Hc as [<-|[<-|[<-|[]]]].
* left. split.
-- apply IN. unfold slot_rest. rewrite Hfr. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
apply in_app_iff. right. left. reflexivity.
-- cbn [mc_loc mc_w]. intros k Hk'. rewrite loc_addr_padd_, ptr_addr_padd_, ES, EP. unfold UNIT. lia.
* right. cbn [mc_loc mc_w mc_val]. split; [rewrite loc_addr_padd_, ptr_addr_padd_, ES, EP; unfold UNIT; lia|]. split; [reflexivity|].
unfold hdr_byte3, rsv_code, RCI, RSVI. cbn [fr_kind fr_off fr_n]. rewrite Est. reflexivity.
* left. split.
-- apply IN. unfold slot_rest. rewrite Hfr. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
apply in_app_iff. right. right. right. left. unfold hdr_off16. cbn [fr_off]. rewrite Est. reflexivity.
-- cbn [mc_loc mc_w]. intros k Hk'. rewrite loc_addr_padd_, ptr_addr_padd_, ES, EP. unfold UNIT. lia.
Qed.
Lemma ix_p3' : exists c3, In c3 (slot_rest (rs_am am idx (fr_off fr) n) idx) /\ cell_range L c3 = (PI L am idx fr - 3, 1).
Proof using HC.
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
pose proof (rs_fields am idx (fr_off fr) n) as (_ & _ & _ & _ & Est & Ess).
unfold slot_rest. rewrite ix_ns', Ess. unfold resize_slot. cbv zeta. cbn [ss_hdr ss_fr fr_off].
destruct (Z.eq_dec (fr_off fr) 0) as [E0|E0].
- rewrite E0, Z.eqb_refl. cbn [app]. eexists. split; [left; reflexivity|].
unfold cell_range. cbn [mc_loc mc_w]. rewrite loc_addr_padd_, ES, EP, E0. f_equal; lia.
- replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). cbn [app].
eexists. split; [apply in_app_iff; right; right; left; reflexivity|].
unfold cell_range. cbn [mc_loc mc_w]. rewrite loc_addr_padd_, ptr_addr_padd_, ES, EP. unfold UNIT. f_equal; lia.
Qed.
Lemma ix_p3 : exists c3, In c3 (image A) /\ cell_range L c3 = (PI L am idx fr - 3, 1).
Proof using HC.
pose proof HC as [MX Hu Hidx Hfr Hk Hn Hc1].
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (mc_wf _ _ _ _ _ M) as HW. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _). pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & _ & Hhdr0).
destruct (image_upd_slot A g am idx Mg Hidx) as (l1 & l2 & Eim & _).
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn').
destruct (Z.eq_dec (fr_off fr) 0) as [E0|E0].
- exists (MCell (LMem (padd (slot_start am idx) (-3))) 1 (VZ (hdr_byte3 am idx fr))). split.
+ rewrite Eim. apply in_app_iff. right. apply in_app_iff. left. unfold slot_rest. rewrite (Hhdr0 E0). apply in_app_iff. left. left. reflexivity.
+ unfold cell_range. cbn [mc_loc mc_w]. rewrite loc_addr_padd_, ES, EP, E0. f_equal; lia.
- exists (MCell (LMem (padd (padd (slot_start am idx) (UNIT * fr_off fr)) (-3))) 1 (VZ (hdr_byte3 am idx fr))). split.
+ rewrite Eim. apply in_app_iff. right. apply in_app_iff. left. unfold slot_rest. rewrite Hfr.
replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). apply in_app_iff. right. right. left. reflexivity.
+ unfold cell_range. cbn [mc_loc mc_w]. rewrite loc_addr_padd_, ptr_addr_padd_, ES, EP. unfold UNIT. f_equal; lia.
Qed.
Lemma ix_p3_owned : alloc_owned L A (PI L am idx fr - 3).
Proof using HC.
pose proof HC as [MX _ _ _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M.
pose proof (mc_wf _ _ _ _ _ M) as HW. pose proof (mc_layout _ _ _ _ _ M) as HL.
destruct ix_p3 as (c3 & Hc3 & Rc3). unfold cell_range in Rc3. injection Rc3 as E1 E2.
pose proof (image_cell_owned L A c3 0 HW HL Hc3 ltac:(lia)) as H.
replace (PI L am idx fr - 3) with (loc_addr L (mc_loc c3) + Z.of_nat 0) by lia. exact H.
Qed.
Lemma ix_tail0 c k : In c (tail_cells (ix_A0 A g am idx)) -> (k < mc_w c)%nat ->
~ (ptr_addr L (slot_start am idx) - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < ENDI L am idx).
Proof using HC.
pose proof HC as [MX Hu Hidx _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (mc_layout _ _ _ _ _ M) as HL.
pose proof ix_HI0 as HI0.
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
intros Hc Hk Hin.
unfold tail_cells in Hc. apply in_flat_map in Hc as ([g' a'] & Hg' & Hc'). cbn [snd] in Hc'.
assert (Hu' : usedX [] (ix_A0 A g am idx) g' a').
{ apply usedX_intro; [reflexivity|]. apply (used_metas_iff _ g' a' (proj1 (inv_keys HI0))). exact Hg'. }
destruct (tail_cell_home [] (Some (g, idx)) U0 _ HI0 g' a' c Hu' Hc') as (rg' & d & Hr' & Hk' & Hl' & Eloc & Hd & Ho' & Hfit' & _).
assert (Hidx0 : 0 <= idx <= am_last (ix_am0 am idx)) by (rewrite ix_last0; exact Hidx).
rewrite Eloc, loc_addr_padd_, ES, EE in Hin.
change (region_of A (prid (am_mem a')) = Some rg') in Hr'.
destruct (Nat.eq_dec (prid (am_mem a')) kr) as [Ekr|Hne].
- pose proof (tail_cells_avoid_slot [] (Some (g, idx)) U0 _ HI0 g (ix_am0 am idx) idx g' a' c d k ix_Hu0 Hidx0 ix_none0 Hu' Hc' Eloc Hk) as AV.
rewrite ix_mem0, Emem in AV. cbn [prid] in AV. specialize (AV Ekr).
rewrite ix_ss0, ix_st0, poff_slot_start, Emem in AV. cbn [poff] in AV.
unfold ptr_addr in Hin. rewrite loc_addr_LMem, Ekr in Hin.
unfold UNIT, IB in *. lia.
- pose proof HL as (_ & _ & PW & _).
pose proof (footprint_region_In A _ _ Hr' Hk' Hl') as In'.
assert (Hne' : (LMem (SP (prid (am_mem a')) 0), rg_len rg') <> (LMem (SP kr 0), rg_len rg)) by (intros X; injection X; intros _ X1; exact (Hne X1)).
unfold ptr_addr in Hin. rewrite loc_addr_LMem in Hin.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW In' InR Hne') as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; unfold UNIT, IB in *; lia.
Qed.
Lemma ix_ft : frame_tail_cells (rs_am am idx (fr_off fr) n) idx =
(if 0 <? RSVI am fr n then [MCell (LMem (padd (frame_ptr am idx fr) n)) 1 (VZ 0)] else []) ++
(if 5 <=? RSVI am fr n then [MCell (LMem (padd (slot_end am idx) (-4))) 4 (VZ (RSVI am fr n));
MCell (LMem (padd (slot_end am idx) (-5))) 1 (VZ 0)] else []).
Proof using HC.
pose proof (rs_fields am idx (fr_off fr) n) as (_ & _ & _ & _ & Est & Ess).
unfold frame_tail_cells. rewrite ix_fr'. cbn [fr_kind fr_n].
assert (ER : reserved_of (rs_am am idx (fr_off fr) n) (mkFrame (fr_off fr) n FUser) = RSVI am fr n)
by (unfold reserved_of, RSVI; cbn [fr_off fr_n]; rewrite Est; reflexivity).
rewrite ER. unfold frame_ptr, slot_end. rewrite Ess, Est. cbn [fr_off]. reflexivity.
Qed.
Lemma ix_tw_cell x : TWI L am idx fr n x ->
exists c k, In c (tail_cells (A_ip A g am idx fr n)) /\ (k < mc_w c)%nat /\ loc_addr L (mc_loc c) + Z.of_nat k = x.
Proof using HC.
pose proof HC as [_ Hu Hidx _ _ _ _]. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
assert (IN : forall c, In c (frame_tail_cells (rs_am am idx (fr_off fr) n) idx) -> In c (tail_cells (A_ip A g am idx fr n))).
{ intros c Hc. destruct (used_metas_upd A g am Mg) as (u1 & u2 & _ & Eu'). unfold tail_cells, A_ip. rewrite Eu'.
apply in_flat_map. exists (g, rs_am am idx (fr_off fr) n). split; [apply in_app_iff; right; left; reflexivity|]. cbn [snd].
unfold group_tail_cells. right. apply in_flat_map. exists idx. split; [|exact Hc].
apply In_zseq. pose proof (rs_fields am idx (fr_off fr) n) as (_ & El & _). rewrite El. lia. }
rewrite ix_ft in IN. intros T. unfold TWI in T. destruct T as [(Hr & Ex) | (Hr & Ex)].
- exists (MCell (LMem (padd (frame_ptr am idx fr) n)) 1 (VZ 0)), 0%nat.
split; [apply IN; apply in_app_iff; left; replace (0 <? RSVI am fr n) with true by (symmetry; apply Z.ltb_lt; exact Hr); left; reflexivity|].
split; [cbn; lia|]. cbn [mc_loc]. rewrite loc_addr_padd_. unfold PI in Ex. lia.
- destruct (Z.eq_dec x (ENDI L am idx - 5)) as [E5|E5].
+ exists (MCell (LMem (padd (slot_end am idx) (-5))) 1 (VZ 0)), 0%nat.
split; [apply IN; apply in_app_iff; right; replace (5 <=? RSVI am fr n) with true by (symmetry; apply Z.leb_le; exact Hr); right; left; reflexivity|].
split; [cbn; lia|]. cbn [mc_loc]. rewrite loc_addr_padd_. unfold ENDI in E5. lia.
+ exists (MCell (LMem (padd (slot_end am idx) (-4))) 4 (VZ (RSVI am fr n))), (Z.to_nat (x - (ENDI L am idx - 4))).
split; [apply IN; apply in_app_iff; right; replace (5 <=? RSVI am fr n) with true by (symmetry; apply Z.leb_le; exact Hr); left; reflexivity|].
split; [cbn [mc_w]; lia|]. cbn [mc_loc]. rewrite loc_addr_padd_. unfold ENDI in *. lia.
Qed.
Lemma ix_frames g0 a0 i f : In (g0, a0, i, f) (frames (A_ip A g am idx fr n)) ->
(g0 = g /\ a0 = rs_am am idx (fr_off fr) n /\ i = idx /\ f = mkFrame (fr_off fr) n FUser) \/
exists a1, In (g0, a1, i, f) (frames A) /\ stride_of a1 = stride_of a0.
Proof using HC.
pose proof HC as [_ Hu _ _ _ _ _]. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
intros Hf. destruct (used_metas_upd A g am Mg) as (u1 & u2 & Eu & Eu').
unfold frames in *. unfold A_ip in Hf. rewrite Eu' in Hf. rewrite Eu. rewrite !flat_map_app in *. cbn [flat_map] in *.
apply in_app_iff in Hf as [Hf|Hf].
{ right. exists a0. split; [apply in_app_iff; left; exact Hf | reflexivity]. }
apply in_app_iff in Hf as [Hf|Hf].
2:{ right. exists a0. split; [apply in_app_iff; right; apply in_app_iff; right; exact Hf | reflexivity]. }
pose proof ix_SE' as SE'. pose proof (shape_eq_stride _ _ _ SE') as Hst. destruct SE' as (Hm & Hml & Hai & Hl & Hsc & Hs).
apply in_flat_map in Hf as (j & Hj & Hf). rewrite Hl in Hj. pose proof Hj as Hj'. apply In_zseq in Hj'.
destruct (Z.eq_dec j idx) as [->|Hne].
- rewrite ix_fr' in Hf. destruct Hf as [E0|[]]. injection E0 as <- <- <- <-. left. auto.
- rewrite (Hs j ltac:(lia) Hne) in Hf. destruct (ss_fr (nth_slot am j)) as [fr0|] eqn:Efr; [|destruct Hf]. destruct Hf as [E0|[]].
injection E0 as <- <- <- <-. right. exists am. split; [|symmetry; exact Hst].
apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists j. split; [exact Hj|]. rewrite Efr. left. reflexivity.
Qed.
Lemma ix_rsv : rsv_ok (A_ip A g am idx fr n).
Proof using HC.
pose proof HC as [MX _ _ _ _ _ _].
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
pose proof (rs_fields am idx (fr_off fr) n) as (_ & _ & _ & _ & Est & _).
intros g0 a0 i f Hf Hkf. destruct (ix_frames g0 a0 i f Hf) as [(-> & -> & -> & ->) | (a1 & Hf' & Hst)].
- unfold reserved_of. rewrite Est. cbn [fr_off fr_n]. unfold UNIT, IB. lia.
- pose proof (MRx_rsv _ _ _ _ _ MX g0 a1 i f Hf' Hkf) as R. unfold reserved_of in *. rewrite Hst in R. exact R.
Qed.
Section mm.
Variables (mem' : word -> option byte) (SCR : Z -> Prop).
Hypothesis SP : ip_memspec B L A mem g am idx fr n mem' SCR.
Lemma ix_scr_reg k rg x : region_of A k = Some rg -> rg_live rg = true -> ly_reg L k <= x < ly_reg L k + rg_len rg -> ~ SCR x.
Proof using HC SP.
intros Hr Hl Hx HS. pose proof HC as [MX _ _ _ _ _ _]. pose proof SP as [SCRh _ _ _ _ _].
pose proof (MRx_MRc _ _ _ _ _ MX) as M.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rg Hr Hl) as (_ & H1 & H2 & H3).
destruct (SCRh x HS) as [Hhi | (Hi & _ & _)]; [lia | exact (H3 x Hx Hi)].
Qed.
Lemma ix_foot_scr e x : In e (footprint A) -> loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> ~ SCR x /\ 0 <= x < 2 ^ 64.
Proof using HC SP.
intros He Hx. pose proof HC as [MX _ _ _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (mc_wf _ _ _ _ _ M) as HW.
pose proof (footprint_low B L A mem md e x M He Hx) as LOW. pose proof alloc_ceiling_lt.
split; [|lia].
intros HS. pose proof SP as [SCRh _ _ _ _ _]. destruct (SCRh x HS) as [Hhi | (Himg & Hns & Hnc)]; [lia|].
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & rr & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- apply Hnc. rewrite <- (mc_ctx _ _ _ _ _ M). lia.
- destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rr & -> & Hom & Ho & Hr & Hl & Hsz & _). cbn [loc_addr] in Hx.
apply (proj2 (proj2 (proj2 (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rr Hr Hl))) x); [unfold PGSZ in *; lia | exact Himg].
- apply (proj2 (proj2 (proj2 (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rr Hr Hl))) x); [lia | exact Himg].
Qed.
Lemma ix_kept x : 0 <= x < 2 ^ 64 -> x <> PI L am idx fr - 3 -> ~ (PI L am idx fr <= x < ENDI L am idx) -> ~ SCR x ->
mem' (w64 x) = mem (w64 x).
Proof using HC SP.
intros H1 H2 H3 H4. pose proof SP as [_ _ _ _ _ FRM]. apply FRM; [exact H1 | exact H2 | | exact H4].
intros T. apply H3. exact (ix_TW x T).
Qed.
Lemma ix_slot_noscr x : ptr_addr L (slot_start am idx) - 4 <= x < ENDI L am idx -> ~ SCR x /\ 0 <= x < 2 ^ 64.
Proof using HC SP.
intros Hx. destruct (ix_reg x Hx) as (L1 & _ & (k & rg & Hr & Hl & Hxr)). pose proof alloc_ceiling_lt.
split; [exact (ix_scr_reg k rg x Hr Hl Hxr) | lia].
Qed.
Lemma ix_ftail c : In c (frame_tail_cells (rs_am am idx (fr_off fr) n) idx) -> cell_mem B L mem' c.
Proof using HC SP.
pose proof SP as [_ _ Wn W45 _ _]. rewrite ix_ft. intros Hc. apply in_app_iff in Hc as [Hc|Hc].
- destruct (0 <? RSVI am fr n) eqn:Er; [|destruct Hc]. apply Z.ltb_lt in Er. destruct Hc as [<-|[]].
apply (ix_cell_bytes B L mem' _ (PI L am idx fr + n) 0); [cbn [mc_loc]; rewrite loc_addr_padd_; reflexivity | reflexivity | exact (Wn Er)].
- destruct (5 <=? RSVI am fr n) eqn:Er; [|destruct Hc]. apply Z.leb_le in Er. destruct (W45 Er) as [W4 W5].
destruct Hc as [<-|[<-|[]]].
+ apply (ix_cell_bytes B L mem' _ (ENDI L am idx - 4) (RSVI am fr n)); [cbn [mc_loc]; rewrite loc_addr_padd_; unfold ENDI; lia | reflexivity | exact W4].
+ apply (ix_cell_bytes B L mem' _ (ENDI L am idx - 5) 0); [cbn [mc_loc]; rewrite loc_addr_padd_; unfold ENDI; lia | reflexivity | exact W5].
Qed.
Lemma ix_memrep : memrep B L (A_ip A g am idx fr n) mem'.
Proof using HC SP.
pose proof HC as [MX Hu Hidx Hfr Hk Hn Hc1]. pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (mc_wf _ _ _ _ _ M) as HW.
pose proof (mc_layout _ _ _ _ _ M) as HL. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
pose proof SP as [SCRh W3 Wn W45 PRES FRM].
pose proof ix_WF2 as HW2.
assert (HL2 : layout_ok L (A_ip A g am idx fr n)) by (unfold A_ip; apply layout_ok_upd_meta; exact HL).
assert (HL0 : layout_ok L (ix_A0 A g am idx)) by (unfold ix_A0; apply layout_ok_upd_meta; exact HL).
assert (Hidx0 : 0 <= idx <= am_last (ix_am0 am idx)) by (rewrite ix_last0; exact Hidx).
assert (Hmeta : meta_slot_cells g (Some (MUsed (rs_am am idx (fr_off fr) n))) = meta_slot_cells g (Some (MUsed (ix_am0 am idx)))).
{ unfold rs_am, ix_am0. rewrite !meta_slot_cells_upd_slot. reflexivity. }
destruct (image_upd_slot_eq _ g _ _ idx ix_Mg0 Hidx0 ix_SE0' Hmeta) as (l1 & l2 & E0 & E2 & _).
rewrite <- ix_EA in E2.
pose proof (image_cells_disjoint _ L HW2 HL2) as DISJ2. rewrite E2 in DISJ2.
destruct ix_p3' as (c3 & Hc3 & Rc3).
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn').
assert (OLD : forall c, In c (l1 ++ l2) -> cell_mem B L mem' c).
{ intros c Hc.
assert (Hc0 : In c (image (ix_A0 A g am idx))).
{ rewrite E0. apply in_app_iff in Hc as [Hc|Hc]; apply in_app_iff; [left; exact Hc | right; apply in_app_iff; right; exact Hc]. }
pose proof (ix_img0 c Hc0) as HcA.
apply (cell_keep B L mem mem' c (proj1 (Forall_forall _ _) (mc_cells _ _ _ _ _ M) c HcA)).
intros k Hk'.
destruct (image_in_footprint A L c HW HL HcA) as (e & He & Hincl).
assert (Hy : loc_addr L (fst e) <= loc_addr L (mc_loc c) + Z.of_nat k < loc_addr L (fst e) + snd e)
by (unfold range_incl, cell_range, crange in Hincl; cbn [fst snd] in Hincl; lia).
destruct (ix_foot_scr e _ He Hy) as [NS R64].
apply ix_kept; [exact R64 | | | exact NS].
- intros X3. destruct (YN26_cf.pairwise_app_mid ranges_disjoint (cell_range L) l1 (slot_rest (rs_am am idx (fr_off fr) n) idx) l2 c3 c DISJ2 Hc3 Hc) as [D|D];
rewrite Rc3 in D; unfold ranges_disjoint, cell_range in D; cbn [fst snd] in D; lia.
- intros X4.
pose proof (slot_body_free [] (Some (g, idx)) U0 (ix_A0 A g am idx) L ix_HI0 HL0 g (ix_am0 am idx) idx
(poff (slot_start (ix_am0 am idx) idx)) (poff (slot_start (ix_am0 am idx) idx) + stride_of (ix_am0 am idx) - IB)
ix_Hu0 Hidx0 ix_none0 ltac:(lia) ltac:(lia) c) as D.
specialize (D ltac:(unfold imageX, image in *; rewrite used_metasX_nil; apply in_app_iff; left; exact Hc0)).
unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D.
rewrite ix_ss0, ix_mem0, ix_st0, poff_slot_start, Emem in D. cbn [prid poff] in D.
rewrite EP, EE in X4. unfold UNIT, IB in *. lia. }
split; [|split].
- apply Forall_forall. intros c Hc. rewrite E2 in Hc. rewrite !in_app_iff in Hc. destruct Hc as [Hc|[Hc|Hc]].
+ apply OLD. apply in_app_iff. left. exact Hc.
+ destruct (ix_rest' c Hc) as [(HcA & Hb) | (Eloc & Ew & Ev)].
* apply (cell_keep B L mem mem' c (proj1 (Forall_forall _ _) (mc_cells _ _ _ _ _ M) c HcA)).
intros k Hk'. destruct (Hb k Hk') as [B1 B2].
assert (Hrg : ptr_addr L (slot_start am idx) - 4 <= loc_addr L (mc_loc c) + Z.of_nat k < ENDI L am idx).
{ rewrite ES, EP in B1. rewrite ES, EE. lia. }
destruct (ix_slot_noscr _ Hrg) as [NS R64].
apply ix_kept; [exact R64 | exact B2 | lia | exact NS].
* apply (ix_cell_bytes B L mem' c (PI L am idx fr - 3) (idx + 32 * RCI am fr n) Eloc Ev). rewrite Ew. exact W3.
+ apply OLD. apply in_app_iff. right. exact Hc.
- apply Forall_forall. intros c Hc. rewrite ix_EA in Hc.
destruct (tail_cells_upd' _ g _ _ idx c ix_Mg0 ix_SE0' Hidx0 ix_none0 Hc) as [Hold | Hnew].
+ pose proof (YN26_cf.tail_cells_upd A g am (ix_am0 am idx) idx c Mg ix_SE0 ix_none0 Hold) as HcA.
apply (cell_keep B L mem mem' c (proj1 (Forall_forall _ _) (mc_tail _ _ _ _ _ M) c HcA)).
intros k Hk'. pose proof (ix_tail0 c k Hold Hk') as AV.
pose proof (proj1 (Forall_forall _ _) (mc_tail_geom _ _ _ _ _ M) c HcA k Hk') as [(e & He & Hy) _].
destruct (ix_foot_scr e _ He Hy) as [NS R64].
apply ix_kept; [exact R64 | intros X3 | intros X4 | exact NS]; apply AV; rewrite ES, EE; [rewrite EP in X3 | rewrite EP, EE in X4]; lia.
+ exact (ix_ftail c Hnew).
- unfold A_ip. rewrite footprint_upd_meta. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) e He) as F. unfold foot_ok in F |- *.
destruct e as [[o|q] len]; cbn [fst snd] in F |- *; [exact I|]. intros x Hx.
destruct (Z.eq_dec x (PI L am idx fr - 3)) as [X3|X3]; [apply PRES; left; exact X3|].
destruct (ix_TWI_dec L am idx fr n x) as [T|T]; [apply PRES; right; exact T|].
destruct (F x Hx) as [b Hb]. exists b. rewrite <- Hb.
destruct (ix_foot_scr (LMem q, len) x He Hx) as [NS R64].
apply FRM; [exact R64 | exact X3 | exact T | exact NS].
Qed.
Lemma ix_statics : statics_ok B mem'.
Proof using HC SP.
pose proof HC as [MX _ _ _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof SP as [SCRh _ _ _ _ FRM].
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
apply (YN26_cf.statics_ok_ext B mem mem' (mc_statics _ _ _ _ _ M)). intros a Ha.
pose proof (mc_syms _ _ _ _ _ M) as SY. pose proof (so_statics_img _ SY a Ha) as Hi. pose proof (so_img_hi _ SY a Hi) as Hlo.
assert (NR : ~ (ptr_addr L (slot_start am idx) - 4 <= a < ENDI L am idx)) by (intros R; destruct (ix_reg a R) as (_ & NI & _); exact (NI Hi)).
apply same_views. apply FRM.
- pose proof alloc_ceiling_lt. lia.
- intros X3. apply NR. rewrite ES, EE. rewrite EP in X3. unfold UNIT, IB in *. lia.
- intros T. apply NR. destruct (ix_TW a T) as [T1 T2]. rewrite ES, EE. rewrite EP in T1. rewrite EE in T2. lia.
- intros HS. destruct (SCRh a HS) as [X|(_ & Hns & _)]; [lia | exact (Hns Ha)].
Qed.
Lemma ix_MRx : MRx B L (A_ip A g am idx fr n) mem' md.
Proof using HC SP.
pose proof HC as [MX Hu _ _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (mc_md _ _ _ _ _ M) as (H1 & H2 & H3).
assert (HL2 : layout_ok L (A_ip A g am idx fr n)) by (unfold A_ip; apply layout_ok_upd_meta; exact (mc_layout _ _ _ _ _ M)).
apply MRx_intro.
- exact (MRc_intro B L _ mem' md (mc_syms _ _ _ _ _ M) ix_WF2 ix_bounded HL2 (mc_ctx _ _ _ _ _ M) (mc_sec _ _ _ _ _ M)
ix_memrep (tail_geom_of_WF _ L ix_WF2 HL2) ix_statics (ledger_ok_upd_meta B L g _ A md (mc_ledger _ _ _ _ _ M)) H1 H2 H3).
- exact (ledger_x_same_regions L A (A_ip A g am idx fr n) md md (MRx_ledger_x _ _ _ _ _ MX) eq_refl eq_refl eq_refl).
- exact ix_rsv.
- unfold A_ip. pose proof (MRx_ama _ _ _ _ _ MX) as AM. unfold ama_ok in *. cbn. exact AM.
- unfold A_ip. apply (span_ok_upd_same3 A g am); [exact (MRx_span _ _ _ _ _ MX) | exact Mg | reflexivity | reflexivity | reflexivity].
Qed.
Lemma ix_frame x : (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x).
Proof using HC SP.
intros Hx HS. pose proof HC as [MX _ _ _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof SP as [_ _ _ _ _ FRM].
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
assert (NR : ~ (ptr_addr L (slot_start am idx) - 4 <= x < ENDI L am idx)).
{ intros R. destruct (ix_reg x R) as ((R1 & R2) & NI & _). destruct Hx as [Hx|Hx]; [lia | exact (NI Hx)]. }
assert (R64 : 0 <= x < 2 ^ 64).
{ destruct Hx as [Hx|Hx]; [lia|]. pose proof (so_img_hi _ (mc_syms _ _ _ _ _ M) x Hx). pose proof alloc_ceiling_lt. lia. }
apply same_views. apply FRM; [exact R64 | | | exact HS].
- intros X3. apply NR. rewrite ES, EE. rewrite EP in X3. unfold UNIT, IB in *. lia.
- intros T. apply NR. destruct (ix_TW x T) as [T1 T2]. rewrite ES, EE. rewrite EP in T1. rewrite EE in T2. lia.
Qed.
Lemma ix_blocks_kept q k i : In (q, k) (user_blocks A) -> In (q, k) (user_blocks (A_ip A g am idx fr n)) -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i).
Proof using HC SP.
intros HqA Hq' Hi. pose proof HC as [MX _ _ _ _ _ _]. pose proof (MRx_MRc _ _ _ _ _ MX) as M.
pose proof (mc_wf _ _ _ _ _ M) as HW. pose proof (mc_layout _ _ _ _ _ M) as HL. pose proof SP as [_ _ _ _ _ FRM].
destruct (blocks_facts B L A mem md q k i M HqA Hi) as (_ & B1 & B2 & NO).
apply same_views. apply FRM.
- pose proof alloc_ceiling_lt. lia.
- intros X3. apply NO. left. rewrite X3. exact ix_p3_owned.
- intros T. destruct (ix_tw_cell _ T) as (c & kk & Hc & Hkk & Ec).
assert (HL2 : layout_ok L (A_ip A g am idx fr n)) by (unfold A_ip; apply layout_ok_upd_meta; exact HL).
pose proof (proj1 (Forall_forall _ _) (tail_geom_of_WF _ L ix_WF2 HL2) c Hc kk Hkk) as [_ NB].
apply NB. exists (q, k). split; [exact Hq'|]. cbn [fst snd]. rewrite Ec. unfold ptr_addr. lia.
- intros HS. destruct (block_region A q k HW HqA) as (kr & o & rg & Eq & Hr & _ & Hl & Ho & _ & Hfit & _).
apply (ix_scr_reg kr rg (ptr_addr L q + i) Hr Hl); [|exact HS]. rewrite Eq. unfold ptr_addr. cbn [loc_addr]. lia.
Qed.
Lemma ix_contents i : 0 <= i < Z.min n (fr_n fr) ->
mbyte (ms_segs B) mem' (PI L am idx fr + i) = mbyte (ms_segs B) mem (PI L am idx fr + i).
Proof using HC SP.
intros Hi. pose proof SP as [_ _ _ _ _ FRM].
destruct ix_geo as (kr & ko & rg & Emem & ES & EP & EE & ST16 & P1 & P2 & C4 & Hr & Hrk & Hrl & Hko & Hfit & R4096 & Rceil & Rimg & InR & Of & Nf & Bf & Bn & Hn).
assert (Hmin : i < n /\ i < fr_n fr) by lia.
destruct (ix_slot_noscr (PI L am idx fr + i) ltac:(rewrite ES, EP, EE; lia)) as [NS R64].
apply same_views. apply FRM; [exact R64 | lia | | exact NS].
unfold TWI, RSVI. rewrite EP, EE. unfold UNIT, IB. lia.
Qed.
Lemma ix_main :
MRx B L (A_ip A g am idx fr n) mem' md /\
WF (A_ip A g am idx fr n) /\ bounded (A_ip A g am idx fr n) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)) /\
(forall q k i, In (q, k) (user_blocks A) -> In (q, k) (user_blocks (A_ip A g am idx fr n)) -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i)) /\
PI L am idx fr <> 0 /\
(forall i, 0 <= i < Z.min n (fr_n fr) -> mbyte (ms_segs B) mem' (PI L am idx fr + i) = mbyte (ms_segs B) mem (PI L am idx fr + i)) /\
(exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am idx fr, fr_n fr) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks (A_ip A g am idx fr n) = m1 ++ (frame_ptr am idx fr, n) :: m2).
Proof using HC SP.
split; [exact ix_MRx|]. split; [exact ix_WF2|]. split; [exact ix_bounded|].
split; [exact ix_frame|]. split; [exact ix_blocks_kept|]. split; [exact ix_PI_nz|].
split; [exact ix_contents | exact ix_blocks].
Qed.
End mm.
End ip.
Theorem realloc_ip_leaf B L A mem md g am idx fr n mem' SCR :
MRx B L A mem md -> usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
0 <= n -> ra_c1 am (fr_off fr) n = true ->
ip_memspec B L A mem g am idx fr n mem' SCR ->
MRx B L (A_ip A g am idx fr n) mem' md /\
WF (A_ip A g am idx fr n) /\ bounded (A_ip A g am idx fr n) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)) /\
(forall q k i, In (q, k) (user_blocks A) -> In (q, k) (user_blocks (A_ip A g am idx fr n)) -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i)) /\
PI L am idx fr <> 0 /\
(forall i, 0 <= i < Z.min n (fr_n fr) -> mbyte (ms_segs B) mem' (PI L am idx fr + i) = mbyte (ms_segs B) mem (PI L am idx fr + i)) /\
(exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am idx fr, fr_n fr) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks (A_ip A g am idx fr n) = m1 ++ (frame_ptr am idx fr, n) :: m2).
Proof using.
intros MX Hu Hidx Hfr Hk Hn Hc SP.
assert (HC : ipc B L A mem md g am idx fr n) by (split; assumption).
exact (ix_main B L A mem md g am idx fr n HC mem' SCR SP).
Qed.
End h.
