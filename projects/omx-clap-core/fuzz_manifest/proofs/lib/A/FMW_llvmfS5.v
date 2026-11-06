(* LLVMFuzzerTestOneInput 0x8091c, segment 0x80a60..0x80a8c (fuzz_manifest.c:305-307): live := fuzz_alloc_live ();
   fuzz_alloc_peak_reset (); named := lv2_locate_manifest_names (t, u); check_bounded_alloc (fuzz_alloc_peak () - live,
   un). From LF_P4 to LF_P5. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_llvmfP FMW_llvmfD.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a callee-saved register after a run (HS holds it as atom n of the resumed register file) and a program call (HP) *)
Local Ltac lf5_carry HS HP n Hv :=
  lazymatch type of HS with st_ok _ (Ereg ?rg ?ex) _ _ =>
  lazymatch type of Hv with getr _ ?r' = _ =>
    eapply (fmw_carry _ rg ex _ _ _ _ n _ HS);
    [ vm_compute; reflexivity
    | rewrite (ew_Ereg_nat rg ex n r' eq_refl); exact Hv
    | exact HP
    | fmw_cs_side ] end end.

(* memory equal at every address below 2 ^ 64 is equal at every address *)
Lemma lf5_sb_all : forall (m m' : word -> option byte) a, same_below m m' (2 ^ 64) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros m m' a H.
assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity. }
rewrite E. apply H. apply Z.mod_pos_bound. lia.
Qed.
Lemma lf5_aview_all : forall (H : word -> bool) m m' a, same_below m m' (2 ^ 64) ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a Hs. unfold aview, mbyte, mrestrict. rewrite (lf5_sb_all m m' a Hs). reflexivity. Qed.

(* x - y as the run writes it: x + y * (2^64 - 1) (FMW_llvmfS1.v lf_U_sub) *)
Lemma lf5_U_sub : forall E a b m x y, U E a = x -> U E b = y -> m mod 2 ^ 64 = 2 ^ 64 - 1 -> 0 <= x - y < 2 ^ 64 ->
  U E (SAlu ALU_ADD a (SMd M_MUL b (SLit m))) = x - y.
Proof.
intros E a b m x y Ha Hb Hm Hr. rewrite U_SAlu, U_SMd, U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite Hm, Z.add_mod_idemp_r by lia.
replace (x + y * (2 ^ 64 - 1)) with (x - y + y * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. exact Hr.
Qed.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis ALIVE : fuzz_alloc_live_spec tfibsegs B.
Hypothesis APRESET : fuzz_alloc_peak_reset_spec tfibsegs B.
Hypothesis APEAK : fuzz_alloc_peak_spec tfibsegs B.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.
Hypothesis CBA : check_bounded_alloc_spec tfibsegs B.

(* a run that writes no memory (resumed with fmw_resume_nr) and leaves sp, s5 and the callee-saved registers outside
   lf_X as they were keeps lf_core *)
Lemma lf5_run : forall cx ly S (W : world tfibsegs) regs mem md k ss ms md',
  lf_core B cx ly S W regs mem md k ->
  st_ok tfibsegs (Ereg regs []) ss (restrict (w_H W) ms) ->
  atoms_kept ss lf_X = true -> sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 21%bv = SOff 21 0 ->
  same_below mem (ms_mem ms) (2 ^ 64) ->
  lf_J B cx ly S W (ms_mem ms) md' k ->
  lf_core B cx ly S W (ms_regs ms) (ms_mem ms) md' k.
Proof.
intros cx ly S W regs mem md k ss ms md' (HJ & HFR & Hsp & HK & H21 & HIN & HRO) HS HA E2 E21 SB HJ'.
unfold lf_J in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 alloc_ceiling_val) as AC.
assert (FL : LLVMF_STK = 32768) by reflexivity.
split; [exact HJ'|].
split; [apply (lf_frame_below cx W mem (ms_mem ms) SB); [unfold LF_FRAME; lia | lia | exact HFR]|].
split; [unfold spZ; rewrite (fmw_reg_atom _ regs [] ss ms 2%bv 2%bv 2 HS E2 eq_refl); exact Hsp|].
split; [exact (kept_step (w_H W) (lx_regs cx) regs [] ss ms (ms_regs ms) lf_X HK HS HA (fun _ _ => eq_refl))|].
split; [rewrite (fmw_reg_atom _ regs [] ss ms 21%bv 21%bv 21 HS E21 eq_refl); exact H21|].
split; [intros i Hi; rewrite (lf5_aview_all (w_H W) mem (ms_mem ms) _ SB); exact (HIN i Hi)|].
exact (arodata_below B W mem (ms_mem ms) (same_below_mono _ _ _ alloc_ceiling SB ltac:(lia)) HRO).
Qed.

(* one program call from a state with lf_core (sp = sp0 - 64, s0 = un): its fpre, the composed journal, lf_core after
   it, and the C strings the caller keeps *)
Lemma lf5_call : forall cx ly S (W : world tfibsegs) regs mem md k pc rr STKc FPc kc
    (Qc : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (Q : world tfibsegs -> config -> Prop),
  lf_base B cx -> lf_core B cx ly S W regs mem md k ->
  (fpre tfibsegs B STKc ly S W regs mem md [] ->
     SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (fpost tfibsegs B STKc FPc regs ly S W mem md kc Qc)) ->
  (forall x, In x (ablocks B (lx_ly cx) (lx_S cx)) -> In x (ablocks B ly S)) ->
  getr regs 1 = Z_to_bv 64 rr -> 4096 <= rr < 2 ^ 64 -> rr mod 2 = 0 ->
  getr regs 8 = w64 (lx_un cx) ->
  0 <= STKc -> STKc + LF_FRAME <= LLVMF_STK ->
  (forall a, inFP FPc a -> inFP FM_PSTAT_FP a) ->
  (forall ly2 S2 W2 regs2 mem2 md2, Qc ly2 S2 W2 regs2 mem2 md2 ->
     forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2,
     lf_core B cx ly2 S2 W2 regs2 mem2 md2 (k + kc) -> aregs_preserved regs regs2 -> Qc ly2 S2 W2 regs2 mem2 md2 ->
     (forall p l, cstr_kept B ly S p l -> cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W2 mem2 p l) ->
     SRr tfibsegs W2 (cfg_at tfibsegs rr regs2 mem2 md2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q.
Proof.
intros cx ly S W regs mem md k pc rr STKc FPc kc Qc Q HB HC HCALL Hinc Hra Hrr Hrr2 H8 HS0 HSb HFP HQinc K.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HC as (HJ & HFR & Hsp & HK & H21 & HIN & HRO).
unfold lf_J in HJ.
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & _ & Hblk & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 alloc_ceiling_val) as AC.
assert (FL : LLVMF_STK = 32768) by reflexivity.
pose proof (lx_ranges B cx HB) as (Hk255 & _ & _ & _ & _ & _ & _ & _ & Hun & _ & _).
assert (Hsp' : spZ regs = lx_sp0 cx + -64) by (unfold LF_FRAME in Hsp; lia).
assert (HPRE : fpre tfibsegs B STKc ly S W regs mem md []).
{ split; [|exact HRO].
  apply (afn_pre_at tfibsegs B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
    ly S W mem md k regs STKc (-64) [] HJ Hsp').
  all: first [ reflexivity | lia | (unfold LF_FRAME in HSb; lia)
             | (rewrite Hra; apply ret_ok_even; rewrite unsigned_lit_small by lia; exact Hrr2)
             | (unfold raZ; rewrite Hra, unsigned_lit_small by lia; lia)
             | (rewrite (kept_get _ _ _ 3%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp0)
             | (rewrite (kept_get _ _ _ 4%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp0)
             | (apply achain_low; unfold s0Z; rewrite H8; unfold w64; rewrite unsigned_lit_small by lia; lia) ]. }
eapply SRr_bind; [exact (HCALL HPRE)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP & HQ).
rewrite Hra.
change (mkCfg (mkst regs2 (Z_to_bv 64 rr) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs rr regs2 mem2 md2).
pose proof (ajournal_sub_incl B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
  ly S W mem md k STKc (spZ regs) FPc [] ly2 S2 W2 mem2 md2 kc HJ HJc
  ltac:(rewrite Hsp'; unfold LF_FRAME in HSb; lia) ltac:(rewrite Hsp'; lia) HFP) as HJ2.
cbn [app] in HJ2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & F2c & _).
assert (Hinc2 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) by exact (HQinc ly2 S2 W2 regs2 mem2 md2 HQ).
assert (Hcl : ~ YI16.sink_open_fp FPc).
{ intros (r & Hr & H0). apply pstat_closed. destruct (HFP 0 (ex_intro _ r (conj Hr H0))) as (r' & Hr' & H0').
  exists r'. split; [exact Hr' | exact H0']. }
assert (Hro : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> ~ inFP FPc a)
  by (intros a Ha Hf; exact (pstat_not_roP a Ha (HFP a Hf))).
assert (Himg : forall a, inFP FPc a -> in_img tfibsegs a) by (intros a Ha; exact (pstat_img a (HFP a Ha))).
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hcl Hro HRO) as HRO2.
assert (HK2 : kept_from (lx_regs cx) regs2 lf_X) by (intros r Hc HX; rewrite (HP r Hc); exact (HK r Hc HX)).
apply (K ly2 S2 W2 regs2 mem2 md2); [| exact HP | exact HQ |].
2: { intros p l Hk Hok. exact (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p l IMG HJc Hinc2 Himg HRO2 Hk Hok). }
split; [exact HJ2|].
split.
{ apply (lf_frame_kept cx W W2 mem mem2); [|exact HFR]. intros a Ha. unfold LF_FRAME in Ha.
  apply F1c; [lia | rewrite Hsp'; lia]. }
split; [unfold spZ; rewrite (fmw_pres _ _ 2%bv HP ltac:(fmw_cs_side)); exact Hsp|].
split; [exact HK2|].
split; [rewrite (fmw_pres _ _ 21%bv HP ltac:(fmw_cs_side)); exact H21|].
split; [|exact HRO2].
intros i Hi. rewrite <- (HIN i Hi).
assert (Hin : In (lx_p cx, lx_n cx) (ablocks B ly S))
  by (destruct Hblk as [(Hn0 & _) | (_ & Hin0)]; [lia | exact (Hinc _ Hin0)]).
assert (Hrq : req_size (lx_n cx) = lx_n cx) by (unfold req_size; destruct (Z.eqb_spec (lx_n cx) 0); lia).
apply (F2c (lx_p cx) (lx_n cx) i Hin (Hinc2 _ Hin)); [rewrite Hrq; lia|].
intros Hf. apply (blk_img tfibsegs B LAWS ly S W mem md (lx_p cx) (lx_n cx) (lx_p cx + i) HAR Hin ltac:(rewrite Hrq; lia)).
exact (Himg _ Hf).
Qed.

Lemma lf_seg5 : forall cx ly S W regs mem md k u t, lf_base B cx -> lf_P4 B cx ly S W regs mem md k u t ->
  (forall ly' S' W' regs' mem' md' k', lf_P5 B cx ly' S' W' regs' mem' md' k' u t ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P5 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P4 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u t HB HP4 K5.
destruct HP4 as (HC & Hk & Hperm & GL & Htn & Hu & Ht & R8 & R9 & R20).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof (lx_ranges B cx HB) as (Hk255 & _ & _ & _ & _ & _ & _ & _ & Hun & _ & Hlub).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hnev0 & Hbb0 & _ & _ & Hc0 & Hc1 & Hlv0).
set (BL := (t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) in *.
assert (Hkt : forall ly' S', Permutation (ablocks B ly' S') BL -> cstr_kept B ly' S' t (lx_tb cx))
  by (intros ly' S' Hp; exact (lf_kept_blk B ly' S' t _ _ (lx_tb cx) Hp ltac:(unfold lx_tn; lia))).
assert (Hku : forall ly' S', Permutation (ablocks B ly' S') BL -> cstr_kept B ly' S' u (lx_ub cx))
  by (intros ly' S' Hp; exact (lf_kept_blk B ly' S' u _ _ (lx_ub cx) (Permutation_trans Hp (perm_swap _ _ _))
        ltac:(unfold lx_un; lia))).
assert (Hinc : forall ly' S', Permutation (ablocks B ly' S') BL ->
  forall x, In x (ablocks B (lx_ly cx) (lx_S cx)) -> In x (ablocks B ly' S'))
  by (intros ly' S' Hp x Hx; exact (Permutation_in _ (Permutation_sym Hp) (in_cons _ _ _ (in_cons _ _ _ Hx)))).
assert (FA : STK_fuzz_alloc = 16) by reflexivity.
assert (FN : STK_names = 16640) by reflexivity.
assert (FC : STK_check_bounded_alloc = 16) by reflexivity.
assert (FL : LLVMF_STK = 32768) by reflexivity.
(* ======== 0x80a60: jal fuzz_alloc_live ======== *)
pose proof (fmw_resume_nr W regs [] mem LF_P4) as HS1.
unfold cfg_at. change (w64 LF_P4) with (Z_to_bv 64 LF_P4).
pose proof HC as (HJ1 & _). unfold lf_J in HJ1.
aj_run_to fmw_tbl_llvmf_ok HS1 HJ1 A_fuzz_alloc_live.
{ apply awr_ok_nil. }
lazymatch type of HS1 with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms1) |- _ => exact (frame_nil_same _ mem (ms_mem ms1) H) end).
assert (SBc1 : same_below mem (ms_mem ms1) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (lf5_run _ _ _ _ _ _ _ _ _ _ _ HC HS1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) SB1 HJ1) as HC1.
pose proof (fmw_reg_lit _ _ _ ms1 1%bv 0x80a64 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
assert (Q8 : getr (ms_regs ms1) 8 = w64 (lx_un cx))
  by (rewrite (fmw_reg_atom _ regs [] _ ms1 8%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl); exact R8).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ ms1 HS1 eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 A_fuzz_alloc_live) (ms_mem ms1) (seg_rom tfibsegs)) ?m)
  with (cfg_at tfibsegs A_fuzz_alloc_live (ms_regs ms1) (ms_mem ms1) m).
eapply (lf5_call cx ly S W (ms_regs ms1) (ms_mem ms1) _ _ A_fuzz_alloc_live 0x80a64 STK_fuzz_alloc [] 0 _ _ HB HC1
  (fun HPRE => ALIVE ly S W (ms_regs ms1) (ms_mem ms1) _ [] _ _ _ _ HPRE (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SBc1 GL))
  (Hinc ly S Hperm) Q1 ltac:(lia) eq_refl Q8 ltac:(lia) ltac:(unfold LF_FRAME; lia)
  (fun a Ha => False_ind _ (inFP_nil a Ha))).
{ intros ? ? ? ? ? ? (_ & E & _) x Hx. rewrite E. exact Hx. }
intros ly1 S1 W1 rg1 mem1 md1 HD1 HP1 (H10a & Hbl1 & GL1) HCS1.
assert (Hperm1 : Permutation (ablocks B ly1 S1) BL) by (rewrite Hbl1; exact Hperm).
pose proof (HCS1 t _ (Hkt ly S Hperm) (cstr_ok_below W mem (ms_mem ms1) t _ SBc1 Ht)) as Ht1.
pose proof (HCS1 u _ (Hku ly S Hperm) (cstr_ok_below W mem (ms_mem ms1) u _ SBc1 Hu)) as Hu1.
assert (R8a : getr rg1 8 = w64 (lx_un cx)) by (lf5_carry HS1 HP1 8%nat R8).
assert (R9a : getr rg1 9 = w64 u) by (lf5_carry HS1 HP1 9%nat R9).
assert (R20a : getr rg1 20 = w64 t) by (lf5_carry HS1 HP1 20%nat R20).
(* ======== 0x80a64: mv s2, a0; jal fuzz_alloc_peak_reset ======== *)
pose proof (fmw_resume_nr W1 rg1 [] mem1 0x80a64) as HS2.
unfold cfg_at. change (w64 0x80a64) with (Z_to_bv 64 0x80a64).
pose proof HD1 as (HJ2 & _). unfold lf_J in HJ2.
aj_run_to fmw_tbl_llvmf_ok HS2 HJ2 A_fuzz_alloc_peak_reset.
{ apply awr_ok_nil. }
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
assert (SB2 : same_below mem1 (ms_mem ms2) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem1 (ms_mem ms2) |- _ => exact (frame_nil_same _ mem1 (ms_mem ms2) H) end).
assert (SBc2 : same_below mem1 (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB2); lia).
pose proof (lf5_run _ _ _ _ _ _ _ _ _ _ _ HD1 HS2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) SB2 HJ2) as HC2.
pose proof (fmw_reg_lit _ _ _ ms2 1%bv 0x80a6c HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1b.
assert (Q8b : getr (ms_regs ms2) 8 = w64 (lx_un cx))
  by (rewrite (fmw_reg_atom _ rg1 [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl); exact R8a).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ ms2 HS2 eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 A_fuzz_alloc_peak_reset) (ms_mem ms2) (seg_rom tfibsegs)) ?m)
  with (cfg_at tfibsegs A_fuzz_alloc_peak_reset (ms_regs ms2) (ms_mem ms2) m).
eapply (lf5_call cx ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) _ _ A_fuzz_alloc_peak_reset 0x80a6c STK_fuzz_alloc FM_PSTAT_FP 0
  _ _ HB HC2
  (fun HPRE => APRESET ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) _ [] _ _ _ _ HPRE
     (fm_glob_below W1 mem1 (ms_mem ms2) _ _ _ _ SBc2 GL1))
  (Hinc ly1 S1 Hperm1) Q1b ltac:(lia) eq_refl Q8b ltac:(lia) ltac:(unfold LF_FRAME; lia) (fun a Ha => Ha)).
{ intros ? ? ? ? ? ? (E & _) x Hx. rewrite E. exact Hx. }
intros ly2 S2 W2 rg2 mem2 md2 HD2 HP2 (Hbl2 & GL2) HCS2.
assert (Hperm2 : Permutation (ablocks B ly2 S2) BL) by (rewrite Hbl2; exact Hperm1).
pose proof (HCS2 t _ (Hkt ly1 S1 Hperm1) (cstr_ok_below W1 mem1 (ms_mem ms2) t _ SBc2 Ht1)) as Ht2.
pose proof (HCS2 u _ (Hku ly1 S1 Hperm1) (cstr_ok_below W1 mem1 (ms_mem ms2) u _ SBc2 Hu1)) as Hu2.
assert (R8b : getr rg2 8 = w64 (lx_un cx)) by (lf5_carry HS2 HP2 8%nat R8a).
assert (R9b : getr rg2 9 = w64 u) by (lf5_carry HS2 HP2 9%nat R9a).
assert (R20b : getr rg2 20 = w64 t) by (lf5_carry HS2 HP2 20%nat R20a).
assert (R18b : getr rg2 18 = w64 (lx_live cx)) by (lf5_carry HS2 HP2 10%nat H10a).
(* ======== 0x80a6c: a0 := t; a1 := u; jal lv2_locate_manifest_names ======== *)
pose proof (fmw_resume_nr W2 rg2 [] mem2 0x80a6c) as HS3.
unfold cfg_at. change (w64 0x80a6c) with (Z_to_bv 64 0x80a6c).
pose proof HD2 as (HJ3 & _). unfold lf_J in HJ3.
aj_run_to fmw_tbl_llvmf_ok HS3 HJ3 A_names.
{ apply awr_ok_nil. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
assert (SB3 : same_below mem2 (ms_mem ms3) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem2 (ms_mem ms3) |- _ => exact (frame_nil_same _ mem2 (ms_mem ms3) H) end).
assert (SBc3 : same_below mem2 (ms_mem ms3) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB3); lia).
pose proof (lf5_run _ _ _ _ _ _ _ _ _ _ _ HD2 HS3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) SB3 HJ3) as HC3.
pose proof (fmw_reg_lit _ _ _ ms3 1%bv 0x80a78 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1c.
assert (Q8c : getr (ms_regs ms3) 8 = w64 (lx_un cx))
  by (rewrite (fmw_reg_atom _ rg2 [] _ ms3 8%bv 8%bv 8 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact R8b).
assert (Q10c : getr (ms_regs ms3) 10 = w64 t)
  by (rewrite (fmw_reg_atom _ rg2 [] _ ms3 10%bv 20%bv 20 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact R20b).
assert (Q11c : getr (ms_regs ms3) 11 = w64 u)
  by (rewrite (fmw_reg_atom _ rg2 [] _ ms3 11%bv 9%bv 9 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact R9b).
assert (Hctx : In (raZ (ms_regs ms3) :: spine []) CTX_lv2_locate_manifest_names).
{ unfold raZ. rewrite Q1c, unsigned_lit_small by lia. cbn [spine map].
  unfold CTX_lv2_locate_manifest_names. repeat (first [left; reflexivity | right]). }
assert (Hnev : st_nev S2 + EV_names <= EV_MAX).
{ pose proof HD2 as ((_ & _ & _ & _ & _ & _ & Hnv & _) & _).
  assert (E1 : EV_LLVMF = 2060) by reflexivity. assert (E2 : EV_check_no_overread = 12) by reflexivity.
  assert (E3 : EV_names = 2) by reflexivity.
  clear - Hnv Hnev0 Hk E1 E2 E3. lia. }
assert (Hbb : blocks_bytes S2 + LIVE_names <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hperm2). unfold BL. rewrite !bsum_cons.
  rewrite <- (blocks_bytes_bsum B (lx_ly cx) (lx_S cx)). cbn [snd].
  assert (E1 : LIVE_names = 2 ^ 9) by reflexivity. assert (E2 : LIVE_LIB = 2 ^ 33) by reflexivity.
  assert (E3 : MANIFEST_MAX = 4 * 2 ^ 20) by reflexivity.
  clear - Hbb0 Htn Hun Hk255 E1 E2 E3. lia. }
assert (Hlv : lx_live cx + Z.of_nat (length (lx_ub cx)) + 3 < 2 ^ 33) by lia.
assert (Hq : quiet (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 2) SIZE_MAXZ 1).
{ split; [reflexivity|]. unfold CNT_LIB in Hc1. destruct (length (lx_ub cx) =? 0)%nat; lia. }
assert (Hcnt : (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 2) + 1 < 2 ^ 33)
  by (destruct Hq as (_ & _ & Hq2); exact Hq2).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ ms3 HS3 eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_names) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
  with (cfg_at tfibsegs A_names (ms_regs ms3) (ms_mem ms3) m).
eapply (lf5_call cx ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ _ A_names 0x80a78 STK_names FM_PSTAT_FP EV_names
  _ _ HB HC3
  (fun HPRE => NAMES ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ [] t u (lx_tb cx) (lx_ub cx) (lx_live cx) (lx_live cx) _ SIZE_MAXZ
     HPRE Hctx Q10c Q11c (cstr_ok_below W2 mem2 (ms_mem ms3) t _ SBc3 Ht2) (cstr_ok_below W2 mem2 (ms_mem ms3) u _ SBc3 Hu2)
     (Hkt ly2 S2 Hperm2) (Hku ly2 S2 Hperm2) Hlub Htn (fm_glob_below W2 mem2 (ms_mem ms3) _ _ _ _ SBc3 GL2)
     Hlv Hcnt Hnev Hbb)
  (Hinc ly2 S2 Hperm2) Q1c ltac:(lia) eq_refl Q8c ltac:(lia) ltac:(unfold LF_FRAME; lia) (fun a Ha => Ha)).
{ intros ? ? ? ? ? ? (res & _ & Hp & _) x Hx. exact (Permutation_in _ (Permutation_sym Hp) Hx). }
intros ly3 S3 W3 rg3 mem3 md3 HD3 HP3 (res & H10r & Hperm3' & HNR) HCS3.
destruct (names_res_quiet W3 mem3 (lx_tb cx) (lx_ub cx) (lx_live cx) (lx_live cx) _ SIZE_MAXZ res HNR Hq) as [Hres GL3].
subst res.
assert (Hperm3 : Permutation (ablocks B ly3 S3) BL) by exact (Permutation_trans Hperm3' Hperm2).
pose proof (HCS3 t _ (Hkt ly2 S2 Hperm2) (cstr_ok_below W2 mem2 (ms_mem ms3) t _ SBc3 Ht2)) as Ht3.
pose proof (HCS3 u _ (Hku ly2 S2 Hperm2) (cstr_ok_below W2 mem2 (ms_mem ms3) u _ SBc3 Hu2)) as Hu3.
assert (R8c : getr rg3 8 = w64 (lx_un cx)) by (lf5_carry HS3 HP3 8%nat R8b).
assert (R9c : getr rg3 9 = w64 u) by (lf5_carry HS3 HP3 9%nat R9b).
assert (R20c : getr rg3 20 = w64 t) by (lf5_carry HS3 HP3 20%nat R20b).
assert (R18c : getr rg3 18 = w64 (lx_live cx)) by (lf5_carry HS3 HP3 18%nat R18b).
(* ======== 0x80a78: mv s3, a0; jal fuzz_alloc_peak ======== *)
pose proof (fmw_resume_nr W3 rg3 [] mem3 0x80a78) as HS4.
unfold cfg_at. change (w64 0x80a78) with (Z_to_bv 64 0x80a78).
pose proof HD3 as (HJ4 & _). unfold lf_J in HJ4.
aj_run_to fmw_tbl_llvmf_ok HS4 HJ4 A_fuzz_alloc_peak.
{ apply awr_ok_nil. }
lazymatch type of HS4 with context [restrict _ ?m] => rename m into ms4 end.
assert (SB4 : same_below mem3 (ms_mem ms4) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem3 (ms_mem ms4) |- _ => exact (frame_nil_same _ mem3 (ms_mem ms4) H) end).
assert (SBc4 : same_below mem3 (ms_mem ms4) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB4); lia).
pose proof (lf5_run _ _ _ _ _ _ _ _ _ _ _ HD3 HS4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) SB4 HJ4) as HC4.
pose proof (fmw_reg_lit _ _ _ ms4 1%bv 0x80a80 HS4 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1d.
assert (Q8d : getr (ms_regs ms4) 8 = w64 (lx_un cx))
  by (rewrite (fmw_reg_atom _ rg3 [] _ ms4 8%bv 8%bv 8 HS4 ltac:(vm_compute; reflexivity) eq_refl); exact R8c).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ ms4 HS4 eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms4) (Z_to_bv 64 A_fuzz_alloc_peak) (ms_mem ms4) (seg_rom tfibsegs)) ?m)
  with (cfg_at tfibsegs A_fuzz_alloc_peak (ms_regs ms4) (ms_mem ms4) m).
eapply (lf5_call cx ly3 S3 W3 (ms_regs ms4) (ms_mem ms4) _ _ A_fuzz_alloc_peak 0x80a80 STK_fuzz_alloc [] 0 _ _ HB HC4
  (fun HPRE => APEAK ly3 S3 W3 (ms_regs ms4) (ms_mem ms4) _ [] _ _ _ _ HPRE
     (fm_glob_below W3 mem3 (ms_mem ms4) _ _ _ _ SBc4 GL3))
  (Hinc ly3 S3 Hperm3) Q1d ltac:(lia) eq_refl Q8d ltac:(lia) ltac:(unfold LF_FRAME; lia)
  (fun a Ha => False_ind _ (inFP_nil a Ha))).
{ intros ? ? ? ? ? ? (_ & E & _) x Hx. rewrite E. exact Hx. }
intros ly4 S4 W4 rg4 mem4 md4 HD4 HP4 (H10p & Hbl4 & GL4) HCS4.
assert (Hperm4 : Permutation (ablocks B ly4 S4) BL) by (rewrite Hbl4; exact Hperm3).
pose proof (HCS4 t _ (Hkt ly3 S3 Hperm3) (cstr_ok_below W3 mem3 (ms_mem ms4) t _ SBc4 Ht3)) as Ht4.
pose proof (HCS4 u _ (Hku ly3 S3 Hperm3) (cstr_ok_below W3 mem3 (ms_mem ms4) u _ SBc4 Hu3)) as Hu4.
assert (R8d : getr rg4 8 = w64 (lx_un cx)) by (lf5_carry HS4 HP4 8%nat R8c).
assert (R9d : getr rg4 9 = w64 u) by (lf5_carry HS4 HP4 9%nat R9c).
assert (R20d : getr rg4 20 = w64 t) by (lf5_carry HS4 HP4 20%nat R20c).
assert (R18d : getr rg4 18 = w64 (lx_live cx)) by (lf5_carry HS4 HP4 18%nat R18c).
assert (R19d : getr rg4 19 = w64 (ManifestModel.names (lx_tb cx) (lx_ub cx))) by (lf5_carry HS4 HP4 10%nat H10r).
(* ======== 0x80a80: a0 := peak - live; a1 := un; jal check_bounded_alloc ======== *)
pose proof (fmw_resume_nr W4 rg4 [] mem4 0x80a80) as HS5.
unfold cfg_at. change (w64 0x80a80) with (Z_to_bv 64 0x80a80).
pose proof HD4 as (HJ5 & _). unfold lf_J in HJ5.
aj_run_to fmw_tbl_llvmf_ok HS5 HJ5 A_check_bounded_alloc.
{ apply awr_ok_nil. }
lazymatch type of HS5 with context [restrict _ ?m] => rename m into ms5 end.
(* the run computes a0 := a0 - s2 (peak - live) and a1 := s0 (un) *)
assert (SB5 : same_below mem4 (ms_mem ms5) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem4 (ms_mem ms5) |- _ => exact (frame_nil_same _ mem4 (ms_mem ms5) H) end).
assert (SBc5 : same_below mem4 (ms_mem ms5) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB5); lia).
pose proof (lf5_run _ _ _ _ _ _ _ _ _ _ _ HD4 HS5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) SB5 HJ5) as HC5.
pose proof (fmw_reg_lit _ _ _ ms5 1%bv LF_P5 HS5 ltac:(vm_compute; reflexivity) ltac:(unfold LF_P5; lia)) as Q1e.
assert (Q8e : getr (ms_regs ms5) 8 = w64 (lx_un cx))
  by (rewrite (fmw_reg_atom _ rg4 [] _ ms5 8%bv 8%bv 8 HS5 ltac:(vm_compute; reflexivity) eq_refl); exact R8d).
assert (Q11e : getr (ms_regs ms5) 11 = w64 (lx_un cx))
  by (rewrite (fmw_reg_atom _ rg4 [] _ ms5 11%bv 8%bv 8 HS5 ltac:(vm_compute; reflexivity) eq_refl); exact R8d).
pose proof GL4 as (_ & _ & _ & _ & Hlp & Hp33 & _).
assert (Hheld : 0 <= rt_peak (lx_ub cx) (lx_live cx) (lx_live cx) - lx_live cx <= lx_un cx + 3)
  by (unfold rt_peak, lx_un; destruct (lx_ub cx); lia).
assert (Q10e : getr (ms_regs ms5) 10 = w64 (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx) - lx_live cx)).
{ lazymatch type of HS5 with st_ok _ _ ?ss _ => rewrite (st_ok_restrict_reg tfibsegs _ _ ss ms5 10%bv HS5) end.
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
  rewrite denot_lit_U.
  rewrite (lf5_U_sub _ _ _ _ (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx)) (lx_live cx)); [reflexivity | | | | lia].
  - apply (U_atom _ 10 (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx))); [|lia].
    rewrite (ew_Ereg_nat rg4 [] 10 10%bv eq_refl). exact H10p.
  - apply (U_atom _ 18 (lx_live cx)); [|lia].
    rewrite (ew_Ereg_nat rg4 [] 18 18%bv eq_refl). exact R18d.
  - reflexivity. }
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ ms5 HS5 eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms5) (Z_to_bv 64 A_check_bounded_alloc) (ms_mem ms5) (seg_rom tfibsegs)) ?m)
  with (cfg_at tfibsegs A_check_bounded_alloc (ms_regs ms5) (ms_mem ms5) m).
eapply (lf5_call cx ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ _ A_check_bounded_alloc LF_P5 STK_check_bounded_alloc [] 0
  _ _ HB HC5
  (fun HPRE => CBA ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ [] _ (lx_un cx) _ _ _ _ HPRE
     (fm_glob_below W4 mem4 (ms_mem ms5) _ _ _ _ SBc5 GL4) Q10e Q11e Hheld ltac:(lia))
  (Hinc ly4 S4 Hperm4) Q1e ltac:(unfold LF_P5; lia) eq_refl Q8e ltac:(lia) ltac:(unfold LF_FRAME; lia)
  (fun a Ha => False_ind _ (inFP_nil a Ha))).
{ intros ? ? ? ? ? ? (E & _) x Hx. rewrite E. exact Hx. }
intros ly5 S5 W5 rg5 mem5 md5 HD5 HP5 (Hbl5 & GL5) HCS5.
pose proof (HCS5 t _ (Hkt ly4 S4 Hperm4) (cstr_ok_below W4 mem4 (ms_mem ms5) t _ SBc5 Ht4)) as Ht5.
pose proof (HCS5 u _ (Hku ly4 S4 Hperm4) (cstr_ok_below W4 mem4 (ms_mem ms5) u _ SBc5 Hu4)) as Hu5.
eapply (K5 ly5 S5 W5 rg5 mem5 md5 _).
split; [exact HD5|].
split; [unfold EV_names; lia|].
split; [rewrite Hbl5; exact Hperm4|].
split.
{ unfold lf_glob5.
  replace (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 3) with
    (if (length (lx_ub cx) =? 0)%nat then (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 2)
     else (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 2) + 1)
    by (destruct (length (lx_ub cx) =? 0)%nat; lia).
  exact GL5. }
split; [exact Htn|].
split; [exact Hu5|]. split; [exact Ht5|].
split; [lf5_carry HS5 HP5 8%nat R8d|].
split; [lf5_carry HS5 HP5 9%nat R9d|].
split; [lf5_carry HS5 HP5 18%nat R18d|].
split; [lf5_carry HS5 HP5 19%nat R19d|].
lf5_carry HS5 HP5 20%nat R20d.
Qed.
End X.
