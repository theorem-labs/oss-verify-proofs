(* name_char 0x822c4..0x82338 (lv2_locate.c:36-39) in fm.asan: FMH_Fn.name_char_spec under musl isalnum's contract
   (FMH_Rt.aisalnum_realizes at PC_isalnum, a Section hypothesis). The walk uses the donor's journal engine
   (lib/Reusable/YCbq.v aj_run / SRr_ret_at, lib/Reusable/YA0o.v srr_branch_with) and FMW_g2rt.aj_rt_ro for the call;
   the answer comes from the 256-case check nc_tab of the word the function builds. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the word name_char builds before its branch: six SLTU results or-ed (0x822d8..0x82314), with b = isalnum's
   answer reduced to 0/1 by `snez a0, a0` ---- *)
Definition ncz (c v : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_OR
    (zcanon (zalu_raw 63 64 ALU_OR
      (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon (c + -92)) (zcanon 1)))
      (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon (c + -37)) (zcanon 1)))))
    (zcanon (zalu_raw 63 64 ALU_OR
      (zcanon (zalu_raw 63 64 ALU_OR
        (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon (c + -58)) (zcanon 1)))
        (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon 0) (zcanon (v + 0))))))
      (zcanon (zalu_raw 63 64 ALU_OR
        (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon (c + -95)) (zcanon 1)))
        (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon (c + -45)) (zcanon 1)))))))).

Lemma z256 : forall P : Z -> bool,
  forallb (fun n => P (Z.of_nat n)) (seq 0 256) = true -> forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. specialize (H (Z.to_nat c)).
rewrite Z2Nat.id in H by lia. apply H. apply in_seq. lia.
Qed.

(* ncz depends on v only through `0 <u v` *)
Lemma ncz_v1 : forall c v, 0 < v < 2 ^ 64 -> ncz c v = ncz c 1.
Proof.
intros c v Hv. unfold ncz. do 2 f_equal.
unfold zcanon, M64, zalu_raw. rewrite (Z.mod_small 0) by lia.
rewrite !(Z.mod_small (v + 0)) by lia. rewrite (Z.mod_small (1 + 0)) by lia.
replace (0 <? v + 0) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <? 1 + 0) with true by reflexivity. reflexivity.
Qed.

(* the branch: taken exactly for isalnum or one of '\\' '%' ':' '_' '-' *)
Lemma ncz_tab0 : forall c, 0 <= c < 256 ->
  (negb (ncz c 0 =? 0) = (c =? 92) || (c =? 37) || (c =? 58) || (c =? 95) || (c =? 45))%bool.
Proof.
intros c Hc. apply Bool.eqb_prop.
revert c Hc. apply (z256 (fun c => Bool.eqb (negb (ncz c 0 =? 0))
  ((c =? 92) || (c =? 37) || (c =? 58) || (c =? 95) || (c =? 45))%bool)).
vm_compute. reflexivity.
Qed.
Lemma ncz_tab1 : forall c, 0 <= c < 256 -> negb (ncz c 1 =? 0) = true.
Proof.
intros c Hc. revert c Hc. apply (z256 (fun c => negb (ncz c 1 =? 0))). vm_compute. reflexivity.
Qed.
(* `srli a0, s0, 7` answers name_char when no earlier test fired *)
Lemma nc_high : forall c, 0 <= c < 256 -> ManifestModel.is_alnum c = false ->
  ((c =? 92) || (c =? 37) || (c =? 58) || (c =? 95) || (c =? 45))%bool = false ->
  Z.shiftr c 7 = (if ManifestModel.name_char c then 1 else 0).
Proof.
intros c Hc Ha Hs.
assert (G : forall c, 0 <= c < 256 ->
  implb (negb (ManifestModel.is_alnum c))
    (implb (negb ((c =? 92) || (c =? 37) || (c =? 58) || (c =? 95) || (c =? 45))%bool)
       (Z.shiftr c 7 =? (if ManifestModel.name_char c then 1 else 0))) = true).
{ apply (z256 (fun c => implb (negb (ManifestModel.is_alnum c))
    (implb (negb ((c =? 92) || (c =? 37) || (c =? 58) || (c =? 95) || (c =? 45))%bool)
       (Z.shiftr c 7 =? (if ManifestModel.name_char c then 1 else 0))))). vm_compute. reflexivity. }
specialize (G c Hc). rewrite Ha, Hs in G. cbn [negb implb] in G. apply Z.eqb_eq. exact G.
Qed.
Lemma nc_specials : forall c, ((c =? 92) || (c =? 37) || (c =? 58) || (c =? 95) || (c =? 45))%bool = true ->
  ManifestModel.name_char c = true.
Proof.
intros c H. unfold ManifestModel.name_char.
repeat (apply Bool.orb_prop in H as [H|H]); apply Z.eqb_eq in H; subst c; vm_compute; reflexivity.
Qed.
Lemma nc_alnum : forall c, ManifestModel.is_alnum c = true -> ManifestModel.name_char c = true.
Proof. intros c H. unfold ManifestModel.name_char. rewrite H. reflexivity. Qed.

Definition NC_LEN : nat := 29.
Definition tbl_nc : ctable := Eval vm_compute in build_table tfibsegs A_name_char NC_LEN TEmpty.
Lemma tbl_nc_eq : tbl_nc = build_table tfibsegs A_name_char NC_LEN TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_nc). Qed.
Lemma tbl_nc_ok : table_ok tfibsegs tbl_nc.
Proof. rewrite tbl_nc_eq. apply build_table_ok; [cbv; discriminate | apply table_ok_empty]. Qed.

(* entry: the 16-byte frame below sp (ra, s0) is the only memory the walk names *)
Definition nc_regions : smem := [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 []].
Definition nc_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] [].
Definition ss_nc : sstate := mkSS A_name_char sr_atoms nc_regions None nc_facts.

Ltac ceil := pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR; unfold YG0f.ASAN_CEIL in CR.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.

Theorem name_char_holds : name_char_spec tfibsegs B.
Proof.
unfold name_char_spec, fpre, fpost.
intros ly S W regs mem md ch c live peak cnt fail (HPRE & HRO) Hglob H10 Hc.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (ajournal_init tfibsegs B STK_name_char [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : STK_name_char = 4112) by reflexivity.
ceil.
set (E := Ereg regs []).
assert (E1 : ew E 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (ew_Ereg_nat regs _ 3 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (ew_Ereg_nat regs _ 4 4%bv eq_refl).
assert (E10 : ew E 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros; reflexivity | reflexivity]).
assert (HS : st_ok tfibsegs E ss_nc (restrict (w_H W) (mkst regs (Z_to_bv 64 A_name_char) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_nc, E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold nc_regions. apply Forall_cons; [|apply Forall_nil].
    apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (-16)); [exact Usp | lia | lia |].
    intros a Ha. apply (apresent_writable tfibsegs). apply Hpres. rewrite FFS. lia.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; exact I]. cbn [nc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp. change (2 ^ 4) with 16. repeat split; lia. }
unfold cfg_at. change (w64 A_name_char) with (Z_to_bv 64 A_name_char).
(* 0x822c4..0x822d4: frame, s0 = a0, call isalnum *)
aj_run tbl_nc_ok HS HJ.
{ awr_ok_tac. exact Usp. }
pose proof (gframe_of_frame tfibsegs W E _ 2 (-16) 0 (spZ regs) (spZ regs - STK_name_char) (spZ regs) mem (ms_mem ms)
  HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite FFS; lia) ltac:(lia)) as G1.
clear HF HFr.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -16).
{ unfold spZ at 1. rewrite R2. rewrite ?E2. fold (spZ regs). apply unsigned_lit_small. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (aj_rt_ro tfibsegs B LAWS Hsegs STK_RT_ISALNUM PC_isalnum
    (fun v => v <> 0 <-> ManifestModel.is_alnum c = true)
    W (ms_regs ms) (ms_mem ms) STK_name_char (spZ regs) [] ly S W mem md [] ly S _ 0 (-16) (Z_to_bv 64 0x822d8) HJ).
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold STK_RT_ISALNUM; lia.
  - rewrite FFS; unfold STK_RT_ISALNUM, ESTACK; lia.
  - rewrite R3, ?E3; exact Hgp.
  - rewrite R4, ?E4; exact Htp.
  - exact R1.
  - apply g2_ret_ok_lit; [lia | reflexivity].
  - intros HPK. apply (AISALNUM ly S W (ms_regs ms) (ms_mem ms) _ c HPK); [rewrite R10, ?E10; exact H10 | exact Hc]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Ha0 & Hv & HRv & G2 & Hpres2).
jafter_call_keep HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp. intros a Ha.
    apply (mbyte_of_aview tfibsegs). apply G2; lia.
  - cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite Usp. intros a Ha _.
    apply (apresent_writable tfibsegs).
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _). apply Hpr2. rewrite FFS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E' := havoc E 32 (map (getr regs2) CLOB)) in HS.
assert (HAE' : env_agree 32 (Ereg regs []) E') by (unfold E'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (F1 : ew E' 1 = getr regs 1) by (unfold E'; rewrite YN3v.ew_havoc_old by lia; exact E1).
assert (F2 : bv_unsigned (ew E' 2) = spZ regs) by (unfold E'; rewrite YN3v.ew_havoc_old by lia; exact Usp).
assert (F10 : ew E' 10 = w64 c) by (unfold E'; rewrite YN3v.ew_havoc_old by lia; rewrite E10; exact H10).
assert (F36 : ew E' 36 = w64 v) by (unfold E'; cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB]; exact Ha0).
(* 0x822d8..0x82318: the six tests, then the branch *)
aj_run tbl_nc_ok HS HJ2.
{ awr_ok_tac. exact F2. }
pose proof (gframe_of_frame tfibsegs W E' _ 2 (-16) 0 (spZ regs) (spZ regs - STK_name_char) (spZ regs) mem2 (ms_mem ms0)
  HFr ltac:(vm_compute; reflexivity) F2 ltac:(rewrite FFS; lia) ltac:(lia)) as G3.
clear HF HFr.
srr_branch_with tbl_nc_ok HS.
- (* taken: the answer is 1 *)
  rewrite branch_ne_U, !U_SAlu, !U_SOff, !U_SLit, F10, F36 in Hc0.
  rewrite !unsigned_lit_small in Hc0 by lia.
  change (negb (ncz c v =? zcanon 0) = true) in Hc0.
  assert (HNC : ManifestModel.name_char c = true).
  { destruct (Z.eqb_spec v 0) as [->|Hv0].
    - change (zcanon 0) with 0 in Hc0. rewrite (ncz_tab0 c Hc) in Hc0. exact (nc_specials c Hc0).
    - apply nc_alnum. apply HRv. exact Hv0. }
  aj_run tbl_nc_ok HS HJ2.
  { awr_ok_tac. exact F2. }
  pose proof (gframe_of_frame tfibsegs W E' _ 2 (-16) 0 (spZ regs) (spZ regs - STK_name_char) (spZ regs)
    (ms_mem ms0) (ms_mem ms1) HFr ltac:(vm_compute; reflexivity) F2 ltac:(rewrite FFS; lia) ltac:(lia)) as G4.
  clear HF HFr.
  rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
  eapply (SRr_ret_at tfibsegs tbl_nc tbl_nc_ok Hwx W E' _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matR.
  lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) =>
    exists ly, S, r, m, d end.
  split; [cbn [ms_regs]; rewrite Q1, F1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs B LAWS Hsegs); exact HJ2|].
  split.
  { eapply (aregs_preserved_of_st_ok tfibsegs (w_H W) E' _ _ regs [] HS); [exact HAE' | vm_compute; reflexivity]. }
  split; [cbn [ms_regs]; rewrite Q10, HNC; reflexivity|].
  split; [reflexivity|].
  cbn [ms_mem].
  apply (fm_glob_gframe tfibsegs W (spZ regs - STK_name_char) (spZ regs) mem (ms_mem ms1));
    [| rewrite FFS; lia | exact Hglob].
  apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms0)); [| exact G4].
  apply (gframe_seq tfibsegs W _ _ mem mem2); [| exact G3].
  apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms)); [exact G1 |].
  apply (gframe_widen tfibsegs W _ _ (spZ regs + -16 - STK_RT_ISALNUM) (spZ regs + -16)); [exact G2 | |];
    unfold STK_name_char, STK_RT_ISALNUM, ESTACK; lia.
- (* not taken: the answer is c >> 7 *)
  rewrite branch_ne_U, !U_SAlu, !U_SOff, !U_SLit, F10, F36 in Hc0.
  rewrite !unsigned_lit_small in Hc0 by lia.
  change (negb (ncz c v =? zcanon 0) = false) in Hc0.
  assert (Hv0 : v = 0).
  { destruct (Z.eqb_spec v 0) as [->|Hv0]; [reflexivity|].
    change (zcanon 0) with 0 in Hc0.
    rewrite (ncz_v1 c v ltac:(lia)), (ncz_tab1 c Hc) in Hc0. discriminate Hc0. }
  subst v. change (zcanon 0) with 0 in Hc0. rewrite (ncz_tab0 c Hc) in Hc0.
  assert (Halnum : ManifestModel.is_alnum c = false).
  { destruct (ManifestModel.is_alnum c) eqn:Ea; [|reflexivity]. exfalso. exact (proj2 HRv eq_refl eq_refl). }
  pose proof (nc_high c Hc Halnum Hc0) as HSH.
  aj_run tbl_nc_ok HS HJ2.
  { awr_ok_tac. exact F2. }
  pose proof (gframe_of_frame tfibsegs W E' _ 2 (-16) 0 (spZ regs) (spZ regs - STK_name_char) (spZ regs)
    (ms_mem ms0) (ms_mem ms1) HFr ltac:(vm_compute; reflexivity) F2 ltac:(rewrite FFS; lia) ltac:(lia)) as G4.
  clear HF HFr.
  rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
  eapply (SRr_ret_at tfibsegs tbl_nc tbl_nc_ok Hwx W E' _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matR.
  lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) =>
    exists ly, S, r, m, d end.
  split; [cbn [ms_regs]; rewrite Q1, F1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs B LAWS Hsegs); exact HJ2|].
  split.
  { eapply (aregs_preserved_of_st_ok tfibsegs (w_H W) E' _ _ regs [] HS); [exact HAE' | vm_compute; reflexivity]. }
  split.
  { cbn [ms_regs]. rewrite Q10, F10. unfold w64. rewrite zalu64_sound. f_equal.
    unfold zalu64, zcanon, zalu_raw, M64. rewrite (Z.mod_small c) by lia.
    change (Z.land (7 mod 2 ^ 64) 63) with 7. rewrite <- HSH.
    rewrite Z.mod_small; [reflexivity|]. pose proof (Z.shiftr_nonneg c 7) as [_ Hnn]. split; [lia|].
    apply (Z.le_lt_trans _ c); [rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; lia | lia]. }
  split; [reflexivity|].
  cbn [ms_mem].
  apply (fm_glob_gframe tfibsegs W (spZ regs - STK_name_char) (spZ regs) mem (ms_mem ms1));
    [| rewrite FFS; lia | exact Hglob].
  apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms0)); [| exact G4].
  apply (gframe_seq tfibsegs W _ _ mem mem2); [| exact G3].
  apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms)); [exact G1 |].
  apply (gframe_widen tfibsegs W _ _ (spZ regs + -16 - STK_RT_ISALNUM) (spZ regs + -16)); [exact G2 | |];
    unfold STK_name_char, STK_RT_ISALNUM, ESTACK; lia.
Qed.
End a.
