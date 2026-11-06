(* lv2_locate_manifest_names 0x81be4 (lv2_locate.c:78-83), 8 instructions:
     addi sp,sp,-16; sd ra,8(sp); sd zero,0(sp); mv a2,sp; jal lv2_locate_manifest_readings; ld ra,8(sp);
     addi sp,sp,16; ret
   names_spec under readings_spec (the callee contract, a Section hypothesis). The walk runs the four stores to the
   call, hands readings its afn_pre at sp - 16 with rp = sp - 16 (the readings counter slot, 0), composes readings'
   journal (window [sp - 16 - STK_readings, sp - 8)) into names' own, and returns through the saved ra at sp - 8,
   which readings' window does not reach. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code table of names (0x81be4, 8 words) ---- *)
Definition nm_tbl : ctable := Eval vm_compute in build_table tfibsegs A_names 8 TEmpty.
Lemma nm_tbl_eq : nm_tbl = build_table tfibsegs A_names 8 TEmpty.
Proof. vm_cast_no_check (eq_refl nm_tbl). Qed.
Lemma nm_tbl_ok : table_ok tfibsegs nm_tbl.
Proof. rewrite nm_tbl_eq. apply build_table_ok0. unfold A_names. lia. Qed.
Lemma nm_tbl_probe : clookup nm_tbl 0x81be4 = Some 0xff010113 /\ clookup nm_tbl 0x81c00 = Some 0x00008067 /\
  clookup nm_tbl 0x81c04 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the return address of the call to readings *)
Definition NM_RA : Z := 0x81bf8.

(* the symbolic states: entry (the 16-byte frame, writable) and after the call (the saved ra at sp + 8, read only;
   atom 32 = names' entry ra) *)
Definition nm_facts : list (nat * afact) := [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)].
Definition ss_nm0 : sstate :=
  mkSS A_names sr_atoms [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 []] None (mkFacts nm_facts [] []).
Definition ss_nm1 : sstate :=
  mkSS NM_RA sr_atoms [YP09.mkRegion (Some 2%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))]] None
    (mkFacts nm_facts [] []).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variables CTX CTXr : list (list Z).
(* names keeps no frame pointer: readings' call context is names' with names' own ra replaced by NM_RA *)
Hypothesis HCTX : forall c, In c CTX -> In (NM_RA :: tl c) CTXr.
Hypothesis READ : readings_spec tfibsegs B CTXr.

Theorem names_holds : names_spec tfibsegs B CTX.
Proof.
intros ly S W regs mem md ch t u tb ub live peak cnt fail HPRE HCX H10 H11 Ct Cu Kt Ku Hub Htb HG Hlv Hcnt Hev Hlb.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (g3_ajsub_img_ok B) as AJSUB.
destruct HPRE as [HAN HROD].
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
assert (FFS : STK_names = 16640) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FEV : EV_names = 2) by reflexivity.
pose proof (ajournal_init tfibsegs B STK_names FM_PSTAT_FP ly S W regs mem md ch HAN) as HJ.
set (E := Ereg regs []).
assert (E1 : ew E 1 = getr regs 1) by exact (ew_Ereg_nat regs [] 1 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs [] 2 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (ew_Ereg_nat regs [] 3 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (ew_Ereg_nat regs [] 4 4%bv eq_refl).
assert (E8 : ew E 8 = getr regs 8) by exact (ew_Ereg_nat regs [] 8 8%bv eq_refl).
assert (E10 : ew E 10 = getr regs 10) by exact (ew_Ereg_nat regs [] 10 10%bv eq_refl).
assert (E11 : ew E 11 = getr regs 11) by exact (ew_Ereg_nat regs [] 11 11%bv eq_refl).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS : st_ok tfibsegs E ss_nm0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_names) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (-16)); [exact Usp | lia | lia |].
    intros a Ha. apply (apresent_writable tfibsegs). apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok nm_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (ew (Ereg regs []) 2) with (getr regs 2). fold (spZ regs). change (2 ^ 4) with 16.
    split; [|exact I]. repeat split; lia. }
assert (HWR : forall a, in_wrange E (ss_mem ss_nm0) a -> spZ regs - 16 <= a < spZ regs).
{ intros a (r & Hin & Hr). cbn [ss_nm0 ss_mem] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp in Hr. lia. }
unfold cfg_at. change (w64 A_names) with (Z_to_bv 64 A_names).
change mem with (ms_mem (mkst regs (Z_to_bv 64 A_names) mem (seg_rom tfibsegs))) in HJ.
(* ---- addi sp,-16; sd ra,8(sp); sd zero,0(sp); mv a2,sp; jal readings ---- *)
aj_run nm_tbl_ok HS HJ.
{ awr_ok_tac. exact Usp. }
remember (with_vm_backing (m_vm_lazy md) mat md) as md1 eqn:Emd1.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (8%bv : bv 5) R8. rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 16).
{ unfold spZ at 1. rewrite R2, Usp. apply unsigned_lit_small. lia. }
assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply (g3_aview_frame E (ss_mem ss_nm0) (w_H W) mem (ms_mem ms) HFr a Ha).
  intros Hw. apply Hn. apply HWR. exact Hw. }
assert (HKL : g3_low_kept W W mem (ms_mem ms)) by (intros a Ha; apply HAV; lia).
(* the two stored words: 0 at sp - 16 (readings' counter), names' ra at sp - 8 *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 0 r HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict] in HR0 end.
pose proof (g3_field_of_region E _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SLit 0) 0 HR0 Usp
  ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hra64. change (bv_modulus 64) with (2 ^ 64) in Hra64.
pose proof (g3_field_of_region E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp
  ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity) ltac:(cbn; unfold raZ; lia)
  ltac:(cbn; lia)) as V1.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V1.
clear HR0.
(* readings' chain: names keeps s0 and writes only below its entry sp *)
assert (Hch1 : achain ly (aview tfibsegs (w_H W) (ms_mem ms)) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) ch).
{ unfold s0Z at 1. rewrite R8, E8. fold (s0Z regs). rewrite Hsp1.
  apply (achain_lower ly _ (spZ regs) (spZ regs - 16)); [|lia].
  apply (achain_kept ly (aview tfibsegs (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply HAV; lia. }
assert (HPRE1 : afn_pre tfibsegs B STK_readings ly S W (ms_regs ms) (ms_mem ms) md1 ch).
{ eapply (afn_pre_at tfibsegs B STK_names (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms) md1 0 (ms_regs ms)
    STK_readings (-16) ch HJ).
  - rewrite Hsp1. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
  - unfold raZ. rewrite R1. rewrite unsigned_lit_small by lia. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact Hch1. }
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 531460) with (w64 A_readings).
change (mkCfg (mkst (ms_regs ms) (w64 A_readings) (ms_mem ms) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs A_readings (ms_regs ms) (ms_mem ms) md1).
(* ---- the call: readings_spec ---- *)
eapply SRr_bind.
{ apply (READ ly S W (ms_regs ms) (ms_mem ms) md1 ch t u (spZ regs - 16) 0 tb ub live peak cnt fail HPRE1).
  - fold (raZ (ms_regs ms)). unfold raZ. rewrite R1. rewrite unsigned_lit_small by lia.
    apply (HCTX (raZ regs :: spine ch) HCX).
  - exact (g3_arodata_kept B W W mem (ms_mem ms) HROD HKL).
  - rewrite R10, E10. exact H10.
  - rewrite R11, E11. exact H11.
  - rewrite R12, Usp. reflexivity.
  - symmetry. exact Hsp1.
  - intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
    apply Hpres1. lia.
  - rewrite Hsp1. lia.
  - replace (spZ regs - 16) with (spZ regs + -16) by lia. exact V0.
  - lia.
  - exact (g3_cstr_ok_kept W W mem (ms_mem ms) t tb Ct HKL).
  - exact (g3_cstr_ok_kept W W mem (ms_mem ms) u ub Cu HKL).
  - exact Kt.
  - exact Ku.
  - exact Hub.
  - exact Htb.
  - exact (g3_fm_glob_kept W W mem (ms_mem ms) live peak cnt fail HG HKL).
  - exact Hlv.
  - exact Hcnt.
  - exact Hev.
  - exact Hlb. }
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HKra & HP2 & H10r & HPerm & HNR & HVrp).
(* names' journal through the call: readings' window ends at its sp + 16 = names' sp *)
pose proof (AJSUB STK_names (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms) md1 0
  (STK_readings + 16) (spZ (ms_regs ms) + 16) FM_PSTAT_FP [] ly2 S2 W2 mem2 md2 EV_names HJ HJ2 ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; right; right; split; [exact Ha | exact (g3_pstat_img a Ha)])) as HJ3.
cbn [app] in HJ3. rewrite Z.add_0_l in HJ3.
(* readings leaves names' saved ra (its sp + 8 .. sp + 16 = names' sp - 8 .. sp) alone *)
assert (V1' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (spZ regs + -8) 8 (raZ regs)).
{ apply (g3_val_mem_kept W W2 (ms_mem ms) mem2); [exact V1|]. intros i Hi. apply HKra. rewrite Hsp1. lia. }
assert (Hsp2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (Usp2 : spZ regs2 = spZ regs - 16) by (unfold spZ; rewrite Hsp2; exact Hsp1).
set (E2' := Ereg regs2 [getr regs 1]).
assert (F2 : ew E2' 2 = getr regs2 2) by exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl).
assert (F10 : ew E2' 10 = getr regs2 10) by exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl).
assert (F32 : ew E2' 32 = getr regs 1) by exact (ew_Ereg_extra regs2 [getr regs 1] 0).
assert (Usp2' : bv_unsigned (ew E2' 2) = spZ regs - 16) by (rewrite F2; exact Usp2).
assert (HS2 : st_ok tfibsegs E2' ss_nm1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 NM_RA) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (ew (Ereg regs2 [getr regs 1]) 2) with (getr regs2 2). fold (spZ regs2). rewrite Usp2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E2' _ (spZ regs - 16) 8 8 (SOff 32 0) (raZ regs)).
    + cbn [sv_denot]. rewrite F32, Z.add_0_r. reflexivity.
    + cbn. unfold raZ. lia.
    + cbn. lia.
    + replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact V1'.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok nm_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (ew (Ereg regs2 [getr regs 1]) 2) with (getr regs2 2). fold (spZ regs2). rewrite Usp2.
    change (2 ^ 4) with 16. split; [|exact I]. repeat split; lia. }
rewrite R1. change (Z_to_bv 64 531448) with (Z_to_bv 64 NM_RA).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 NM_RA) mem2 (seg_rom tfibsegs))) in HJ3.
(* ---- ld ra,8(sp); addi sp,sp,16; (ret) ---- *)
aj_run nm_tbl_ok HS2 HJ3.
{ awr_ok_tac. }
lazymatch goal with H : frame_of E2' (ss_mem ss_nm1) mem2 _ |- _ =>
  pose proof (frame_of_read_only E2' (ss_mem ss_nm1) _ _ eq_refl H) as Hm3 end.
eapply (SRr_ret_at tfibsegs nm_tbl nm_tbl_ok g3_wx W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
intros mat3.
rreg HS2 (1%bv : bv 5) Q1. rreg HS2 (2%bv : bv 5) Q2.
assert (U2a : bv_unsigned (getr regs2 2) = spZ regs - 16) by exact Usp2.
assert (X2 : bv_unsigned (getr (ms_regs ms0) 2) = spZ regs).
{ rewrite Q2. rewrite ?Usp2', ?U2a. rewrite unsigned_lit_small by lia. lia. }
unfold fpost, apost_base.
eexists ly2, S2, (ms_regs ms0), (ms_mem ms0), _.
split.
{ rewrite Q1. rewrite ?F32. rewrite Hra. reflexivity. }
split; [apply (ajournal_materialize tfibsegs B LAWS g3_segs_low); exact HJ3|].
split.
{ apply g3_aregs.
  - intros r Hr.
    pose proof (g3_regs_of_st_ok tfibsegs E2' _ _ regs2 [getr regs 1] G3_KEPT HS2 (env_agree_refl _ _)
      ltac:(vm_compute; reflexivity) r Hr) as K1. cbn [ms_regs restrict] in K1. rewrite K1.
    rewrite (g3_aregs_keep _ _ HP2 r Hr).
    pose proof (g3_regs_of_st_ok tfibsegs E _ _ regs [] G3_KEPT HS (env_agree_refl _ _)
      ltac:(vm_compute; reflexivity) r Hr) as K0. cbn [ms_regs restrict] in K0. exact K0.
  - apply bv_eq. rewrite X2. reflexivity. }
cbv beta. exists res. split.
{ pose proof (g3_regs_of_st_ok tfibsegs E2' _ _ regs2 [getr regs 1] [10%bv] HS2 (env_agree_refl _ _)
    ltac:(vm_compute; reflexivity) 10%bv ltac:(left; reflexivity)) as K1. cbn [ms_regs restrict] in K1.
  rewrite K1. exact H10r. }
split; [exact HPerm|].
rewrite Hm3. exact HNR.
Qed.

End c.
