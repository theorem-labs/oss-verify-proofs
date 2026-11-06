(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Rt/LinkFoWrap.v, with its module paths changed; 2 of its 289 lines of code are new or changed and 2 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): fmemopen's wrapper, walked to musl fmemopen.
   proves function ___interceptor_fmemopen (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates,
   origin/release/pau-projects-recipes / proof-index ___interceptor_fmemopen
   __interceptor_trampoline_fmemopen __wrap_fmemopen __interceptor_fmemopen)

   WHAT THIS FILE PROVES. fo_wrap_ok: afmemopen_w_spec (lib/A/Rt/LinkFoSpec.v), statement unchanged, at the
   wrapper's entry LA_W_FMEMOPEN 0x430a8, from the same statement at musl fmemopen LA_FMEMOPEN 0x96a1c (the Section
   hypothesis RFM). One statement at both entries: the same window AFMW_STK, the same ra (LA_FM_MALLOC_RA), CTX, MT and
   constant window [0x10360, 0x10380). The other hypothesis is the image's own law PcapSyms B (TB, lib/A/AF0m.v); AR's
   laws are closed (lib/Reusable/YG0q.v AR_laws_ok).

   THE CODE (listings link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST), image A):
     0x430a8 `j 0x48024`                                  (link-a/listings/runtime/wrapper_fmemopen.jump.fuzz_link.asan.s:4 (internal record, sha256 fce4b91e4990), word 0x77d0406f)
     0x48024 ___interceptor_fmemopen, 20 instructions     (link-a/listings/runtime/wrapper_fmemopen.fuzz_link.asan.s:4-23 (internal record, sha256 488d0d2c4d21)):
       addi sp,-32; sd ra/s0/s1/s2; mv s0,a2; mv s1,a1; mv s2,a0; jal 0x5b214 TryAsanInitFromRtl;
       auipc a0 + ld t1,0x738(a0) from the cell 0xa3780 (image value 0x96a1c, AMemFile.v link_amf_real_fmemopen);
       mv a0,s2; mv a1,s1; mv a2,s0; ld ra/s0/s1/s2; addi sp,32 (0x4806c); jr t1 (0x48070, a TAIL jump)
     0x5b214 TryAsanInitFromRtl, frame 16 (link-a/tools/adis.py (internal record, sha256 ba8c20cb31c5) 0x5b214, rt_0): lb a1 from 0xab118; a0 = 1; fence; +0x20 0x5b234
       `bne a1,a0` to 0x5b248 (the path that initializes the runtime: lr/sc, then jal 0x5af60); else ld ra/s0, ret.
   The walk is ONE symbolic run (fm_front) from 0x430a8 to 0x96a1c over tbl_icpt (lib/A/AE34.v: the trampoline run
   0x43044 and TryAsanInitFromRtl 0x5b214) plus the 20 words at 0x48024 (tbl_fm; tbl_fm_probe checks words against
   the image). At 0x96a1c sp, ra, gp, tp and s0..s11 are the caller's again (shapeM), a0..a2 are the caller's
   arguments, and only the 48 bytes [sp - 48, sp) were written (32 for the wrapper, 16 for TryAsanInitFromRtl). So
   the frame chain (CTX, ch) passes to musl fmemopen unchanged: the wrapper adds no return address.

   THE INITIALIZING PATH IS PROVED UNREACHABLE. The wrapper has no shadow check and no error call; its one callee's
   one escape is `bne a1,a0` at 0x5b234, taken when the byte 0xab118 (the runtime's "initialized" flag) is not 1.
   The run reads that byte from the AR const law (fm_const, through PcapSyms' Tfib_const: AF0m.v `z1 (ANum 0xab118)
   0x1`) as 1, so the branch is decided not-taken inside the run: escape_operands states the two operands at 0x5b234
   (a1 = 1, a0 = 1), and r_M ends RS_running AT 0x96a1c, which a run through 0x5b248 cannot do (0x5af60 is outside
   tbl_fm, so such a run stops at its first word). The cell 0xa3780 -> 0x96a1c is AF0m.v `z8 (ANum 0xa3780)
   0x96a1c`; fm_const_chk checks both rows against AF0m's table.

   THE PRE AT 0x96a1c (afm_w_pre, LinkFoSpec.v). afn_pre at AFMW_STK: AR at the new memory (al_frame), ra / gp / tp /
   sp kept, the window present, the chain by achain_kept (the run wrote only below sp). afm_w_args: a0..a2 kept; the
   mode word, "rwa\0", the constant window, amf_env and the list head are image addresses below 0x7fff8000, so below
   alloc_ceiling and the stack (LOW). The head law, the spine, the room and universe premises are unchanged.

   THE POST. The run's journal (ajournal_init, ajournal_after_write for [sp - 48, sp)) and musl fmemopen's journal
   compose by YC85G.ajournal_sub_tok (equal windows at the same sp, the footprint [sink_token] on both sides); m_fds and
   m_fs pass through same_but_materialized (fds_fs_of_sbm); every other conjunct is RFM's post. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI16 YCbq YC20 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* 32 bytes of wrapper frame (0x48024) and 16 of TryAsanInitFromRtl's (0x5b214). *)
Definition FM_WIN : Z := 48.

(* tbl_icpt (AE34.v) holds the trampoline run (0x43044, 40 words) and TryAsanInitFromRtl (0x5b214, 40); the
   wrapper's 20 words are added here. *)
Definition fm_ranges : list (Z * nat) := [(LA_I_FMEMOPEN, 20%nat)].
Definition tbl_fm : ctable := Eval vm_compute in build_ranges fm_ranges tbl_icpt.
Lemma tbl_fm_eq : tbl_fm = build_ranges fm_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_fm). Qed.
Lemma tbl_fm_ok : table_ok tfibsegs tbl_fm.
Proof.
rewrite tbl_fm_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold fm_ranges. repeat constructor; cbn; discriminate.
Qed.
(* The words read out of the image (the table is built from tfibsegs): the trampoline's `j`, the wrapper's first
   and last words (`addi sp,sp,-32`, `jr t1`), TryAsanInitFromRtl's first word and its escape test `bne a1,a0`;
   musl fmemopen 0x96a1c and the initializing callee 0x5af60 are NOT in the table. *)
Lemma tbl_fm_probe :
clookup tbl_fm LA_W_FMEMOPEN = Some 0x77d0406f /\ clookup tbl_fm LA_I_FMEMOPEN = Some 0xfe010113 /\
clookup tbl_fm 0x48070 = Some 0x00030067 /\ clookup tbl_fm 0x5b214 = Some 0xff010113 /\
clookup tbl_fm 0x5b234 = Some 0x00a59a63 /\ clookup tbl_fm LA_FMEMOPEN = None /\ clookup tbl_fm 0x5af60 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fm_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_fm FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fm tbl_fm_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* The two runtime cells the run reads, from the AR const law (PcapSyms' Tfib_const, AF0m.v): the "initialized"
   byte 0xab118 = 1 and the REAL(fmemopen) cell 0xa3780 = 0x96a1c. *)
Definition fm_const : list (Z * Z * list (Z * N * Z)) :=
[ (0xab118, 1, [(0, 1%N, 1)]); (0xa3780, 8, [(0, 8%N, LA_FMEMOPEN)]) ].
Lemma fm_const_chk : forall ly, rodata_chk ly fm_const = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Definition stkM : YP09.region := YP09.mkRegion (Some 2%nat) (- FM_WIN) 0 (- FM_WIN) 0 [].
Definition memM : smem := stkM :: map ro_region fm_const.
Definition ssM : sstate := mkSS LA_W_FMEMOPEN sr_atoms memM None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition fm_RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_fm FUEL stop s.
Definition fm_RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition fm_reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (fm_RG ss r) v.
Definition eM : sstate := Eval vm_compute in fst (fm_RUNTO LA_FMEMOPEN ssM).
Lemma r_M : fm_RUNTO LA_FMEMOPEN ssM = (eM, RS_running). Proof. vm_compute. reflexivity. Qed.
(* The escape test, stated on its own: run to 0x5b234 and read the two operands of `bne a1,a0`. *)
Definition eB : sstate := Eval vm_compute in fst (fm_RUNTO 0x5b234 ssM).
Lemma r_B : fm_RUNTO 0x5b234 ssM = (eB, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma escape_operands : ss_pc eB = 0x5b234 /\ fm_RG eB 11 = SLit 1 /\ fm_RG eB 10 = SLit 1.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* At musl fmemopen: ra and a0..a2 are the entry's, every callee-saved register (sp included) is the entry's, the
   stack window is [sp - 48, sp) and every other region is read-only. *)
Definition KEPTM : list Z := [1; 10; 11; 12].
Definition shapeM (ss : sstate) : bool :=
(ss_pc ss =? LA_FMEMOPEN) && match ss_resv ss with None => true | _ => false end &&
forallb (fun r => fm_reg_is ss r (SOff (Z.to_nat r) 0)) KEPTM &&
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - FM_WIN) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
Lemma shapeM_ok : shapeM eM = true. Proof. vm_compute. reflexivity. Qed.

Lemma fm_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
unfold tfibsegs, Asan.M.loaded_segments in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.

Lemma fds_fs_of_sbm : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros md md' H. pose proof (same_but_materialized_frame _ _ H) as (_ & _ & _ & _ & _ & _ & _ & _ & E1 & _ & _ & E2 & _).
split; assumption.
Qed.

Variable B : asyms.
Hypothesis TB : PcapSyms B.

(* The trampoline, the wrapper and TryAsanInitFromRtl, as one run to musl fmemopen. *)
Theorem fm_front : forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + FM_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - FM_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
SRr tfibsegs W (cfg_at tfibsegs LA_W_FMEMOPEN regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs LA_FMEMOPEN regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
(forall r, In r KEPTM -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
aregs_preserved regs regs1 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FM_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - FM_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a)).
Proof.
intros ly S W regs mem md HAR Hal16 Hslo Hshi HpresE.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold FM_WIN in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at at 1. change (w64 LA_W_FMEMOPEN) with (Z_to_bv 64 LA_W_FMEMOPEN).
assert (HS0 : st_ok tfibsegs EE ssM (restrict H (mkst regs (Z_to_bv 64 LA_W_FMEMOPEN) mem (seg_rom tfibsegs)))).
{ unfold ssM. rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memM. apply Forall_cons.
{ unfold stkM, FM_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 48)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. lia. }
exact (AE2y.rodata_ok B TB fm_const ly S H mem EE (fm_const_chk ly) (proj1 HAR)).
- apply pairwise_disjoint_of_extents. unfold memM, stkM, fm_const, ro_region, extent_of_region, FM_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (fm_phase_to W EE LA_FMEMOPEN ssM eM RS_running _ md HS0 r_M)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). apply SRr_ret. split; [reflexivity|].
assert (MEQ1 : forall z : word, ~ (sp0 - 48 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
pose proof (in_wrange_single_b EE memM (bv_unsigned z) 2 (- 48) 0 sp0 ltac:(vm_compute; reflexivity) EE2 Hin). lia. }
clear HF1 HFr1.
pose proof shapeM_ok as Hsh. unfold shapeM in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HCS].
apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eM = None) by (destruct (ss_resv eM); [discriminate | reflexivity]).
destruct (ss_mem eM) as [|r0 rest] eqn:Hmem; [discriminate |].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. unfold FM_WIN in W0b.
assert (RD : forall (r : bv 5) v, fm_reg_is eM (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold fm_reg_is, fm_RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (AF0x.st_ok_reg_denot H EE eM ms1 r HS1). }
assert (RK : forall r, In r KEPTM -> getr (ms_regs ms1) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTM in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK. specialize (HK r Hin). cbn beta in HK.
assert (Hu : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)); [| rewrite Hu; exact HK].
cbn [sv_denot]. rewrite (EEreg (Z.to_nat r) (Z_to_bv 5 r)); [| rewrite Hu; lia].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (AE2y.aregs_preserved_of_st_ok H EE eM ms1 regs [] HS1 (env_agree_refl 32 EE) HCS) as RP1.
set (regs1 := ms_regs ms1) in *.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 Hresv) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape.
rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply AF0x.aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 48 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha.
assert (HN : nth_error (ss_mem eM) 0%nat = Some r0) by (rewrite Hmem; reflexivity).
assert (HB : base_val EE (YP09.r_base r0) + YP09.r_wlo r0 <= a < base_val EE (YP09.r_base r0) + YP09.r_whi r0).
{ rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (HT : AF0x.TFIB_IMG_END <= a < 2 ^ 64) by (unfold AF0x.TFIB_IMG_END, pcap_img_end, IMG_TOP; lia).
exact (AF0x.st_ok_window_apresent H EE eM ms1 0%nat r0 a HS1 HN HB HT). }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 48)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(apply (AF0x.apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ pose proof (same_but_materialized_frame md _ MF1) as MF.
apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 48)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply AE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply MF. + apply MF. + apply MF.
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(lia) ltac:(lia)). }
exists regs1, (ms_mem ms1), md1. split; [reflexivity|]. split; [exact MF1|]. split; [exact HAR1|].
split; [exact RK|]. split; [exact RP1|].
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.

Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis RFM : afmemopen_w_spec link_asink_head tfibsegs B link_amf MT CTX LA_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.

Theorem fo_wrap_ok : afmemopen_w_spec link_asink_head tfibsegs B link_amf MT CTX LA_W_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.
Proof.
intros W ly S regs mem md ch HPRE.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HHL & HFN & HSP & HARGS & Hev & Hlive & HMO & Hu0 & HuC).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HARGS as (G10 & G11 & G12 & GMODE & GRWA & GWIN & GENV & GHEAD).
assert (FS : AFMW_STK = 16432) by reflexivity.
rewrite FS in Hslo, Hpres, Hstk0, Hbot.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
eapply SRr_bind.
{ apply (fm_front ly S W regs mem md HAR Hal16); unfold FM_WIN; [lia | exact Hshi | intros a Ha; apply Hpres; lia]. }
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & RK & RP1 & AV1 & PRS1 & PM1).
unfold FM_WIN in AV1, PRS1.
assert (RK' : forall r (rb : bv 5), In r KEPTM -> Z_to_bv 5 r = rb -> getr regs1 rb = getr regs rb)
  by (intros r rb Hr <-; apply RK; exact Hr).
assert (RP' : forall r (rb : bv 5), acallee_saved r -> Z_to_bv 5 r = rb -> getr regs1 rb = getr regs rb)
  by (intros r rb Hr <-; apply RP1; exact Hr).
assert (R1 : getr regs1 1 = getr regs 1) by (apply (RK' 1); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R10 : getr regs1 10 = getr regs 10) by (apply (RK' 10); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R11 : getr regs1 11 = getr regs 11) by (apply (RK' 11); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R12 : getr regs1 12 = getr regs 12) by (apply (RK' 12); [cbn; tauto | apply bv_eq; reflexivity]).
assert (R2 : getr regs1 2 = getr regs 2) by (apply (RP' 2); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (R3 : getr regs1 3 = getr regs 3) by (apply (RP' 3); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (R4 : getr regs1 4 = getr regs 4) by (apply (RP' 4); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (R8 : getr regs1 8 = getr regs 8) by (apply (RP' 8); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (SP1 : spZ regs1 = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (S01 : s0Z regs1 = s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
(* every byte below the allocator ceiling is the entry's: the run wrote only [sp - 48, sp) *)
assert (LOW : forall a, 0 <= a < alloc_ceiling -> mbyte tfibsegs (mrestrict (w_H W) mem1) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply AE2y.mbyte_of_aview. apply AV1; lia. }
(* so every fact afm_w_args states at an image address (all below 0x7fff8000 = kLowMemEnd) holds at mem1 *)
assert (VMF : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 0x7fff8000 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem1) a n v).
{ intros a n v Ha Hn Hv k Hk. rewrite LOW by lia. exact (Hv k Hk). }
(* the journal of the run: only the 48 bytes below sp changed *)
assert (J00 : ajournal (SK:=link_asink_head) tfibsegs B AFMW_STK (spZ regs) afmemopen_w_fp ly S W mem md [] ly S W mem md 0)
  by (eapply ajournal_init; exact HFN).
assert (J0 : ajournal (SK:=link_asink_head) tfibsegs B AFMW_STK (spZ regs) afmemopen_w_fp ly S W mem md [] ly S W mem1 md1 0).
{ apply (ajournal_after_write tfibsegs B LAWS fm_segs_low AFMW_STK (spZ regs) afmemopen_w_fp ly S W mem md []
    ly S W mem md 0 mem1 md1 (fun a => spZ regs - 48 <= a < spZ regs) S [] J00).
- intros a Ha Hna. exact (AV1 a Ha Hna).
- exact PM1.
- exact MF1.
- intros a Ha. left. left. rewrite FS. lia.
- exact HAR1.
- reflexivity. - reflexivity. - lia. - reflexivity. - exact HQT. }
(* musl fmemopen's precondition at the same sp *)
eapply SRr_mono.
{ apply (RFM W ly S regs1 mem1 md1 ch).
split; [exact HHL|].
split.
{ split; [exact HAR1|]. split; [rewrite R1; exact Hra|]. split; [unfold raZ; rewrite R1; exact Hra4|].
split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
split; [rewrite SP1; exact Hstk|].
split; [rewrite SP1, FS; intros a Ha; apply PM1; apply Hpres; exact Ha|].
split; [|exact HQT].
rewrite SP1, S01. apply (achain_kept ly (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem1) (spZ regs) (s0Z regs) ch (spZ regs) Hch);
  [lia | lia | intros a Ha; apply AV1; lia]. }
split; [exact HSP|].
split.
{ split; [rewrite R10; exact G10|].
split; [rewrite R11; exact G11|].
split; [rewrite R12; exact G12|].
split; [apply VMF; [unfold LA_MODE_W; lia | unfold LA_MODE_W; lia | exact GMODE]|].
split; [apply (garr8_frame tfibsegs (mrestrict (w_H W) mem)); [exact GRWA|];
  intros a Ha; change (Z.of_nat (length rwa_Z)) with 4 in Ha; unfold LA_RWA in Ha; apply LOW; lia|].
(* the constant window [0x10360, 0x10380) *)
split; [intros a Ha; unfold amf_rd; rewrite LOW by lia; exact (GWIN a Ha)|].
split.
{ destruct GENV as (E1 & E2 & E3). unfold amf_env.
split; [|split]; apply VMF; first [assumption | cbv [amf_threaded amf_need_locks amf_ofl_lock link_amf]; lia]. }
apply VMF; [cbv [amf_ofl_head amf_ofl_lock link_amf]; lia | cbv [amf_ofl_head amf_ofl_lock link_amf]; lia | exact GHEAD]. }
split; [exact Hev|].
split; [exact Hlive|].
split; [exact HMO|].
split; [exact Hu0 | exact HuC]. }
cbv beta. intros W' c' _ HP.
destruct HP as (ly' & S' & regs' & mem' & md' & res & -> & J1 & RPF & Q10 & QFR & QMO & QFD & QFS & Q4096 & Q16 & QAB & QK & QDYN & QHEAD & QENV & QWILD).
rewrite SP1 in J1.
destruct (fds_fs_of_sbm md md1 MF1) as [FD1 FS1].
exists ly', S', regs', mem', md', res.
split; [rewrite R1; reflexivity|].
split.
{ exact (ajournal_sub_tok tfibsegs B LAWS fm_segs_low AFMW_STK (spZ regs) afmemopen_w_fp ly S W mem md []
    ly S W mem1 md1 0 AFMW_STK (spZ regs) afmemopen_w_fp [] ly' S' W' mem' md' 1 J0 J1
    ltac:(lia) ltac:(lia) (fun a Ha => or_introl Ha)). }
split; [exact (aregs_preserved_trans _ _ _ RP1 RPF)|].
split; [exact Q10|].
split; [exact QFR|].
split; [exact QMO|].
split; [rewrite QFD; exact FD1|].
split; [rewrite QFS; exact FS1|].
split; [exact Q4096|]. split; [exact Q16|]. split; [exact QAB|].
split; [exact QK|]. split; [exact QDYN|]. split; [exact QHEAD|]. split; [exact QENV | exact QWILD].
Qed.

End b.

About fo_wrap_ok.
Print Assumptions fo_wrap_ok.
