(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0p YP0n YP0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0h YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL01 YN03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI16 YI00 YI14 YI07 YI19 YI15 UI5b UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UN37.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition FW_DEPTH : Z := 256.
Definition reg_fw_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-FW_DEPTH) 0 (-FW_DEPTH) 0 [].
Definition reg_fw_file (buffered : bool) : YP09.region :=
YP09.mkRegion (Some 13%nat) 0 FILE_HDR 0 FILE_HDR (obj_chunks_gen LAY_FILE 32 (lits_FILE buffered)).
Definition fw_facts (buffered : bool) : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FWRITE_STK) (2^47) 4); (13%nat, mkAF 4096 CEIL_MAX 4);
(10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 0 (2^30) 0); (43%nat, mkAF 4096 CEIL_MAX 0); (47%nat, mkAF 0 (2^31 - 1) 0) ]
++ (if buffered then [ (36%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 4096 CEIL_MAX 0); (39%nat, mkAF 4096 CEIL_MAX 0) ] else []).
Definition ss_fw (buffered : bool) : sstate :=
mkSS ubs0_A_fwrite (sr_set sr_atoms 11%bv (SLit 1)) [ reg_fw_stack; reg_fw_file buffered; reg_got; reg_guard ] None (mkFacts (fw_facts buffered) [] []).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis AX : AllocExtra ubs0_msyms MR.
Theorem ubs0_fwrite : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Proof using AX IMG LAWS.
intros L A regs mem md src n f S bs HPRE Hsp47 H10 H11 H12 H13 Hfin HSA HGs Hn Hsrc0 Hsrc47 Hsrcf Hsrcs HSmax Hn30.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FWRITE_STK = 512) by reflexivity.
assert (HFB : FILE_BLOCK = 1264) by reflexivity. assert (HBO : FILE_BUF_OFF = 240) by reflexivity.
assert (HBS : FILE_BUFSIZ = 1024) by reflexivity. assert (HU : U32M1 = 4294967295) by reflexivity.
assert (HSM : SINK_MAX = 2 ^ 62) by reflexivity. assert (HFH : FILE_HDR = 232) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md f FILE_BLOCK HH Hfin ltac:(lia)) as (Bf0 & Bf1 & Bf16).
destruct HSA as (fd & W & P & -> & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfd & Huniq).
destruct (file_at_obj ubs0_msyms mem f fd P ubs0_sink_code_ok ltac:(lia) ltac:(lia) Hfile) as (Hfdr & Hreg).
destruct (ax_statics AX L A mem md (proj1 HH)) as (Hgot & (g & Hg0 & Hguard) & _).
assert (Hfimg : forall i, 0 <= i < FILE_BLOCK -> ~ in_img ubs0_msyms (f + i)).
{ intros i Hi. pose proof Hfin as Hq. apply blocks_In in Hq as (q & Hq & Hqin). rewrite <- Hq.
exact (il_blocks IMG L A mem md q FILE_BLOCK i (proj1 HH) Hqin Hi). }
assert (HoffR : f + FILE_BLOCK <= 0x10000 \/ 0x10000 + 0x2000 <= f)
by exact (blk_off_img 0x10000 0x2000 f FILE_BLOCK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hfimg).
assert (Hoff : f + FILE_BLOCK <= 0x1f000 \/ 0x52000 <= f).
{ destruct (blk_off_img 0x1f000 0x1000 f FILE_BLOCK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hfimg) as [Hoff1 | Hoff1];
destruct (blk_off_img 0x20000 0x32000 f FILE_BLOCK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hfimg) as [Hoff2 | Hoff2]; lia. }
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Hwr0 : forall E' cs1 cs2 cs3 cs4, ew E' 2 = getr regs 2 -> ew E' 13 = Z_to_bv 64 f ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs1; YP09.mkRegion (Some 13%nat) 0 232 0 232 cs2;
YP09.mkRegion None 128824 128832 0 0 cs3; YP09.mkRegion None 331032 331040 0 0 cs4]
FWRITE_STK (spZ regs) (sink_fp f) (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 cs3 cs4 HE2' HE13'.
eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia |].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 13 f f FILE_BLOCK);
[reflexivity | rewrite HE13'; apply unsigned_lit_small; lia | exact Hfin | cbn; lia | cbn; lia | | ].
{ cbn [r_wlo r_whi]. intros a Ha. exists (f, f + FILE_BLOCK). split; [right; left; reflexivity | cbn; lia]. }
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HfrK : forall E' cs1 cs2 cs3 cs4 (m m' : word -> option byte), ew E' 2 = getr regs 2 -> ew E' 13 = Z_to_bv 64 f ->
frame_of E' [YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs1; YP09.mkRegion (Some 13%nat) 0 232 0 232 cs2;
YP09.mkRegion None 128824 128832 0 0 cs3; YP09.mkRegion None 331032 331040 0 0 cs4] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E' cs1 cs2 cs3 cs4 m m' HE2' HE13' HF' a Ha Hns Hnf. unfold mbyte. rewrite (HF' (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [r_base r_wlo r_whi base_val] in Hr; rewrite ?HE2', ?HE13', ?Hspw, ?unsigned_lit_small in Hr by lia; lia. }
assert (Henvk : forall a, env_addr a -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 256 <= a < spZ regs) /\ ~ (f <= a < f + FILE_BLOCK)).
{ intros a Ha. unfold env_addr in Ha.
change sk_ofl_head with 0x51168 in Ha. change sk_threaded with (0x50d38 + 1) in Ha.
change sk_path_addr with 0x10304 in Ha. change sk_mode_addr with 0x102a2 in Ha. change sk_trailer_addr with 0x10311 in Ha. change sk_ofl_lock with 0x51160 in Ha.
change sk_rwa_addr with 0x10390 in Ha. change sk_highs_addr with 0x103b8 in Ha. change sk_ones_addr with 0x103c8 in Ha. lia. }
assert (Htok : sink_open_fp (sink_fp f)) by (apply sink_open_token; left; reflexivity).
destruct Hreg as [(-> & Hobj) | (Hobj & HGP & HLP)].
2:{
set (p := Z.of_nat (length P)) in *.
assert (Hp0 : 0 <= p) by (subst p; lia).
remember (file_vals f fd (f + FILE_BUF_OFF + FILE_BUFSIZ) (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF) U32M1) as vals eqn:Hvals.
remember (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) E0) by (rewrite HE0; apply env_agree_refl).
assert (HEv : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 src) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE12 : ew E0 12 = Z_to_bv 64 n) by (subst E0; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE13 : ew E0 13 = Z_to_bv 64 f) by (subst E0; rewrite (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact H13).
assert (HE36 : ew E0 36 = Z_to_bv 64 (f + FILE_BUF_OFF + FILE_BUFSIZ)) by (apply (HEv 4%nat); rewrite Hvals; reflexivity).
assert (HE37 : ew E0 37 = Z_to_bv 64 (f + FILE_BUF_OFF + p)) by (apply (HEv 5%nat); rewrite Hvals; reflexivity).
assert (HE39 : ew E0 39 = Z_to_bv 64 (f + FILE_BUF_OFF)) by (apply (HEv 7%nat); rewrite Hvals; reflexivity).
assert (HE43 : ew E0 43 = Z_to_bv 64 (f + FILE_BUF_OFF)) by (apply (HEv 11%nat); rewrite Hvals; reflexivity).
assert (HE47 : ew E0 47 = Z_to_bv 64 fd) by (apply (HEv 15%nat); rewrite Hvals; reflexivity).
assert (HE63 : ew E0 63 = Z_to_bv 64 g).
{ subst E0. rewrite (ew_Ereg_extra regs _ 31). rewrite Hvals. reflexivity. }
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_fwrite) mem (seg_rom ubs0segs)).
pose proof (journal_init ubs0_msyms MR FWRITE_STK (sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (HS : st_ok ubs0segs E0 (ss_fw true) ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- apply regs_ok_pin; [rewrite HE0; apply regs_ok_Ereg | reflexivity | exact H11].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| unfold FW_DEPTH; lia | lia | intros a Ha; apply Hstw; unfold FW_DEPTH in Ha; lia].
rewrite HE2. exact Hspw.
+ eapply (region_ok_obj_gen ubs0segs E0 mem 13 f FILE_HDR 0 FILE_HDR LAY_FILE vals 32 (lits_FILE true));
[ rewrite HE13; apply unsigned_lit_small; lia | lia | lia | exact Hobj | reflexivity | exact HEv | | ].
* intros j z Hj. rewrite Hvals.
do 31 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
* intros i Hi. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f FILE_BLOCK i HH Hfin ltac:(lia))).
+ unfold region_ok, reg_got. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_got_stack_chk_guard 8 (SLit ubs0_D_stack_chk_guard) ubs0_D_stack_chk_guard);
[reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hgot.
+ unfold region_ok, reg_guard. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_stack_chk_guard 8 (SOff 63%nat 0) g);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE63 | change (8 * Z.of_N 8) with 64; exact Hg0 | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hguard.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, reg_fw_stack, reg_fw_file, reg_got, reg_guard.
cbn [r_base r_lo r_hi base_val]. rewrite HE2, HE13, Hspw, !unsigned_lit_small by lia.
change ubs0_D_got_stack_chk_guard with 128824. change ubs0_D_stack_chk_guard with 331032. unfold FW_DEPTH.
repeat split; lia.
- split; [|split; [exact I|exact I]].
cbn [f_atoms atoms_ok fw_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE12, HE13, HE36, HE37, HE39, HE43, HE47, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
-
rewrite branch_geu_U in Hc. rewrite U_sub_form in Hc; rewrite ?(U_atom _ 36 _ HE36), ?(U_atom _ 37 _ HE37), ?(U_atom _ 12 _ HE12) in * by lia; [|lia].
assert (Hroom : n <= FILE_BUFSIZ - p) by (destruct (Z.ltb_spec (f + FILE_BUF_OFF + FILE_BUFSIZ - (f + FILE_BUF_OFF + p)) n); [discriminate Hc | lia]).
clear Hc.
pose proof (HfrK _ _ _ _ _ _ _ HE2 HE13 HF) as Hk1. unfold ms0 in Hk1. cbn [ms_mem mkst] in Hk1.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (Hk2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem a).
{ intros a Ha1 Ha2 Ha3. rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HF0 a Ha1 Ha2 Ha3). exact (Hk1 a Ha1 Ha2 Ha3). }
jreg HS (10%bv:reg) as Ha0. jreg HS (11%bv:reg) as Ha1. jreg HS (12%bv:reg) as Ha2. jreg HS (1%bv:reg) as Hra'.
rewrite HE37 in Ha0. rewrite HE10 in Ha1. rewrite HE12 in Ha2.
assert (HGs1 : garr8 ubs0segs (ms_mem ms1) src bs).
{ eapply garr8_frame; [exact HGs|]. intros a Ha. apply Hk2; lia. }
eapply SR_bind.
{ eapply (jmemcpy_rd ubs0_msyms MR LAWS IMG ubs0_A_memcpy ubs0_memcpy) with (n := n) (bs := bytes bs);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra'
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | | | | ].
- intros i Hi. replace (f + FILE_BUF_OFF + p + i) with (f + (FILE_BUF_OFF + p + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f FILE_BLOCK (FILE_BUF_OFF + p + i) (proj1 HJ) Hfin ltac:(lia))).
- rewrite bytes_length. apply (rdn_of_garr8 ubs0_msyms). exact HGs1.
- rewrite bytes_length. exact Hn.
- lia.
- intros a Ha. right. left. split; [exists (f, f + FILE_BLOCK); split; [right; left; reflexivity | cbn; lia]|].
exists f, FILE_BLOCK. split; [exact Hfin | lia]. }
intros c' (regsM & memM & -> & HJM & _ & HfrM & HoutM & HgrM & HcpM).
jafter_stretch HS 64%nat regsM memM (10%bv :: MEMCPY_CLOB) 0x18ce8 HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [intros rr Hrr; apply HfrM; exact (reg_in_cons_false _ _ _ Hrr)|];
assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_outside _ _ _ _ _ (f + FILE_BUF_OFF + p) n HoutM HgrM); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw; lia.
- eapply (region_kept_outside _ _ _ _ _ (f + FILE_BUF_OFF + p) n HoutM HgrM); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE13, ?unsigned_lit_small by lia; lia.
- apply (region_kept_abs_ro ubs0segs _ _ _ _ _ _ (f + FILE_BUF_OFF + p) n HoutM); lia.
- apply (region_kept_abs_ro ubs0segs _ _ _ _ _ _ (f + FILE_BUF_OFF + p) n HoutM); lia. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJM.
{ wr_norm. apply Hwr0; ew_havoc; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_eq_U, U_mul1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJM.
{ wr_norm. apply Hwr0; ew_havoc; [exact HE2 | exact HE13]. }
assert (HE2h : forall ws, ew (havoc E0 64 ws) 2 = getr regs 2) by (intros; ew_havoc; exact HE2).
assert (HE13h : forall ws, ew (havoc E0 64 ws) 13 = Z_to_bv 64 f) by (intros; ew_havoc; exact HE13).
assert (Hk3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) ->
~ (f + FILE_BUF_OFF + p <= a < f + FILE_BUF_OFF + p + n) -> mbyte ubs0segs (ms_mem ms3) a = mbyte ubs0segs mem a).
{ intros a A1 A2 A3 A4. rewrite (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF2 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF1 a A1 A2 A3).
cbn [ms_mem mkst]. unfold mbyte. rewrite (HoutM (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). exact (Hk2 a A1 A2 A3). }
assert (HA64 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) (havoc E0 64 (map (getr regsM) (10%bv :: MEMCPY_CLOB))))
by (eapply (env_agree_havoc_ge 32); [lia | exact HA0]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA64 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(right; left; reflexivity)) as (_ & _ & _ & Hcs).
cbn [r_base r_chunks base_val] in Hcs. rewrite HE13h, unsigned_lit_small in Hcs by lia.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJM)) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms3), (ms_mem ms3), md.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJM|]. split; [exact HPR|].
split; [rewrite Hr10; exact HE12|].
exists fd, W, (P ++ bs).
split; [symmetry; apply app_assoc|].
split; [apply Forall_app; split; [exact Hok | exact (garr8_bytes_ok _ _ _ _ HGs)]|].
split; [rewrite (length_app (W ++ P) bs), Nat2Z.inj_add; lia|].
split.
{ apply (stdio_env_frame ubs0_msyms mem (ms_mem ms3)); [|exact Henv]. intros a Ha. destruct (Henvk a Ha) as (K1 & K2 & K3). apply Hk3; lia. }
split.
{ apply (obj_file_at_buf ubs0_msyms (ms_mem ms3) f fd (P ++ bs) Hfdr).
- apply (obj_at_of_chunks_sv ubs0segs _ _ _ _ LAY_FILE _ Hcs eq_refl).
rewrite length_app, Nat2Z.inj_add. fold p. rewrite <- Hn.
unfold file_vals, LAY_FILE.
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_atom HE36|].
constructor; [cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; lia | eexists; split; [fld_in |
match goal with |- bv_unsigned (sv_denot ?E ?e) mod _ = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff; ew_havoc; rewrite HE12, HE37, !unsigned_lit_small by lia;
rewrite !Z.add_0_r; unfold zcanon, M64; change (8 * Z.of_N 8) with 64;
rewrite (Z.mod_small n), (Z.mod_small (f + FILE_BUF_OFF + p)) by lia; rewrite Z.mod_mod by lia; rewrite Z.mod_small by lia; lia]] |].
constructor; [fld_lit|]. constructor; [fld_atom HE39|].
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_atom HE43|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_atom HE47|].
do 15 (constructor; [fld_lit|]). constructor.
- apply garr8_app. split.
+ eapply garr8_frame; [exact HGP|]. intros a Ha. apply Hk3; lia.
+ fold p. apply (garr8_copy ubs0segs (ms_mem ms1) (ms_mem ms3) src (f + FILE_BUF_OFF + p) bs HGs1).
intros i Hi.
rewrite (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF2 (f + FILE_BUF_OFF + p + i)) by lia.
rewrite (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF1 (f + FILE_BUF_OFF + p + i)) by lia.
exact (HcpM i ltac:(lia)).
- rewrite length_app, Nat2Z.inj_add. fold p. lia. }
split.
{ apply (val_mem_word_mem ubs0segs). apply (val_mem_word_mem ubs0segs) in Hhead.
eapply (val_mem_frame ubs0_msyms); [|exact Hhead]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
assert (Hex : env_addr x) by (left; lia). destruct (Henvk x Hex) as (K1 & K2 & K3). apply Hk3; lia. }
split; [exact Hf0|]. split; [exact Hfs|]. split; [exact Hfd | exact Huniq].
-
rewrite branch_geu_U in Hc. rewrite U_sub_form in Hc; rewrite ?(U_atom _ 36 _ HE36), ?(U_atom _ 37 _ HE37), ?(U_atom _ 12 _ HE12) in * by lia; [|lia].
assert (Hbig : FILE_BUFSIZ - p < n) by (destruct (Z.ltb_spec (f + FILE_BUF_OFF + FILE_BUFSIZ - (f + FILE_BUF_OFF + p)) n); [lia | discriminate Hc]).
clear Hc.
pose proof (HfrK _ _ _ _ _ _ _ HE2 HE13 HF) as Hk1. unfold ms0 in Hk1. cbn [ms_mem mkst] in Hk1.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (Hk2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem a).
{ intros a Ha1 Ha2 Ha3. rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HF0 a Ha1 Ha2 Ha3). exact (Hk1 a Ha1 Ha2 Ha3). }
jbranch ubs0tbl HS.
+
rewrite branch_eq_U, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) in Hc by lia.
assert (Hp : p = 0) by (destruct (Z.eqb_spec (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF)); [lia | discriminate Hc]).
clear Hc.
jrun_ecall LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
sym_ecall_open HS.
assert (HP0 : P = []) by (destruct P; [reflexivity | subst p; cbn [length] in Hp; lia]).
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ =>
change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ;
assert (Hk3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs m a = mbyte ubs0segs mem a)
by (intros a A1 A2 A3; rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HFx a A1 A2 A3); exact (Hk2 a A1 A2 A3)) end.
match type of Hmem with mem_ok _ _ _ ?rs =>
let r := eval vm_compute in (iov_read1 rs (Some 2%nat) (-152)) in
match r with Some (?vb, ?vl) =>
destruct (iov_read1_sound ubs0segs E0 mem0 rs (Some 2%nat) (-152) vb vl Hmem ltac:(vm_compute; reflexivity)) as [M0 L0] end end.
cbn [base_val sv_denot] in M0, L0. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, HE2, Hspw in M0, L0. rewrite HE10 in M0. rewrite HE12, Hn in L0.
assert (HGs0 : garr8 ubs0segs mem0 src bs) by (eapply garr8_frame; [exact HGs|]; intros a Ha; apply Hk3; lia).
apply (J_writev_node1 ubs0_msyms MR LAWS regs0 _ mem0 _ _ _ _ _ _ _ _ _ _ _ fd W (spZ regs + -152) src bs HJ Htok (conj Hfs (conj Hfd Huniq)) Hfdr).
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
{ rewrite (Hregs 12%bv). eval_sr_get. rewrite denot_lit_U, U_iovcnt, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) by lia.
rewrite Hp, Z.add_0_r, Z.eqb_refl. reflexivity. }
{ rewrite (Hregs 11%bv). eval_sr_get. cbn [sv_denot]. rewrite HE2, Hspw. reflexivity. }
{ lia. } { lia. }
{ exact M0. }
{ exact L0. }
{ exact HGs0. } { lia. } { lia. } { change MAX_RW_COUNT with 2147479552. lia. }
{ rewrite HP0, app_nil_r in HSmax. lia. }
intros md' HJ' Hos'. cbn [ss_pc].
resume_reg_sr ubs0segs (22%bv : reg).
{ rewrite denot_lit_U. f_equal.
rewrite U_sub_form_gen; [| reflexivity | rewrite U_add2; rewrite ?(U_atom _ 12 _ HE12), ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia].
rewrite U_add2; rewrite ?(U_atom _ 12 _ HE12), ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia. }
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (HUrem : U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 12 0) (SOff 37 0)) (SMd M_MUL (SOff 39 0) (SLit 18446744073709551615))) = n + p).
{ rewrite U_sub_form_gen; [| reflexivity | rewrite U_add2; rewrite ?(U_atom _ 12 _ HE12), ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia].
rewrite U_add2; rewrite ?(U_atom _ 12 _ HE12), ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_ltu_U, HUrem, U_lit in Hc by lia. destruct (Z.ltb_spec (n + p) 18446744073709547521); [discriminate Hc | lia]. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_eq_U, U_mul1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (Hk6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs (ms_mem ms4) a = mbyte ubs0segs mem a).
{ intros a A1 A2 A3. rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HF4 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ HE2 HE13 HF3 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ HE2 HE13 HF2 a A1 A2 A3).
cbn [ms_mem mkst]. exact (Hk3 a A1 A2 A3). }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(right; left; reflexivity)) as (_ & _ & _ & Hcs).
cbn [r_base r_chunks base_val] in Hcs. rewrite HE13, unsigned_lit_small in Hcs by lia.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms4), (ms_mem ms4), md'.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPR|].
split; [rewrite Hr10; exact HE12|].
destruct Hos' as (Hfs' & Hfd' & Huniq').
exists fd, (W ++ bs), [].
split; [rewrite HP0, !app_nil_r; reflexivity|].
split; [apply Forall_app; split; [exact Hok | exact (garr8_bytes_ok _ _ _ _ HGs)]|].
split; [rewrite (length_app (W ++ P) bs), Nat2Z.inj_add; lia|].
split.
{ apply (stdio_env_frame ubs0_msyms mem (ms_mem ms4)); [|exact Henv]. intros a Ha. destruct (Henvk a Ha) as (K1 & K2 & K3). apply Hk6; lia. }
split.
{ apply (obj_file_at_buf ubs0_msyms (ms_mem ms4) f fd [] Hfdr).
- apply (obj_at_of_chunks_sv ubs0segs _ _ _ _ LAY_FILE _ Hcs eq_refl).
cbn [length Z.of_nat]. unfold file_vals, LAY_FILE.
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE47|].
do 15 (constructor; [fld_lit|]). constructor.
- apply garr8_nil.
- cbn. lia. }
split.
{ apply (val_mem_word_mem ubs0segs). apply (val_mem_word_mem ubs0segs) in Hhead.
eapply (val_mem_frame ubs0_msyms); [|exact Hhead]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
assert (Hex : env_addr x) by (left; lia). destruct (Henvk x Hex) as (K1 & K2 & K3). apply Hk6; lia. }
split; [exact Hf0|]. split; [exact Hfs'|]. split; [exact Hfd' | exact Huniq'].
+
rewrite branch_eq_U, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) in Hc by lia.
assert (Hp : p <> 0) by (destruct (Z.eqb_spec (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF)); [discriminate Hc | lia]).
clear Hc.
jrun_ecall LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ =>
change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ;
assert (Hk3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs m a = mbyte ubs0segs mem a)
by (intros a A1 A2 A3; rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HFx a A1 A2 A3); exact (Hk2 a A1 A2 A3)) end.
match type of Hmem with mem_ok _ _ _ ?rs =>
let r := eval vm_compute in (iov_read1 rs (Some 2%nat) (-168)) in
match r with Some (?vb, ?vl) =>
destruct (iov_read1_sound ubs0segs E0 mem0 rs (Some 2%nat) (-168) vb vl Hmem ltac:(vm_compute; reflexivity)) as [M0 L0] end;
let r := eval vm_compute in (iov_read1 rs (Some 2%nat) (-152)) in
match r with Some (?vb, ?vl) =>
destruct (iov_read1_sound ubs0segs E0 mem0 rs (Some 2%nat) (-152) vb vl Hmem ltac:(vm_compute; reflexivity)) as [M1 L1] end end.
rewrite (denot_lit_U E0 (SAlu _ _ _)), U_sub_form in L0; rewrite ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) in * by lia; [|lia].
replace (f + FILE_BUF_OFF + p - (f + FILE_BUF_OFF)) with p in L0 by lia.
cbn [base_val sv_denot] in M0, L0, M1, L1.
rewrite HE2, Hspw, Z.add_0_r, Z_to_bv_bv_unsigned, HE39 in M0. rewrite HE2, Hspw in L0.
rewrite HE2, Hspw, Z.add_0_r, Z_to_bv_bv_unsigned, HE10 in M1. rewrite HE2, Hspw, Z.add_0_r, Z_to_bv_bv_unsigned, HE12, Hn in L1.
assert (HGs0 : garr8 ubs0segs mem0 src bs) by (eapply garr8_frame; [exact HGs|]; intros a Ha; apply Hk3; lia).
assert (HGP0 : garr8 ubs0segs mem0 (f + FILE_BUF_OFF) P) by (eapply garr8_frame; [exact HGP|]; intros a Ha; apply Hk3; lia).
apply (J_writev_node2 ubs0_msyms MR LAWS regs0 _ mem0 _ _ _ _ _ _ _ _ _ _ _ fd W (spZ regs + -168) (f + FILE_BUF_OFF) src P bs HJ Htok (conj Hfs (conj Hfd Huniq)) Hfdr).
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
{ rewrite (Hregs 12%bv). eval_sr_get. rewrite denot_lit_U, U_iovcnt, (U_atom _ 37 _ HE37), (U_atom _ 39 _ HE39) by lia.
destruct (Z.eqb_spec (f + FILE_BUF_OFF + p) (f + FILE_BUF_OFF)); [lia | reflexivity]. }
{ rewrite (Hregs 11%bv). eval_sr_get. cbn [sv_denot]. rewrite HE2, Hspw. reflexivity. }
{ lia. } { lia. }
{ exact M0. } { exact L0. }
{ replace (spZ regs + -168 + 16) with (spZ regs + -152) by lia. exact M1. }
{ replace (spZ regs + -168 + 24) with (spZ regs + -152 + 8) by lia. exact L1. }
{ exact HGP0. } { exact HGs0. } { lia. } { fold p. lia. } { lia. } { lia. }
{ fold p. change MAX_RW_COUNT with 2147479552. lia. }
{ fold p. rewrite length_app, Nat2Z.inj_add in HSmax. fold p in HSmax. lia. }
intros md' HJ' Hos'. cbn [ss_pc].
assert (HUrem : U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 12 0) (SOff 37 0)) (SMd M_MUL (SOff 39 0) (SLit 18446744073709551615))) = n + p).
{ rewrite U_sub_form_gen; [| reflexivity | rewrite U_add2; rewrite ?(U_atom _ 12 _ HE12), ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia].
rewrite U_add2; rewrite ?(U_atom _ 12 _ HE12), ?(U_atom _ 37 _ HE37), ?(U_atom _ 39 _ HE39) by lia; lia. }
resume_reg_sr ubs0segs (22%bv : reg).
{ rewrite denot_lit_U, HUrem. f_equal. fold p. lia. }
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_ltu_U, HUrem, U_lit in Hc by lia. destruct (Z.ltb_spec (n + p) 18446744073709547521); [discriminate Hc | lia]. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_eq_U, U_mul1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (Hk6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs (ms_mem ms4) a = mbyte ubs0segs mem a).
{ intros a A1 A2 A3. rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HF4 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ HE2 HE13 HF3 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ HE2 HE13 HF2 a A1 A2 A3).
cbn [ms_mem mkst]. exact (Hk3 a A1 A2 A3). }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(right; left; reflexivity)) as (_ & _ & _ & Hcs).
cbn [r_base r_chunks base_val] in Hcs. rewrite HE13, unsigned_lit_small in Hcs by lia.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms4), (ms_mem ms4), md'.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPR|].
split; [rewrite Hr10; exact HE12|].
destruct Hos' as (Hfs' & Hfd' & Huniq').
exists fd, (W ++ P ++ bs), [].
split; [rewrite app_nil_r, <- app_assoc; reflexivity|].
split; [apply Forall_app; split; [exact Hok | exact (garr8_bytes_ok _ _ _ _ HGs)]|].
split; [rewrite (length_app (W ++ P) bs), Nat2Z.inj_add; lia|].
split.
{ apply (stdio_env_frame ubs0_msyms mem (ms_mem ms4)); [|exact Henv]. intros a Ha. destruct (Henvk a Ha) as (K1 & K2 & K3). apply Hk6; lia. }
split.
{ apply (obj_file_at_buf ubs0_msyms (ms_mem ms4) f fd [] Hfdr).
- apply (obj_at_of_chunks_sv ubs0segs _ _ _ _ LAY_FILE _ Hcs eq_refl).
cbn [length Z.of_nat]. unfold file_vals, LAY_FILE.
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE47|].
do 15 (constructor; [fld_lit|]). constructor.
- apply garr8_nil.
- cbn. lia. }
split.
{ apply (val_mem_word_mem ubs0segs). apply (val_mem_word_mem ubs0segs) in Hhead.
eapply (val_mem_frame ubs0_msyms); [|exact Hhead]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
assert (Hex : env_addr x) by (left; lia). destruct (Henvk x Hex) as (K1 & K2 & K3). apply Hk6; lia. }
split; [exact Hf0|]. split; [exact Hfs'|]. split; [exact Hfd' | exact Huniq'].
}
remember (file_vals f fd 0 0 0 0) as vals eqn:Hvals.
remember (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) E0) by (rewrite HE0; apply env_agree_refl).
assert (HEv : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 src) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE12 : ew E0 12 = Z_to_bv 64 n) by (subst E0; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE13 : ew E0 13 = Z_to_bv 64 f) by (subst E0; rewrite (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact H13).
assert (HE43 : ew E0 43 = Z_to_bv 64 (f + FILE_BUF_OFF)) by (apply (HEv 11%nat); rewrite Hvals; reflexivity).
assert (HE47 : ew E0 47 = Z_to_bv 64 fd) by (apply (HEv 15%nat); rewrite Hvals; reflexivity).
assert (HE63 : ew E0 63 = Z_to_bv 64 g).
{ subst E0. rewrite (ew_Ereg_extra regs _ 31). rewrite Hvals. reflexivity. }
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_fwrite) mem (seg_rom ubs0segs)).
pose proof (journal_init ubs0_msyms MR FWRITE_STK (sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (HS : st_ok ubs0segs E0 (ss_fw false) ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- apply regs_ok_pin; [rewrite HE0; apply regs_ok_Ereg | reflexivity | exact H11].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| unfold FW_DEPTH; lia | lia | intros a Ha; apply Hstw; unfold FW_DEPTH in Ha; lia].
rewrite HE2. exact Hspw.
+ eapply (region_ok_obj_gen ubs0segs E0 mem 13 f FILE_HDR 0 FILE_HDR LAY_FILE vals 32 (lits_FILE false));
[ rewrite HE13; apply unsigned_lit_small; lia | lia | lia | exact Hobj | reflexivity | exact HEv | | ].
* intros j z Hj. rewrite Hvals.
do 31 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
* intros i Hi. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f FILE_BLOCK i HH Hfin ltac:(lia))).
+ unfold region_ok, reg_got. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_got_stack_chk_guard 8 (SLit ubs0_D_stack_chk_guard) ubs0_D_stack_chk_guard);
[reflexivity | vm_compute; split; congruence | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hgot.
+ unfold region_ok, reg_guard. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply (chunk_ok_val ubs0segs E0 mem 0 ubs0_D_stack_chk_guard 8 (SOff 63%nat 0) g);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE63 | change (8 * Z.of_N 8) with 64; exact Hg0 | vm_compute; congruence | ].
apply (val_mem_word_mem ubs0segs). exact Hguard.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, reg_fw_stack, reg_fw_file, reg_got, reg_guard.
cbn [r_base r_lo r_hi base_val]. rewrite HE2, HE13, Hspw, !unsigned_lit_small by lia.
change ubs0_D_got_stack_chk_guard with 128824. change ubs0_D_stack_chk_guard with 331032. unfold FW_DEPTH.
repeat split; lia.
- split; [|split; [exact I|exact I]].
cbn [f_atoms atoms_ok fw_facts app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE12, HE13, HE43, HE47, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
pose proof (HfrK _ _ _ _ _ _ _ HE2 HE13 HF) as Hk1. unfold ms0 in Hk1. cbn [ms_mem mkst] in Hk1.
jbranch ubs0tbl HS.
-
rewrite branch_geu_U, U_lit, (U_atom _ 12 _ HE12) in Hc by lia.
assert (Hroom : n <= FILE_BUFSIZ) by (destruct (Z.ltb_spec 1024 n); [discriminate Hc | lia]).
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (Hk2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem a).
{ intros a Ha1 Ha2 Ha3. rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HF0 a Ha1 Ha2 Ha3). exact (Hk1 a Ha1 Ha2 Ha3). }
jreg HS (10%bv:reg) as Ha0. jreg HS (11%bv:reg) as Ha1. jreg HS (12%bv:reg) as Ha2. jreg HS (1%bv:reg) as Hra'.
rewrite HE43 in Ha0. rewrite HE10 in Ha1. rewrite HE12 in Ha2.
assert (HGs1 : garr8 ubs0segs (ms_mem ms1) src bs).
{ eapply garr8_frame; [exact HGs|]. intros a Ha. apply Hk2; lia. }
eapply SR_bind.
{ eapply (jmemcpy_rd ubs0_msyms MR LAWS IMG ubs0_A_memcpy ubs0_memcpy) with (n := n) (bs := bytes bs);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra'
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | | | | ].
- intros i Hi. replace (f + FILE_BUF_OFF + i) with (f + (FILE_BUF_OFF + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f FILE_BLOCK (FILE_BUF_OFF + i) (proj1 HJ) Hfin ltac:(lia))).
- rewrite bytes_length. apply (rdn_of_garr8 ubs0_msyms). exact HGs1.
- rewrite bytes_length. exact Hn.
- lia.
- intros a Ha. right. left. split; [exists (f, f + FILE_BLOCK); split; [right; left; reflexivity | cbn; lia]|].
exists f, FILE_BLOCK. split; [exact Hfin | lia]. }
intros c' (regsM & memM & -> & HJM & _ & HfrM & HoutM & HgrM & HcpM).
jafter_stretch HS 64%nat regsM memM (10%bv :: MEMCPY_CLOB) 0x18ce8 HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [intros rr Hrr; apply HfrM; exact (reg_in_cons_false _ _ _ Hrr)|];
assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_outside _ _ _ _ _ (f + FILE_BUF_OFF) n HoutM HgrM); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw; lia.
- eapply (region_kept_outside _ _ _ _ _ (f + FILE_BUF_OFF) n HoutM HgrM); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE13, ?unsigned_lit_small by lia; lia.
- apply (region_kept_abs_ro ubs0segs _ _ _ _ _ _ (f + FILE_BUF_OFF) n HoutM); lia.
- apply (region_kept_abs_ro ubs0segs _ _ _ _ _ _ (f + FILE_BUF_OFF) n HoutM); lia. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJM.
{ wr_norm. apply Hwr0; ew_havoc; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_eq_U, U_mul1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJM.
{ wr_norm. apply Hwr0; ew_havoc; [exact HE2 | exact HE13]. }
assert (HE2h : forall ws, ew (havoc E0 64 ws) 2 = getr regs 2) by (intros; ew_havoc; exact HE2).
assert (HE13h : forall ws, ew (havoc E0 64 ws) 13 = Z_to_bv 64 f) by (intros; ew_havoc; exact HE13).
assert (Hk3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) ->
~ (f + FILE_BUF_OFF <= a < f + FILE_BUF_OFF + n) -> mbyte ubs0segs (ms_mem ms3) a = mbyte ubs0segs mem a).
{ intros a A1 A2 A3 A4. rewrite (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF2 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF1 a A1 A2 A3).
cbn [ms_mem mkst]. unfold mbyte. rewrite (HoutM (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). exact (Hk2 a A1 A2 A3). }
assert (HA64 : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals ++ [Z_to_bv 64 g])) (havoc E0 64 (map (getr regsM) (10%bv :: MEMCPY_CLOB))))
by (eapply (env_agree_havoc_ge 32); [lia | exact HA0]).
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA64 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(right; left; reflexivity)) as (_ & _ & _ & Hcs).
cbn [r_base r_chunks base_val] in Hcs. rewrite HE13h, unsigned_lit_small in Hcs by lia.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJM)) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms3), (ms_mem ms3), md.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJM|]. split; [exact HPR|].
split; [rewrite Hr10; exact HE12|].
exists fd, W, bs.
split; [rewrite app_nil_r; reflexivity|].
split; [apply Forall_app; split; [exact Hok | exact (garr8_bytes_ok _ _ _ _ HGs)]|].
split; [rewrite (length_app (W ++ []) bs), Nat2Z.inj_add; lia|].
split.
{ apply (stdio_env_frame ubs0_msyms mem (ms_mem ms3)); [|exact Henv]. intros a Ha. destruct (Henvk a Ha) as (K1 & K2 & K3). apply Hk3; lia. }
split.
{ apply (obj_file_at_buf ubs0_msyms (ms_mem ms3) f fd bs Hfdr).
- apply (obj_at_of_chunks_sv ubs0segs _ _ _ _ LAY_FILE _ Hcs eq_refl).
rewrite <- Hn. unfold file_vals, LAY_FILE.
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|].
constructor; [cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; lia | eexists; split; [fld_in |
match goal with |- bv_unsigned (sv_denot ?E ?e) mod _ = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff; ew_havoc; rewrite HE12, HE43, !unsigned_lit_small by lia;
rewrite !Z.add_0_r; unfold zcanon, M64; change (8 * Z.of_N 8) with 64;
rewrite (Z.mod_small n), (Z.mod_small (f + FILE_BUF_OFF)) by lia; rewrite Z.mod_mod by lia; rewrite Z.mod_small by lia; lia]] |].
constructor; [fld_lit|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE47|].
do 15 (constructor; [fld_lit|]). constructor.
- apply (garr8_copy ubs0segs (ms_mem ms1) (ms_mem ms3) src (f + FILE_BUF_OFF) bs HGs1).
intros i Hi.
rewrite (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF2 (f + FILE_BUF_OFF + i)) by lia.
rewrite (HfrK _ _ _ _ _ _ _ (HE2h _) (HE13h _) HF1 (f + FILE_BUF_OFF + i)) by lia.
exact (HcpM i ltac:(lia)).
- lia. }
split.
{ apply (val_mem_word_mem ubs0segs). apply (val_mem_word_mem ubs0segs) in Hhead.
eapply (val_mem_frame ubs0_msyms); [|exact Hhead]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
assert (Hex : env_addr x) by (left; lia). destruct (Henvk x Hex) as (K1 & K2 & K3). apply Hk3; lia. }
split; [exact Hf0|]. split; [exact Hfs|]. split; [exact Hfd | exact Huniq].
-
rewrite branch_geu_U, U_lit, (U_atom _ 12 _ HE12) in Hc by lia.
assert (Hbig : FILE_BUFSIZ < n) by (destruct (Z.ltb_spec 1024 n); [lia | discriminate Hc]).
clear Hc.
jrun_ecall LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
sym_ecall_open HS.
match goal with HFx : frame_of _ _ _ (ms_mem (pend_at ?r ?pc ?m ?ro)) |- _ =>
change (ms_mem (pend_at r pc m ro)) with m in HFx, HJ;
assert (Hk3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs m a = mbyte ubs0segs mem a)
by (intros a A1 A2 A3; rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HFx a A1 A2 A3); exact (Hk1 a A1 A2 A3)) end.
match type of Hmem with mem_ok _ _ _ ?rs =>
let r := eval vm_compute in (iov_read1 rs (Some 2%nat) (-152)) in
match r with Some (?vb, ?vl) =>
destruct (iov_read1_sound ubs0segs E0 mem0 rs (Some 2%nat) (-152) vb vl Hmem ltac:(vm_compute; reflexivity)) as [M0 L0] end end.
cbn [base_val sv_denot] in M0, L0.
rewrite HE2, Hspw, Z.add_0_r, Z_to_bv_bv_unsigned, HE10 in M0. rewrite HE2, Hspw, Z.add_0_r, Z_to_bv_bv_unsigned, HE12, Hn in L0.
assert (HGs0 : garr8 ubs0segs mem0 src bs) by (eapply garr8_frame; [exact HGs|]; intros a Ha; apply Hk3; lia).
apply (J_writev_node1 ubs0_msyms MR LAWS regs0 _ mem0 _ _ _ _ _ _ _ _ _ _ _ fd W (spZ regs + -152) src bs HJ Htok (conj Hfs (conj Hfd Huniq)) Hfdr).
{ rewrite (Hregs 17%bv). eval_sr_get. reflexivity. }
{ rewrite (Hregs 10%bv). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE47. }
{ rewrite (Hregs 12%bv). eval_sr_get. rewrite denot_lit_U, U_iovcnt, Z.eqb_refl. reflexivity. }
{ rewrite (Hregs 11%bv). eval_sr_get. cbn [sv_denot]. rewrite HE2, Hspw. reflexivity. }
{ lia. } { lia. }
{ exact M0. } { exact L0. }
{ exact HGs0. } { lia. } { lia. } { change MAX_RW_COUNT with 2147479552. lia. }
{ rewrite app_nil_r in HSmax. lia. }
intros md' HJ' Hos'. cbn [ss_pc].
resume_reg_sr ubs0segs (22%bv : reg).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HE12, Hn. reflexivity. }
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_eq_U, U_mul1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ'.
{ wr_norm. apply Hwr0; [exact HE2 | exact HE13]. }
assert (Hk6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 256 <= a < spZ regs) -> ~ (f <= a < f + 232) -> mbyte ubs0segs (ms_mem ms2) a = mbyte ubs0segs mem a).
{ intros a A1 A2 A3. rewrite (HfrK _ _ _ _ _ _ _ HE2 HE13 HF2 a A1 A2 A3), (HfrK _ _ _ _ _ _ _ HE2 HE13 HF1 a A1 A2 A3).
cbn [ms_mem mkst]. exact (Hk3 a A1 A2 A3). }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
pose proof (mem_ok_region _ _ _ _ _ (st_ok_mem_ok _ _ _ _ HS) ltac:(right; left; reflexivity)) as (_ & _ & _ & Hcs).
cbn [r_base r_chunks base_val] in Hcs. rewrite HE13, unsigned_lit_small in Hcs by lia.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ')) as (Hh' & Hlz' & _).
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | exact Hh' | exact Hlz' | exact HS | reflexivity | vm_compute; reflexivity |].
exists (ms_regs ms2), (ms_mem ms2), md'.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPR|].
split; [rewrite Hr10; exact HE12|].
destruct Hos' as (Hfs' & Hfd' & Huniq').
exists fd, (W ++ bs), [].
split; [rewrite !app_nil_r; reflexivity|].
split; [apply Forall_app; split; [exact Hok | exact (garr8_bytes_ok _ _ _ _ HGs)]|].
split; [rewrite (length_app (W ++ []) bs), Nat2Z.inj_add; lia|].
split.
{ apply (stdio_env_frame ubs0_msyms mem (ms_mem ms2)); [|exact Henv]. intros a Ha. destruct (Henvk a Ha) as (K1 & K2 & K3). apply Hk6; lia. }
split.
{ apply (obj_file_at_buf ubs0_msyms (ms_mem ms2) f fd [] Hfdr).
- apply (obj_at_of_chunks_sv ubs0segs _ _ _ _ LAY_FILE _ Hcs eq_refl).
cbn [length Z.of_nat]. unfold file_vals, LAY_FILE.
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_off HE43|].
constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE43|]. constructor; [fld_lit|]. constructor; [fld_lit|]. constructor; [fld_lit|].
constructor; [fld_off HE47|].
do 15 (constructor; [fld_lit|]). constructor.
- apply garr8_nil.
- cbn. lia. }
split.
{ apply (val_mem_word_mem ubs0segs). apply (val_mem_word_mem ubs0segs) in Hhead.
eapply (val_mem_frame ubs0_msyms); [|exact Hhead]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
assert (Hex : env_addr x) by (left; lia). destruct (Henvk x Hex) as (K1 & K2 & K3). apply Hk6; lia. }
split; [exact Hf0|]. split; [exact Hfs'|]. split; [exact Hfd' | exact Huniq'].
Qed.
End S.
End b.
