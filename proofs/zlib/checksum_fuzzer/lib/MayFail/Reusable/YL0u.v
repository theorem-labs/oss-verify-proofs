(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0u.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN35.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition hdr_env (E : env) (data : list byte) (buf : Z) : Prop :=
ed E 2 = data /\ bv_unsigned (ew E 14) = buf /\ bv_unsigned (ew E 27) = Z.of_nat (length data).
Definition hdr_anch (E : env) : Prop := forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored E G.
Lemma hdr_anch_ext : forall E E', hdr_anch E -> (forall n, (n < 10)%nat -> ew E' n = ew E n) -> hdr_anch E'.
Proof.
intros E E' H HE G HG. apply (stack_anchored_ext E E' RD_facts G (H RD_facts eq_refl) HG).
intros [n K] Hin. cbn [fst].
match type of Hin with In _ ?l => let v := eval vm_compute in l in change l with v in Hin end.
assert (Hn : (n < 10)%nat).
{ cbn in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
apply HE. exact Hn.
Qed.
Definition md_ok (inp : ProcInput) (md : Model) : Prop :=
fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) md /\ fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md /\ m_fs md = in_fs inp.
Lemma md_ok_vm : forall inp md vm, md_ok inp md -> md_ok inp (with_vmmaps vm md).
Proof. intros inp md vm ([H1 H1'] & [H2 H2'] & H3). unfold md_ok, fdchan. autorewrite with model. repeat split; assumption. Qed.
Lemma md_ok_ex : forall inp md md', md_ok inp md -> (exists vm, md' = with_vmmaps vm md) -> md_ok inp md'.
Proof. intros inp md md' H [vm ->]. apply md_ok_vm. exact H. Qed.
End c.
Ltac drv_anch ::= first [ assumption | match goal with H : hdr_anch ?E |- stack_anchored ?E _ => apply H; vm_compute; reflexivity end ].
Ltac drv_fwrite HS Hch k HF :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 ?fd) ?ch ?model =>
lazymatch goal with |- realizes _ _ (t_emit (map _ ?msg) _) =>
let r := eval vm_compute in (wx_msg_check k ss msg) in
lazymatch r with
| Some (?s2, _) =>
let Hck := fresh "Hck" in
assert (Hck : wx_msg_check k ss msg = Some (s2, fd)) by (vm_compute; reflexivity);
apply (realizes_writev_msg_by_run E ss ms model ch k msg s2 fd _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in
let Hsk := fresh "Hsk" in let Hma := fresh "Hma" in
intros ms' ws HS HF Hsk Hma; clear Hsk Hma; cbn [ms_mem mkst pend_at] in HF
| None => fail "drv_fwrite: wx_msg_check failed on this state"
end
end end end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma list_len2 {X} : forall (l : list X), (2 <= length l)%nat -> exists a b r, l = a :: b :: r.
Proof. intros [|a [|b r]] H; cbn in H; try lia. exists a, b, r. reflexivity. Qed.
Definition K_SW : nat := 47.
Definition K_SF : nat := 58.
Definition RA_sf : Z := Eval vm_compute in (src0_A_main + 0x1fc).
Definition ss_h0 : sstate := Eval vm_compute in (run_ S_HDR).
Definition cond_SH : acond := mkAC BC_GEU (SLit 5) (SOff 27 0).
Definition cond_H6 : acond := mkAC BC_LTU (SLit 5) (SOff 27 0).
Definition ss_short : sstate := Eval vm_compute in (add_cond ss_h0 cond_SH).
Definition ss_sw : sstate := Eval vm_compute in
(match wx_msg_check K_SW ss_short msg_short with Some (s2, _) => s2 | None => ss_short end).
Definition ss_sf : sstate := Eval vm_compute in (runto_ src0_A_free ss_sw).
Definition L_sf : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep MAIN_SP ALLOC_STACK (ss_mem ss_sf)).
Definition RS_sf : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd L_sf) (K_SF + 16) with Some x => x | None => [] end).
Lemma site_sf : site_check src0_msyms ss_sf src0_A_free RA_sf MAIN_SP src0_keep [] K_SF L_sf = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statics_sf : drv_add_statics src0_msyms (map snd L_sf) (K_SF + 16) = Some RS_sf.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_sf : exit_run_check src0segs src0tbl (post_state ss_sf RA_sf K_SF RS_sf) 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma a0_sf : sr_get (ss_regs ss_sf) 10%bv = SOff 14 0.
Proof. vm_compute. reflexivity. Qed.
Definition blkreg6 : YP09.region := block_region 14 6 [mkChunk 0 (CData 2 0 6)].
Definition ss_h0c : sstate := Eval vm_compute in (add_cond ss_h0 cond_H6).
Definition ss_h6 : sstate := mkSS (ss_pc ss_h0c) (ss_regs ss_h0c) (blkreg6 :: ss_mem ss_h0c) None (ss_facts ss_h0c).
Definition ss_h1 : sstate := Eval vm_compute in (run_ ss_h6).
Definition cond_OV : acond := mkAC BC_LTU (SOff 27 0) sv_cl6.
Definition cond_OK : acond := mkAC BC_GEU (SOff 27 0) sv_cl6.
Definition ss_ov : sstate := Eval vm_compute in (add_cond ss_h1 cond_OV).
Definition ss_swO : sstate := Eval vm_compute in
(match wx_msg_check K_SW ss_ov msg_overrun with Some (s2, _) => s2 | None => ss_ov end).
Definition ss_sfO : sstate := Eval vm_compute in (runto_ src0_A_free ss_swO).
Definition L_sfO : list (nat * YP09.region) := Eval vm_compute in
(List.filter (fun p => negb (obase_eqb (r_base (snd p)) (Some 14%nat))) (precall src0_keep MAIN_SP ALLOC_STACK (ss_mem ss_sfO))).
Definition RS_sfO : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd L_sfO) (K_SF + 16) with Some x => x | None => [] end).
Lemma site_sfO : site_check src0_msyms ss_sfO src0_A_free RA_sf MAIN_SP src0_keep [] K_SF L_sfO = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statics_sfO : drv_add_statics src0_msyms (map snd L_sfO) (K_SF + 16) = Some RS_sfO.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_sfO : exit_run_check src0segs src0tbl (post_state ss_sfO RA_sf K_SF RS_sfO) 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma a0_sfO : sr_get (ss_regs ss_sfO) 10%bv = SOff 14 0.
Proof. vm_compute. reflexivity. Qed.
Lemma ss_h_facts : ss_pc ss_h0 = src0_A_main + 0x100 /\ ss_pc ss_h1 = src0_A_main + 0x11c /\
sr_get (ss_regs ss_h1) 10%bv = sv_cl6 /\ sr_get (ss_regs ss_h1) 18%bv = sv_cl /\
sr_get (ss_regs ss_h1) 19%bv = SOff 27 0 /\ sr_get (ss_regs ss_h1) 21%bv = sv_b1s /\ sr_get (ss_regs ss_h1) 9%bv = SOff 14 0 /\
sep_check src0_msyms (ss_facts ss_h0c) (ss_mem ss_h0c) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Section e.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variables (inp : ProcInput) (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis HLc : dlen data < cap0.
Hypothesis HW : WF A'.
Hypothesis HB : bounded A'.
Hypothesis Hid : st_init_done A' = true.
Ltac msg_free_exit HS HMR Hch Hmd Hin HE13 E ss_sw ss_sf L_sf RS_sf site statics exit_ck a0_lemma :=
let HF := fresh "HF" in let Hr10 := fresh "Hr10" in
let HG00 := fresh "HG00" in let HSA00 := fresh "HSA00" in
lazymatch type of HS with st_ok _ _ ?ss0 _ =>
assert (HG00 : facts_ok E (ss_facts ss0)) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X);
assert (HSA00 : stack_anchored E (ss_facts ss0)) by drv_anch
end;
drv_fwrite HS Hch K_SW HF;
lazymatch type of HS with st_ok _ ?Eh _ ?msx =>
change (st_ok src0segs Eh ss_sw msx) in HS;
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
apply (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX _ _ _ _ _ E _ src0_keep rs0 HMR HG00 HSA00 ltac:(vm_compute; reflexivity)) in HF end;
clear HMR HG00 HSA00; rename HF into HMR;
let HANh := fresh "HANh" in
assert (HANh : hdr_anch Eh) by (eapply hdr_anch_ext; [eassumption | intros; apply ew_havoc_old; unfold K_SW; lia]);
drv_run_to_with src0tbl_ok HS src0_A_free HF;
lazymatch type of HS with st_ok _ _ _ ?msy => change (st_ok src0segs Eh ss_sf msy) in HS end;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Eh HS HF HMR;
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site src0_msyms API AX _ ss_sf _ _ L' A' b0 cap0 MAIN_SP src0_keep [] K_SF L_sf RS_sf RA_sf _
HS ltac:(drv_anch) site statics HMR HW HB Hid Hin);
[ rewrite Hr10, a0_lemma; cbn [sv_denot]; rewrite Z.add_0_r, (ew_havoc_old _ K_SW _ 14) by (unfold K_SW; lia); rewrite <- HE13, Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| ];
clear Hr10;
let vm2 := fresh "vm2" in let HSA2 := fresh "HSA2" in
intros A2 L2 ms3 md3 g2 tr HS2 HSA2 HMR2 HW2 HB2 [vm2 Hmd3] Hpath Hub2 Hstab Hhi Hbk;
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _);
replace (in_fs inp) with (m_fs md3) by (rewrite Hmd3; autorewrite with model; exact (proj2 (proj2 Hmd)));
exact (src0_exit _ _ ms3 md3 2 HS2 ltac:(lia) exit_ck Hh2 Hlz2)
end.
Theorem src0_short_tail : forall E ms md,
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> dlen data <= 5 ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md -> md_ok inp md ->
realizes src0segs (mkCfg ms md) (diag msg_short (in_fs inp)).
Proof.
intros E ms md (HEd & HE13 & HE26) HAN HL HS0 HMR Hmd.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (proj1 (proj2 Hmd)) as Hch.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia). unfold dlen in HL.
assert (HS : st_ok src0segs E ss_short ms).
{ apply (st_ok_add_cond src0segs E ss_h0 ms BC_GEU (SLit 5) (SOff 27 0) HS0).
rewrite branch_geu_U, U_SLit, U_SOff, HE26, Z.add_0_r, !zcanon_id by (unfold M64; lia). rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
clear HS0. unfold diag, wr, ex.
msg_free_exit HS HMR Hch Hmd Hin HE13 E ss_sw ss_sf L_sf RS_sf site_sf statics_sf exit_sf a0_sf.
Qed.
Theorem src0_to_h1 : forall E ms md T,
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> 6 <= dlen data ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall ms', st_ok src0segs E ss_h1 ms' -> aa_MR API L' A' (ms_mem ms') md ->
blk_data src0_msyms (ms_mem ms') (ptr_addr L' b0) data ->
realizes src0segs (mkCfg ms' md) T) ->
realizes src0segs (mkCfg ms md) T.
Proof.
intros E ms md T (HEd & HE13 & HE26) HAN HL HS0 HMR HD K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia). unfold dlen in HL, HLc.
destruct ss_h_facts as (Hpc0 & Hpc1 & _ & _ & _ & _ & _ & Hsep).
apply (st_ok_add_cond_neg src0segs E ss_h0 ms BC_GEU (SLit 5) (SOff 27 0)) in HS0.
2:{ rewrite branch_geu_U, U_SLit, U_SOff, HE26, Z.add_0_r, !zcanon_id by (unfold M64; lia).
rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
change (add_cond ss_h0 (mkAC (neg_bc BC_GEU) (SLit 5) (SOff 27 0))) with ss_h0c in HS0.
assert (HS : st_ok src0segs E ss_h6 ms).
{ destruct HS0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold st_ok, ss_h6. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [| exact H9].
eapply (mem_ok_cons src0_msyms); [exact H8 | reflexivity | |].
- unfold region_ok, blkreg6, block_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE13.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_cdata0 src0_msyms); [exact HEd | lia |]. intros i Hi. apply HD. lia.
- eapply (sep_check_disjoint src0_msyms (aa_MR API) (aa_laws API) AX E _ (ss_facts ss_h0c) L' A' md b0 cap0 _ blkreg6 14);
[exact H9 | apply HAN; vm_compute; reflexivity | exact HMR | exact Hin | reflexivity | cbn; lia | | | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | exact Hsep].
+ cbn [r_lo blkreg6 block_region]. rewrite HE13. lia.
+ cbn [r_hi blkreg6 block_region]. rewrite HE13. lia. }
clear HS0.
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E ss_h1 msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L' A' m0 m1 _ E (ss_facts ss_h1) src0_keep rs0 b0 cap0 (ptr_addr L' b0) data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx => exact (K msx HS HMR HD) end.
Qed.
Theorem src0_overrun_tail : forall E ms md,
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> 6 <= dlen data -> dlen data < 6 + config_len data ->
st_ok src0segs E ss_h1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_ok inp md ->
realizes src0segs (mkCfg ms md) (diag msg_overrun (in_fs inp)).
Proof.
intros E ms md (HEd & HE13 & HE26) HAN HL Hov HS0 HMR Hmd.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (proj1 (proj2 Hmd)) as Hch.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia). unfold dlen in HL, Hov, HLc.
assert (HS : st_ok src0segs E ss_ov ms).
{ apply (st_ok_add_cond src0segs E ss_h1 ms BC_LTU (SOff 27 0) sv_cl6 HS0).
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
pose proof (config_len_bound data) as Hcl.
rewrite branch_ltu_U, (U_cl6 E d0 d1 rest) by (rewrite HEd; exact Ed).
rewrite U_SOff, HE26, Z.add_0_r, zcanon_id by (unfold M64; lia).
apply Z.ltb_lt. rewrite <- Ed. lia. }
clear HS0. unfold diag, wr, ex.
msg_free_exit HS HMR Hch Hmd Hin HE13 E ss_swO ss_sfO L_sfO RS_sfO site_sfO statics_sfO exit_sfO a0_sfO.
Qed.
End e.
End d.
