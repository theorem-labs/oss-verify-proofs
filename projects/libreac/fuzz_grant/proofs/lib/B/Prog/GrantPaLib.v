(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantPaLib.v (a working branch d98082bd58b): PALib names image B's objects (the shadow-base GOT word is object 1 and its cell object 35, the side-stack flag's GOT word object 0 and its cell object 36), the image bounds are GrantTop.v's IMG_LO_B / IMG_TOP_B, and blk_off_imgB states a block's position against image B's own bounds; image A's file was made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantTop.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma find_segment_hit : forall segs (a n : Z) seg,
find_segment segs a n = Some seg -> In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
induction segs as [|s rest IH]; intros a n seg H; [discriminate|]. cbn in H.
destruct (Z.leb (Z.of_N (seg_base s)) a) eqn:Hlo; destruct (Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:Hhi; cbn in H.
- injection H as <-. split; [left; reflexivity|]. split; [apply Z.leb_le, Hlo | apply Z.leb_le, Hhi].
- destruct (IH a n seg H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH a n seg H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH a n seg H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Context {L : ptable gsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).
Definition paj_run := SRr_run_pi_tok_AJ gsym SEGS B LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to := SRr_run_to_pi_tok_AJ gsym SEGS B LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Lemma paj_branch : forall W E ss ms md Q c a b,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_ok_pi SEGS VAL E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) -> SRr SEGS W (mkCfg ms md) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false -> st_ok_pi SEGS VAL E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) -> SRr SEGS W (mkCfg ms md) Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof. exact (SRr_sym_branch_pi SEGS VAL). Qed.
Lemma paj_ret_at : forall W E ss ms md Q,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
plookup pl_tpi (ss_pc ss) = Some (PW RET_WORD_r) ->
(forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom SEGS))
(with_vm_backing (m_vm_lazy md) mat' md))) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q HS Hrv Hpl HQ.
rewrite <- pl_tpi_eq in Hpl.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA L pa_cert _ _ Hpl) as (Hck & _ & _). unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (BASE + ss_pc ss)) as [wz|] eqn:Hl; [|discriminate Hck]. apply Z.eqb_eq in Hck. subst wz.
apply (SRr_ret_at SEGS pa_tbl pa_tbl_ok pa_wx W E (abs_ss VAL ss) ms md Q HS); [destruct ss; exact Hrv | exact Hl | exact HQ].
Qed.
Lemma pa_entry_st_ok_full : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok SEGS E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok_pi SEGS VAL E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok_pi, abs_ss, setpc, st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma st_ok_pi_restrict_reg : forall (H : word -> bool) E ss ms r,
st_ok_pi SEGS VAL E ss (restrict H ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros H E ss ms r HS. exact (st_ok_restrict_reg SEGS H E (abs_ss VAL ss) ms r HS). Qed.
Lemma st_ok_pi_restrict_mkst : forall (H : word -> bool) E ss ms,
st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None ->
ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (seg_rom SEGS).
Proof. intros H E ss ms HS Hrv. exact (st_ok_restrict_mkst SEGS H E (abs_ss VAL ss) ms HS ltac:(destruct ss; exact Hrv)). Qed.
Lemma regs_kept_of_st_ok_pi : forall E ss ms regs0 extra (l : list (bv 5)),
st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
forall r, In r l -> getr (ms_regs ms) r = getr regs0 r.
Proof. intros E ss ms regs0 extra l HS HA Hl. exact (regs_kept_of_st_ok SEGS E (abs_ss VAL ss) ms regs0 extra l HS HA Hl). Qed.
Lemma img_env_codeptr : forall E, img_env VAL A_LIM E -> forall k, Z_to_bv 64 (bv_unsigned (ew E 240%nat) + k) = Z_to_bv 64 (BASE + k).
Proof. intros E HE k. pose proof (HE A_TEXT (conj (le_n A_TEXT) A_LIM_text)) as H. cbv [A_TEXT] in H. rewrite H. reflexivity. Qed.
Lemma codeptr_val : forall E k, img_env VAL A_LIM E -> sv_denot E (SOff A_TEXT k) = Z_to_bv 64 (BASE + k).
Proof. intros E k HE. cbn [sv_denot]. rewrite (HE A_TEXT (conj (le_n A_TEXT) A_LIM_text)). reflexivity. Qed.
Lemma ret_ok_codeptr_v : forall k, 0 <= k < 2 ^ 40 -> k mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 (BASE + k)).
Proof.
intros k Hk Hk2. pose proof pa_B_ok as HB. apply ret_ok_even. rewrite unsigned_lit_small by lia.
assert (HB2 : BASE mod 2 = 0).
{ destruct HB as (_ & _ & H4). apply Z.mod_divide in H4; [|lia]. apply Z.mod_divide; [lia|]. destruct H4 as [q Hq]. exists (2 * q). lia. }
rewrite Z.add_mod, HB2, Hk2 by lia. reflexivity.
Qed.
Lemma st_ok_pi_add_fact : forall E ss ms n f, st_ok_pi SEGS VAL E ss ms -> afact_ok E n f -> st_ok_pi SEGS VAL E (add_atom ss n f) ms.
Proof. intros E ss ms n f HS Hf. exact (st_ok_add_fact SEGS E (abs_ss VAL ss) ms n f HS Hf). Qed.
Lemma st_ok_pi_add_region : forall E ss ms r,
st_ok_pi SEGS VAL E ss ms -> region_wf r = true -> region_ok SEGS E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r HS Hw Hr Hd. exact (ast_ok_add_region SEGS E (abs_ss VAL ss) ms r HS Hw Hr Hd). Qed.
Theorem st_ok_pi_after_call : forall k E ss ms regs' mem' rs retk,
img_env VAL A_LIM E -> 0 <= retk < 2 ^ 40 ->
st_ok SEGS E ss ms ->
ss_resv ss = None ->
(k + 16 <= A_TEXT)%nat ->
ss_atoms_p (pband k A_TEXT) ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k A_TEXT) rs = true ->
submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SOff A_TEXT retk ->
aregs_preserved (ms_regs ms) regs' ->
Forall (region_kept SEGS E (ms_mem ms) mem') rs ->
st_ok_pi SEGS VAL (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retk)
(mkst regs' (Z_to_bv 64 (BASE + retk)) mem' (seg_rom SEGS)).
Proof.
intros k E ss ms regs' mem' rs retk HE Hrk HS Hrv Hk Hat Hwf Hnc Hmat Hsub Hra HP Hkept.
unfold st_ok_pi, abs_ss, ss_after_call, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
pose proof (st_ok_mkst SEGS E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc_p SEGS k A_TEXT E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) (BASE + retk)
(ms_mem ms) mem' rs [] CLOB HS Hk Hat) as H.
cbn [map app] in H. apply H.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hmat.
- apply regs_preserved_frame. exact HP.
- constructor.
- apply (mem_ok_kept SEGS E (ms_mem ms) mem' rs); [| exact Hnc | exact Hkept].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok SEGS E ss _ HS)].
Qed.
Theorem st_ok_pi_after_stretch : forall k E ss ms regs' mem' rs retk (clob : list (bv 5)),
st_ok SEGS E ss ms ->
ss_resv ss = None ->
(k + length clob <= A_TEXT)%nat ->
ss_atoms_p (pband k A_TEXT) ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k A_TEXT) rs = true ->
submem rs (ss_mem ss) ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
(forall r, reg_in r clob = false -> getr regs' r = getr (ms_regs ms) r) ->
Forall (region_kept SEGS E (ms_mem ms) mem') rs ->
st_ok_pi SEGS VAL (havoc E k (map (getr regs') clob)) (ss_after_stretch ss rs k clob retk)
(mkst regs' (Z_to_bv 64 (BASE + retk)) mem' (seg_rom SEGS)).
Proof.
intros k E ss ms regs' mem' rs retk clob HS Hrv Hk Hat Hwf Hnc Hmat Hsub Hnd Hnz Hsame Hkept.
unfold st_ok_pi, abs_ss, ss_after_stretch, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
pose proof (st_ok_mkst SEGS E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc_p SEGS k A_TEXT E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) (BASE + retk)
(ms_mem ms) mem' rs [] clob HS Hk Hat) as H.
cbn [map app] in H. apply H.
- exact Hnd.
- exact Hnz.
- reflexivity.
- exact Hmat.
- exact Hsame.
- constructor.
- apply (mem_ok_kept SEGS E (ms_mem ms) mem' rs); [| exact Hnc | exact Hkept].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok SEGS E ss _ HS)].
Qed.
Lemma U_img_atom : forall E, img_env VAL A_LIM E -> forall a, (A_TEXT <= a < A_LIM)%nat -> U E (SOff a 0) = VAL a.
Proof. intros E HE a Ha. rewrite U_SOff, (HE a Ha), Z.add_0_r. apply zcanon_id. pose proof (pa_val_range a). unfold M64. lia. Qed.
Lemma regs_ok_Eimg_Ereg : forall regs extra, regs_ok (Eimg (Ereg regs extra)) sr_atoms regs.
Proof.
intros. apply (regs_ok_agree 32 (Ereg regs extra)).
- split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma pa_lookup_pw : forall k w, plookup pl_tpi k = Some (PW w) -> clookup pa_tbl (BASE + k) = Some w /\ 0 <= k /\ k mod 4 = 0.
Proof.
intros k w Hpl. rewrite <- pl_tpi_eq in Hpl.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA L pa_cert _ _ Hpl) as (Hck & Hk0 & Hk4). unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (BASE + k)) as [wz|] eqn:Hl; [|discriminate Hck]. apply Z.eqb_eq in Hck. subst wz. auto.
Qed.
Lemma pa_fetch_pw : forall k w, plookup pl_tpi k = Some (PW w) -> fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. apply pa_fetch_ok. exact (proj1 (pa_lookup_pw k w H)). Qed.
Lemma pa_slot_img : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e -> IMG_LO_B <= BASE + k.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA L pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_img_range _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia. lia.
Qed.
Lemma pa_base_lo : IMG_LO_B <= BASE.
Proof.
pose proof (pl_slot0 (L:=L)) as H0. rewrite pl_tpi_eq in H0.
destruct (plookup pl_tpi 0) as [e|] eqn:He; [|destruct H0].
pose proof (pa_slot_img 0 e ltac:(lia) He) as H. lia.
Qed.
Lemma st_ok_pi_pin_reg' : forall E ss ms (r : bv 5) z,
st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r z HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
(sr_set (ss_regs ss) r (SLit z)) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq. rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma st_ok_pi_jalr_entry : forall (H : word -> bool) E ss ms (rd : bv 5) tgt,
img_env VAL A_LIM E -> st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None -> bv_eqb rd 0 = false ->
0 <= ss_pc ss + 4 < 2 ^ 40 ->
st_ok SEGS E (mkSST tgt (sr_set (ss_regs ss) rd (SOff A_TEXT (ss_pc ss + 4))) (ss_fregs ss) (ss_mem ss) None (ss_facts ss))
(restrict H (mkst (regupd (ms_regs ms) rd (Z_to_bv 64 (BASE + (ss_pc ss + 4)))) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom SEGS))).
Proof.
intros H E ss ms rd tgt HEI HS Hrv Hrd Hk. rewrite restrict_mkst_fx.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold abs_ss, setpc in H4, H7, H8, H9. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H4, H7, H8, H9.
rewrite Hrv in H4.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst restrict
ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
cbn [restrict ms_fregs ms_fcsr ms_regs ms_mem] in H2, H5, H7, H8, H9.
do 6 (split; [first [reflexivity | assumption] |]).
split; [| exact (conj H8 H9)].
pose proof (regs_ok_set E (ss_regs ss) (ms_regs ms) rd (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (SOff A_TEXT (ss_pc ss + 4)) H7) as R.
rewrite Hrd in R. apply R. exact (codeptr_val E (ss_pc ss + 4) HEI).
Qed.
Lemma v_jalr_lit_even : forall tgt, 0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 -> v_jalr (Z_to_bv 64 tgt) 0 = Z_to_bv 64 tgt.
Proof.
intros tgt Ht He. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite YK0s.land_m2_even by exact He. reflexivity.
Qed.
Lemma SRr_jalr_call_pi : forall W E ss ms md Q w (rd rs1 : bv 5) tgt,
img_env VAL A_LIM E -> st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
plookup pl_tpi (ss_pc ss) = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Jalr rd rs1 0%bv, 4%Z) -> bv_eqb rd 0 = false ->
ss_pc ss + 4 < 2 ^ 40 ->
getr (ms_regs ms) rs1 = Z_to_bv 64 tgt -> 0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 ->
(forall mat' ms1,
ms1 = mkst (regupd (ms_regs ms) rd (Z_to_bv 64 (BASE + (ss_pc ss + 4)))) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom SEGS) ->
st_ok SEGS E (mkSST tgt (sr_set (ss_regs ss) rd (SOff A_TEXT (ss_pc ss + 4))) (ss_fregs ss) (ss_mem ss) None (ss_facts ss))
(restrict (w_H W) ms1) ->
SRr SEGS W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q w rd rs1 tgt HEI HS Hrv Hpc Hdec Hrd Hk Hrs1 Htgt Heven HK.
pose proof pa_B_ok as (HB0 & HB1 & _).
pose proof (pa_lookup_pw _ _ Hpc) as (Hl & Hk0 & _).
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hshape at 1.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
eapply (step_jalr_link SEGS _ _ _ _ (Z_to_bv 32 w) rd rs1 (0%bv : bv 12) (Z_to_bv 64 tgt)).
+ exact (pa_fetch_ok _ _ Hl).
+ eapply not_ecall_of_decode; [exact Hdec | discriminate].
+ exact Hdec.
+ exact Hrd.
+ cbn [ms_regs mkst]. exact Hrs1.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
change (bv_signed (0%bv : bv 12)) with 0. rewrite (v_jalr_lit_even tgt Htgt Heven).
unfold v_addi. rewrite unsigned_lit_small by (clear - HB0 HB1 Hk0 Hk; lia).
replace (BASE + ss_pc ss + 4) with (BASE + (ss_pc ss + 4)) by (clear; lia).
eapply HK; [reflexivity|].
exact (st_ok_pi_jalr_entry (w_H W) E ss ms rd tgt HEI HS Hrv Hrd ltac:(clear - Hk0 Hk; lia)).
Qed.
Lemma SRr_jr_pi : forall W E ss ms md Q w (rs1 : bv 5) tgt,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
plookup pl_tpi (ss_pc ss) = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Jalr 0%bv rs1 0%bv, 4%Z) ->
getr (ms_regs ms) rs1 = Z_to_bv 64 tgt -> 0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 ->
(forall mat' ms1,
ms1 = mkst (ms_regs ms) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom SEGS) ->
st_ok SEGS E (mkSST tgt (ss_regs ss) (ss_fregs ss) (ss_mem ss) None (ss_facts ss)) (restrict (w_H W) ms1) ->
SRr SEGS W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q w rs1 tgt HS Hrv Hpc Hdec Hrs1 Htgt Heven HK.
pose proof (pa_lookup_pw _ _ Hpc) as (Hl & _ & _).
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hshape at 1.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
eapply (step_jalr_x0 SEGS _ _ _ _ (Z_to_bv 32 w) rs1 (0%bv : bv 12) (Z_to_bv 64 tgt)).
+ exact (pa_fetch_ok _ _ Hl).
+ eapply not_ecall_of_decode; [exact Hdec | discriminate].
+ exact Hdec.
+ cbn [ms_regs mkst]. exact Hrs1.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
change (bv_signed (0%bv : bv 12)) with 0. rewrite (v_jalr_lit_even tgt Htgt Heven).
eapply HK; [reflexivity|].
rewrite restrict_mkst_fx.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold abs_ss, setpc in H4, H7, H8, H9. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H4, H7, H8, H9.
rewrite Hrv in H4.
cbn [restrict ms_fregs ms_fcsr ms_regs ms_mem] in H2, H5, H7, H8, H9.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
do 6 (split; [first [reflexivity | assumption] |]). split; [exact H7 | exact (conj H8 H9)].
Qed.
Record PALib : Prop := {
pal_got_shadow : as_got_shadow B = VAL (A_OBJ 1);
pal_cell : as_shadow_cell B = VAL (A_OBJ 35);
pal_got_uar : as_got_uar B = VAL (A_OBJ 0);
pal_uar_cell : as_uar_cell B = VAL (A_OBJ 36);
pal_got_cell : VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 35) \/ VAL (A_OBJ 35) + 8 <= VAL (A_OBJ 1);
pal_env : api_env SEGS B;
pal_free : SIGMA GS___interceptor_trampoline_free = pc_wrap_free (as_code B);
pal_malloc : SIGMA GS___interceptor_trampoline_malloc = pc_wrap_malloc (as_code B);
pal_rt_below : pc_free_ra0 (as_code B) < BASE /\ pc_malloc_ra0 (as_code B) < BASE
}.
Definition got_regionP : YP09.region := YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 35) 0))].
Definition bcell_regionP (bx : nat) : YP09.region := YP09.mkRegion (Some (A_OBJ 35)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff bx 0))].
Definition stack_region (frame : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- frame) 0 (- frame) 0 [].
(* A block of the heap lies wholly below or wholly above image B's own range: the image's bytes are never
   client bytes (client_byte_not_img), and the layout's image range covers IMG_LO_B..IMG_TOP_B (pa_img_cover). *)
Lemma blk_off_imgB : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n <= IMG_LO_B \/ IMG_TOP_B <= p.
Proof.
intros ly S W mem md p n (M & LG & _) Hin. pose proof (pa_img_cover ly S md LG) as [C1 C2].
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Hn in G7.
pose proof (req_size_pos n ltac:(lia)) as [Q _].
destruct (Z.le_gt_cases (p + req_size n) IMG_LO_B) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases IMG_TOP_B p) as [|H2]; [right; lia|]. exfalso.
pose proof IMG_LO_B_lt_TOP as HLT.
apply (client_byte_not_img B ly S _ (Z.max p IMG_LO_B) M).
- left. exists k. rewrite Hu. unfold ck_n. rewrite Hn. refine (conj Hk (conj Hst _)). lia.
- unfold in_zr. lia.
Qed.
(* blk_off_imgP concludes the core's off_img, which image B's own bounds imply. On the integration tree off_img is
   lib/B/YCbq.v's, over image B's top 0x5fb000, so blk_off_imgP states image B's bound and duplicates blk_off_imgB; the walks
   do not depend on which they use. *)
Lemma blk_off_imgP : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> off_img p (req_size n).
Proof.
intros ly S W mem md p n HAR Hin. pose proof (blk_off_imgB ly S W mem md p n HAR Hin) as H.
pose proof IMG_LO_B_val as E1. pose proof IMG_TOP_B_val as E2. unfold off_img. lia.
Qed.
Lemma region_kept_val_at : forall E (m m' : word -> option byte) nn lo (n : nat) v wlo whi cs,
bv_unsigned (ew E nn) = lo -> val_mem SEGS m lo n v -> val_mem SEGS m' lo n v -> whi <= wlo ->
region_kept SEGS E m m' (YP09.mkRegion (Some nn) 0 (Z.of_nat n) wlo whi cs).
Proof.
intros E m m' nn lo n v wlo whi cs Hn H1 H2 Hro.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
replace a with (lo + (a - lo)) by lia. apply (val_mem_agree SEGS m m' lo n v H1 H2). lia.
Qed.
Lemma ew_havoc_above : forall E k ws i, (k + length ws <= i)%nat -> ew (havoc E k ws) i = ew E i.
Proof.
intros E k ws i Hi. unfold havoc. cbn [ew]. destruct (i <? k)%nat eqn:Hlt; [reflexivity|]. apply nth_overflow. lia.
Qed.
Lemma img_env_havoc : forall E k ws, img_env VAL A_LIM E -> (k + length ws <= A_TEXT)%nat -> img_env VAL A_LIM (havoc E k ws).
Proof. intros E k ws HE Hk a Ha. rewrite ew_havoc_above by lia. exact (HE a Ha). Qed.
End g.
End d.
Arguments PALib {_ _ _} B.
Ltac pmkst HS :=
first [ rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]
| lazymatch type of HS with st_ok ?segs _ _ _ => rewrite (st_ok_restrict_mkst segs _ _ _ _ HS eq_refl); cbn [ss_pc setpc] end ].
Ltac psym_why_tok TPI TW K Bx Bspan SH st :=
let r := eval vm_compute in (sym_step_pi_tok TPI TW K Bx Bspan SH st) in
lazymatch r with
| PTStop ?why => why
| _ => fail "psym_why_tok: state is not stuck"
end.
Ltac prreg_norm Hr :=
cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in Hr;
repeat (rewrite ew_havoc_old in Hr; [|cbv; lia]);
try (lazymatch type of Hr with context [ew ?E 240%nat] =>
lazymatch goal with HEI : img_env _ _ E |- _ => rewrite !(img_env_codeptr E HEI) in Hr end end);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr.
Ltac prreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr; prreg_norm Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr; prreg_norm Hr
end.
Ltac jafter_call_keep_pi HS k regs2 mem2 HP idxs HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jafter_call_keep_pi: no img_env hypothesis for" E end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call k E (abs_ss val ss) ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call (abs_ss val ss) rs k retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jafter_call_keep_pi: no img_env hypothesis for" E end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call k E ss ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call ss rs k retk) with ss2 in HS2
end.
Ltac jafter_stretch_pi HS k regs2 mem2 clob retk HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let rs := eval vm_compute in (ss_mem ss) in
pose proof (st_ok_pi_after_stretch k E (abs_ss val ss) ms regs2 mem2 rs retk clob HS eq_refl
ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) (submem_refl rs) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob retk) in
change (ss_after_stretch (abs_ss val ss) rs k clob retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (ss_mem ss) in
pose proof (st_ok_pi_after_stretch k E ss ms regs2 mem2 rs retk clob HS eq_refl
ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) (submem_refl rs) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob retk) in
change (ss_after_stretch ss rs k clob retk) with ss2 in HS2
end.
Ltac paj_after_run_tok HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in let HEI := fresh "HEI" in
intros ws ms' mat' Hlen HEI HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK, HEI;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac paj_tables RUN :=
lazymatch type of RUN with
| context [sym_runN_pi_tok ?tpi ?tw _ _ _ _ _ _] => constr:((tpi, tw))
| context [sym_run_toN_pi_tok ?tpi ?tw _ _ _ _ _ _ _] => constr:((tpi, tw))
end.
Ltac paj_run_tok RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_tok: no hypothesis  img_env _ _ E" end in
eapply (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
| _ => fail "paj_run_tok: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_to_tok RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_to_tok: no hypothesis  img_env _ _ E" end in
eapply (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
| _ => fail "paj_run_to_tok: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac psrr_branch_tok RUN BR HS SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let why := psym_why_tok tpi tw K Bx Bspan SH (start K Bx Bspan SH ss) in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (BR W E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "psrr_branch_tok: state is not stuck at a branch:" why
end end
end
end.
