(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names and addresses changed; 1881 of its 1980 lines of code are new or changed and 485 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segB2.v, with its module names changed; 283 of its 407 lines of code are new or changed and 1856 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD2_s34.v, with its addresses changed; 63 of its 172 lines of code are new or changed and 298 lines of the source are left out. *)
(* check_round_trip (fs.asan 0x81a9c, build A), WALK LANE D2, SEGMENT 35: from the boundary crtD2_INV_35 (0x822b4,
   the return of pj_free (&back)) over `mv a0, s10` and `jal pj_free` (0x822b8, a0 = s10 = F + 0x20 = &doc) to the
   boundary crtD2_INV_36 (0x822bc, the return of pj_free (&doc)).

   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd19.v .. sd24.v)
   The function-level lookup is the one quoted in the lane head (internal path)
   (checker a Theorem Labs lane, role check, CONFIRM). This file ports the CONTENT of d25a984c903's St20 step
   (check_round_trip_sd20.v: pj_free frees the document's tree D20; text's and back's blocks and the frame survive) into
   S0's ajournal / ARU / U form, with the same kit as segment 34 (FSH_crt_segD2_s34.v): pj_free_spec at level 0,
   v = F + 0x20, D = Ddoc. The document is crt_doc tb2, an object of depth 2 (its one nested object holds strings
   only), so its tree is freeable at depth 2 with no further premise. The budget needs no room premise here:
   crtD2_INV_35 already carries the allowance for EV_pj_free Ddoc. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret
FSW_frame FSW_frame3 FSW_rd FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_segD FSH_crt_segD2 FSH_crt_segD2_s34.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the run (MEASURED by the engine over crt_tbl) =================
   From the store-free boundary state at 0x822b4: `mv a0, s10` and `jal pj_free` reach pj_free (A 0x83570) with
   a0 = s10 (atom 26 = &doc), ra = 0x822bc, and every other register still its boundary atom. *)
Definition crtD2_sc35 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_free (crt_ss2 0x822b4)).
Lemma crtD2_run35 : sym_run_toN tfibsegs crt_tbl FUEL A_pj_free (crt_ss2 0x822b4) = (crtD2_sc35, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_site35 : crt_csite crtD2_sc35 A_pj_free 0x822bc /\ sr_get (ss_regs crtD2_sc35) 10%bv = SOff 26 0.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ssave35 : crt_ssave crtD2_sc35.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

(* ================= segment 35 ================= *)
Section s35. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_FREE : @pj_free_spec fx rc SK tfibsegs B 0.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the call's own part: from crtD2_INV_35 at the call, pj_free (&doc) into crtD2_INV_36 *)
Lemma crtD2_hcall35 :
  crt_hcall SK B crtD2_sc35 A_pj_free 0x822bc (STK_pj_free 2) (crtD2_INV_35 B) (crtD2_INV_36 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJ HARU Hfr HSB RG HPRE HFRL HTOP.
destruct crtD2_site35 as ((_ & _ & _ & _ & G2 & _ & _ & _ & _ & _) & G10).
pose proof crtD2_ssave35 as HSV.
pose proof HE as (E2 & _).
destruct HINV as (E20 & E21 & E26 & (same & nsame & back & Ddoc & live & peak & cnt &
  E24 & E25 & HPB & HPU & HFH & HTX & HBK & HRT & HPO2 & HG & _ & HL & HC & Hk)).
unfold crtD2_blocks in HPB. unfold crtD2_heads in HPU.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HARU as (_ & (_ & PWU) & _).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJ HARU Hfr) as (_ & HF4096 & HFceil & _ & _ & _).
pose proof (crtD2_F_at SK B cx ly3 S3 W3 (unpoison U3 memC) mdC k HJ) as EFa.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (@alloc_ceiling_value rc) as (HCr & _).
(* the registers at the call *)
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (R10 : YK11.getr regsC 10%bv = w64 (crt_F cx + 0x20)) by (rewrite RG, G10, fsw_SOff0; exact E26).
(* the boundary's data facts, from the boundary memory to the call's (same below alloc_ceiling) *)
assert (KIMG : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W3) memC a = aview tfibsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (crt_img_range a Ha). apply (aview_below (w_H W3) (ms_mem ms3) memC alloc_ceiling a HSB). lia. }
pose proof (crt_glob_keep W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ KIMG HG) as HG'.
pose proof (rnode_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC Ddoc (crt_F cx + 0x20) _ Ddoc HAR HSB
  ltac:(lia) ltac:(lia) HRT) as HRT'.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HAR HSB HPO2) as HPO2'.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR HSB HTX) as HTX'.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR HSB HBK) as HBK'.
(* the live list at the call: crt's entry blocks and the four kept blocks (K), then Ddoc's *)
assert (HPK : Permutation (ablocks B ly3 S3)
  ((ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back) ++ rd_hblocks Ddoc)).
{ eapply Permutation_trans; [exact HPB|]. rewrite <- app_assoc. apply Permutation_refl. }
assert (HDh : forall bk, In bk (rd_hblocks Ddoc) -> In bk (ablocks B ly3 S3)).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPK)). apply in_or_app. right. exact Hbk. }
assert (HKin : forall bk,
  In bk (ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back) -> ~ In bk (rd_hblocks Ddoc)).
{ intros bk Hbk. exact (crtD2pf_not_in_r B ly3 S3 W3 _ mdC _ _ bk HAR HPK Hbk). }
(* U at the call: the kept heads, then Ddoc's *)
assert (HPU2 : Permutation U3 ((c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)]) ++ rd_heads Ddoc)).
{ eapply Permutation_trans; [exact HPU|]. rewrite <- app_assoc. apply Permutation_refl. }
assert (HF16 : Forall (fun x => 0 < snd x) (rd_heads Ddoc)).
{ apply Forall_forall. intros x Hx. unfold rd_heads in Hx. apply in_map_iff in Hx as (b & <- & _). cbn [snd].
  unfold HEAD. lia. }
pose proof (crtD2_udrop_perm U3 _ (rd_heads Ddoc) PWU HPU2 HF16) as HUD.
(* pj_free's premises: the document's tree is freeable at depth 2 = its depth *)
destruct HRT' as (HN & HBk & HI).
assert (Hdep : (PjTree.depth (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) <= 2)%nat)
  by exact (le_n 2).
pose proof (PjStruct.pj_fd_mono tfibsegs _ _ _ 2 _ Ddoc Hdep (PjStruct.pj_node_fd tfibsegs _ _ _ _ Ddoc HN)) as HFD.
assert (HINC : incl (rd_heads Ddoc) U3).
{ intros h Hh. apply (Permutation_in _ (Permutation_sym HPU2)). apply in_or_app. right. exact Hh. }
assert (HSUM : rd_sum Ddoc <= live).
{ pose proof (crt_live0 B cx HB).
  pose proof HTX as (_ & _ & Ht & _). pose proof HBK as (_ & _ & Hb & _). lia. }
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNEV & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & HNJ & _).
assert (HNEVD : st_nev S3 + EV_pj_free Ddoc <= EV_MAX) by (unfold CRT_EV_WRAP, EV_fuzz_free in Hk; lia).
pose proof (crtD2_window SK B cx ly3 S3 U3 W3 memC mdC k regsC 0x20 (STK_pj_free 2) HB HJ HARU Hfr Esp
  ltac:(lia) ltac:(lia) crtD2_stk_pj_free) as HWIN.
assert (HV : crt_F cx + 0x20 = 0 /\ Ddoc = [] \/
  crt_F cx + 0x20 <> 0 /\
  PjStruct.pj_fd tfibsegs (mrestrict (w_H W3) memC) (fun a n => In (a, n) Ddoc) (2 - 0) (crt_F cx + 0x20) Ddoc /\
  pobj tfibsegs B ly3 S3 W3 memC (crt_F cx + 0x20) /\
  (crt_F cx + 0x20 + 56 <= spZ regsC - STK_pj_free (2 - 0) \/ spZ regsC <= crt_F cx + 0x20)).
{ right. split; [lia|]. split; [exact HFD|]. split; [exact HPO2'|]. left. exact HWIN. }
(* the call *)
pose proof (PJ_FREE ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (crt_F cx + 0x20) Ddoc live peak cnt SIZE_MAXZ
  ltac:(lia) HPRE HFH R10 HV HBk HINC HG' HSUM HNEVD) as HSRr.
exists ((crt_F cx + 0x20, crt_F cx + 0x20 + 56) :: ablocks_fp (rd_hblocks Ddoc) ++ FS_PSTAT_FP), (EV_pj_free Ddoc).
eexists. split; [exact HSRr|].
(* the footprint is crt's: the object is crt's own frame, the freed blocks crt's temporaries, the statics image *)
split.
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
  - right. right. right. left. exists 3, (c_pos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa, crt_frame3. lia.
  - apply inFP_app in Ha as [Ha | Ha].
    + right. left. destruct Ha as (r & Hr & Hra). unfold ablocks_fp in Hr.
      apply in_map_iff in Hr as ([b n] & <- & Hbn). cbn [fst snd] in Hra.
      exists b, n. split; [exact (HDh _ Hbn)|]. split; [|lia].
      apply (crtD2pf_not_in_l B ly3 S3 W3 _ mdC _ _ (b, n) HAR HPB).
      apply in_or_app. right. exact Hbn.
    + right. right. left. split; [exact Ha | exact (crt_pstat_img a Ha)]. }
(* the flag word is off the footprint *)
split.
{ intros a Ha Hf. rewrite crt_frame3 in Ha. apply inFP_cons in Hf as [Hf | Hf]; [lia|].
  apply (crtD2pf_frm_off_fp B ly3 S3 W3 _ mdC (c_pos cx) [] (rd_hblocks Ddoc) a HAR Hin3 HDh);
    [rewrite EFa; lia | exact (inFP_nil a) | exact Hf]. }
(* the next boundary *)
intros W' c' HPc. destruct HPc as (ly' & S' & regs' & mem' & md' & Hc' & HJc & OK' & PO' & HPR & HQ).
destruct HQ as (HPerm & _ & HG2).
exists ly', S', (udrop U3 (rd_heads Ddoc)), regs', mem', md'.
split; [exact Hc'|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HPR|].
intros HJ' HARU'.
assert (ER : forall n, (18 <= n <= 27)%nat -> ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hn; exact (crtD2pf_reg E crtD2_sc35 regsC regs' (crt_extra cx) n HSV Hn RG HPR)).
(* the heads after the call: each one's block is still live (it is no head of Ddoc) *)
assert (HFH' : FSupoisonU.fs_heads B ly' S' (udrop U3 (rd_heads Ddoc))).
{ intros r Hr. rewrite crtD2pf_udrop_eq in Hr. apply filter_In in Hr as (HrU & Hnd). cbv beta in Hnd.
  destruct (HFH r HrU) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m. split; [|exact Hm16].
  apply (Permutation_in _ HPerm) in Hm. apply in_app_or in Hm as [Hm | Hm]; [exfalso | exact Hm].
  unfold rd_hblocks in Hm. apply in_map_iff in Hm as ([a kk] & Ea & Hak). cbn [fst snd] in Ea.
  assert (Hr' : In r (rd_heads Ddoc)).
  { destruct r as [r1 r2]. cbn [fst snd] in E16, Ea. subst r2. injection Ea as Ea1 Ea2.
    unfold rd_heads. apply in_map_iff. exists (a, kk). cbn [fst snd]. rewrite Ea1. split; [reflexivity | exact Hak]. }
  rewrite (crtD2pf_hd_in_true _ _ Hr') in Hnd. cbn in Hnd. discriminate. }
(* the footprint's object part *)
assert (HFR : forall a, inFP [(crt_F cx + 0x20, crt_F cx + 0x20 + 56)] a ->
  frame_addr ly3 3 (c_pos cx) <= a < frame_addr ly3 3 (c_pos cx) + 512).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [rewrite EFa; lia | destruct (inFP_nil a Ha)]. }
assert (HKt : ~ In (c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD) (rd_hblocks Ddoc)).
{ apply HKin. apply in_or_app. right. unfold crtD2_L4. cbv zeta. cbn [In]. left. reflexivity. }
assert (HKb : ~ In (back - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) (rd_hblocks Ddoc)).
{ apply HKin. apply in_or_app. right. unfold crtD2_L4. cbv zeta. cbn [In]. right. right. right. left. reflexivity. }
unfold crtD2_INV_36. cbv zeta.
change (ms_mem (mkst regs' (Z_to_bv 64 0x822bc) mem' (seg_rom tfibsegs))) with mem'.
exists same, nsame, back, (live - rd_sum Ddoc), peak, cnt.
split; [rewrite (ER 24%nat ltac:(lia)); exact E24|].
split; [rewrite (ER 25%nat ltac:(lia)); exact E25|].
(* the blocks: Ddoc's are gone *)
split.
{ unfold crtD2_blocks. apply (Permutation_app_inv_l (rd_hblocks Ddoc)).
  eapply Permutation_trans; [apply Permutation_sym; exact HPerm|].
  eapply Permutation_trans; [exact HPK | apply Permutation_app_comm]. }
split; [exact HUD|].
split; [exact HFH'|].
split.
{ exact (crtD2pf_rblock_kept SK B (STK_pj_free 2) (spZ regsC) (EV_pj_free Ddoc) (c_pos cx)
    [(crt_F cx + 0x20, crt_F cx + 0x20 + 56)] (rd_hblocks Ddoc) ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
    HJc HARU OK' PO' Hin3 HFR HDh HKt HTX'). }
split.
{ exact (crtD2pf_rblock_kept SK B (STK_pj_free 2) (spZ regsC) (EV_pj_free Ddoc) (c_pos cx)
    [(crt_F cx + 0x20, crt_F cx + 0x20 + 56)] (rd_hblocks Ddoc) ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
    HJc HARU OK' PO' Hin3 HFR HDh HKb HBK'). }
split; [exact HG2|].
split; [exact (crt_rom SK B IMG cx (k + EV_pj_free Ddoc) ly' S' _ W' mem' md' HB HJ' HARU')|].
split; [lia|].
split; [exact HC|].
lia.
Qed.

Lemma crtD2_seg35 : crt_from SK B crt_ss36 (crtD2_INV_36 B) -> crt_from SK B crt_ss35 (crtD2_INV_35 B).
Proof.
intros NEXT.
destruct crtD2_site35 as (HCS & _).
exact (crt_seg_call SK B 0x822b4 A_pj_free 0x822bc crtD2_sc35 (crtD2_INV_35 B) (crtD2_INV_36 B) (STK_pj_free 2)
  crtD2_run35 HCS ltac:(lia) eq_refl (proj1 crtD2_stk_pos) crtD2_stk_pj_free crtD2_hcall35 NEXT).
Qed.
End s35.
