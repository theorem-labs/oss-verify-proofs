(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its numbers changed; 154 of its 207 lines of code are new or changed and 1639 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the CALL-SITE machinery shared by every call
   the arms make (put of '[' / '{' / ',' / the separator, indent, put_string of a key, write_value of an item), over
   the loop invariant of lib/A/ZZwv_inv.v:
   - wvc_sem_run: a run between two calls writes write_value's own frame only, so the writer facts carry over;
   - the resumed state's regions and shadow entries (the node at atom 9, the object's key slot) from the facts;
   - the env change at a resume: the frame chunks name only atoms that every run and every callee keeps.
   Template (segmentation of the arm into call sites; not a copied proof): the bespoke ASan proof
   a working branch lib/A/Prog/write_value_cont.v (wvc_fi_munch 480-492, wvc_fi_same 494-505,
   wvc_callpre 564-578); the port-line call composition pjw_put_call (lib/A/FSW_pj_write.v,
   a working branch b6c5b22a453, 1925-2258).
   Rule 24: no function proved here (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= a run that writes write_value's own frame only ================= *)
(* the chain clause puts o at or above the entry sp *)
Lemma wvc_sem_o_sp : forall F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st -> wf_sp F + 8 <= wf_o F.
Proof.
intros F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HC & _).
destruct HC as [(E & _) | (L & _)]; lia.
Qed.

Lemma wvc_sem_run : forall F ly0 S0 U0 W0 mem0 regs0 ly S U W m m' md' buf st,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st ->
  ARU tfibsegs B ly S U W m' md' ->
  (forall x : word, ~ (wf_sp F - WVC_F <= bv_unsigned x < wf_sp F) -> rdW W m' x = rdW W m x) ->
  alloc_ceiling <= wf_sp F - WVC_F -> wf_o F + 32 <= 2 ^ 64 -> wf_ot F <= 2 ^ 64 ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W m' buf st.
Proof.
intros F ly0 S0 U0 W0 mem0 regs0 ly S U W m m' md' buf st HSEM HARU' HFR Hlo Hhi Hot.
pose proof (wvc_sem_o_sp F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st HSEM) as Hosp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HARU') as HAR'.
set (sp := wf_sp F) in *.
assert (HWF : WVC_F = 176) by reflexivity.
(* the restricted memory outside the frame, at an address *)
assert (MR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - WVC_F <= a < sp) ->
  rdW W m' (Z_to_bv 64 a) = rdW W m (Z_to_bv 64 a)).
{ intros a Ha Hn. apply HFR. rewrite unsigned_lit_small by lia. exact Hn. }
assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - WVC_F <= a < sp) ->
  mbyte tfibsegs (rdW W m') a = mbyte tfibsegs (rdW W m) a).
{ intros a Ha Hn. unfold mbyte. rewrite (MR a Ha Hn). reflexivity. }
assert (AVB : zwk_avb W m m').
{ intros a Ha. apply aview_eq_of. apply MR; [lia | unfold WVC_F in *; lia]. }
assert (AVS : forall a, sp <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U m') a = aview tfibsegs (w_H W) (unpoison U m) a).
{ intros a Ha.
  pose proof (zwk_p_stack_not_ush B ly S U W m' md' a HARU' ltac:(unfold WVC_F in *; lia)) as NU.
  rewrite (aview_unpoison_out tfibsegs _ U m' a NU), (aview_unpoison_out tfibsegs _ U m a NU).
  apply aview_eq_of. apply MR; [lia | lia]. }
destruct HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN & HB0 &
  HRO & H8 & HC & HU0).
pose proof HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
assert (VM : forall a n v, sp <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W m') a n v).
{ intros a n v Ha Hn Hv i Hi. rewrite (MB (a + Z.of_nat i) ltac:(lia) ltac:(lia)). exact (Hv i Hi). }
unfold wvc_sem.
split.
{ (* the out-object *)
  unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [exact Hotop|]. split.
  { intros i Hi. destruct (HOW i Hi) as [Hw Hpr]. split.
    - exact (writable_at_eq tfibsegs _ _ (wf_o F + i) (MR (wf_o F + i) ltac:(lia) ltac:(lia)) Hw).
    - destruct Hpr as (Hh & b & Hb). split; [exact Hh|]. exists b.
      pose proof (MR (wf_o F + i) ltac:(lia) ltac:(lia)) as E. unfold mrestrict in E. rewrite Hh in E.
      rewrite E. exact Hb. }
  split; [exact Hbuf64|]. split; [exact Hcap64|].
  split; [exact (VM (wf_o F) 8%nat buf ltac:(lia) ltac:(lia) Vbuf)|].
  split; [exact (VM (wf_o F + 8) 8%nat _ ltac:(lia) ltac:(lia) Vlen)|].
  split; [exact (VM (wf_o F + 16) 8%nat _ ltac:(lia) ltac:(lia) Vcap)|].
  split; [exact (VM (wf_o F + 24) 4%nat _ ltac:(lia) ltac:(lia) Vfail)|].
  split; [exact Hf01|]. split; [exact Htok|].
  destruct Hcase as [Hz | (Hj & HRB & Hlt & HZB)]; [left; exact Hz | right].
  pose proof HRB as (Hin & _ & _ & _).
  destruct (fsw_ablock_low B ly S W _ md' _ _ HAR' Hin) as (A1 & A2 & A3).
  split; [exact Hj|].
  split; [exact (zwk_rblock_avb B ly S W m m' _ md' _ _ HAR' AVB HRB)|].
  split; [exact Hlt|].
  apply (zwk_p_zbytes_avb W m m' _ _ AVB); [unfold HEAD in *; lia | | exact HZB].
  rewrite length_app. cbn [length]. unfold HEAD, req_size in *; lia. }
split.
{ destruct HGL as (peak & Hpk & HG). exists peak. split; [exact Hpk|].
  exact (zwk_fs_glob_avb W m m' _ _ _ _ AVB HG). }
split; [exact HHD|]. split; [exact HUS|]. split; [exact HBS|]. split; [exact HBK|]. split; [exact HCNT|].
split.
{ intros a Ha Hno. destruct (HWK a Ha Hno) as [E1 E2]. split.
  - rewrite (MB a ltac:(lia) ltac:(lia)). exact E1.
  - split; intros Hx.
    + apply (writable_at_eq tfibsegs (rdW W m) (rdW W m') a (MR a ltac:(lia) ltac:(lia))). apply E2. exact Hx.
    + apply E2. apply (writable_at_eq tfibsegs (rdW W m') (rdW W m) a); [symmetry; apply MR; lia | exact Hx]. }
split.
{ apply (zwk_pj_node_avb B ly S W m m' _ md' _ _ _ _ (wf_D F) HAR' AVB HPO HUL); [|exact HN].
  intros a k Hak. exact Hak. }
split; [exact (zwk_pobj_avb B ly S W m m' _ md' _ HAR' AVB HPO)|].
split.
{ intros x Hx. rewrite <- (HNB x Hx). apply HFR. destruct (fsw_pobj_low B ly S W _ md' m (wf_v F) HAR' HPO) as (L1 & L2).
  unfold WVC_F in *. lia. }
split; [exact (zwk_ublocks_avb B ly S W m m' _ md' _ HAR' AVB HUL)|].
split; [exact HD|]. split; [exact HROOT|]. split; [exact HBIN|]. split; [exact HB0|].
split; [exact (zwk_arodata_avb B W m m' AVB HRO)|].
split.
{ rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U m)) _ (wf_o F - 8)); [exact H8|].
  intros k Hk. apply AVS. lia. }
split; [|exact HU0].
destruct HC as [HC1 | (H16 & nfp & Hnfp & Hend)]; [left; exact HC1 | right].
split; [exact H16|]. exists nfp. split; [|exact Hend].
rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U m)) _ (wf_o F - 16)); [exact Hnfp|].
intros k Hk. apply AVS. lia.
Qed.

(* ================= the resumed state ================= *)
(* the root node's region based at the resumed s1 (atom 9): the field chunks from pj_hdr (FSW_write_value.wv_node_ok's
   proof at atom 9) *)
Lemma wvc_node_ok : forall E m v ty num str kids keys n cap,
  PjStruct.pj_hdr tfibsegs m v ty num str kids keys n cap ->
  ew E 9 = Z_to_bv 64 v -> ew E (xatom 0) = Z_to_bv 64 str -> ew E (xatom 1) = Z_to_bv 64 kids ->
  ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 3) = Z_to_bv 64 n ->
  YP09.region_ok tfibsegs E m (wvc_node ty).
Proof.
intros E m v ty num str kids keys n cap ((H8 & Hlo & Hhi & _) & Hty & _ & Hstr & Hkids & Hkeys & Hn & _) E9 E0 E1 E2 E3.
unfold YP09.region_ok, wvc_node.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, (unsigned_lit_small v) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- apply (fsw_pj_chunk4 tfibsegs E m v 0 _ ty); [rewrite Z.add_0_r; exact Hty | reflexivity].
- apply (fsw_pj_chunk8 tfibsegs E m v 16 _ str); [exact Hstr | rewrite fsw_SOff0; exact E0].
- apply (fsw_pj_chunk8 tfibsegs E m v 24 _ kids); [exact Hkids | rewrite fsw_SOff0; exact E1].
- apply (fsw_pj_chunk8 tfibsegs E m v 32 _ keys); [exact Hkeys | rewrite fsw_SOff0; exact E2].
- apply (fsw_pj_chunk8 tfibsegs E m v 40 _ n); [exact Hn | rewrite fsw_SOff0; exact E3].
Qed.

(* the object's key slot keys + 8 * i, holding the key pointer *)
Lemma wvc_keyR_ok : forall E m ke key,
  PjStruct.pj_u64 tfibsegs m ke key -> ew E (xatom 18) = Z_to_bv 64 ke -> ew E (xatom 19) = Z_to_bv 64 key ->
  0 <= ke -> ke + 8 <= 2 ^ 64 ->
  YP09.region_ok tfibsegs E m wvc_keyR.
Proof.
intros E m ke key Hu E18 E19 H0 H1.
unfold YP09.region_ok, wvc_keyR.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E18, (unsigned_lit_small ke) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (fsw_pj_chunk8 tfibsegs E m ke 0 _ key); [rewrite Z.add_0_r; exact Hu | rewrite fsw_SOff0; exact E19].
Qed.

(* the shadow-base atom of a T env, read as a number *)
Lemma wvc_U32 : forall E, ew E 32 = Z_to_bv 64 SHADOW_OFF -> U E fs_Bx = SHADOW_OFF.
Proof.
intros E H. unfold fs_Bx. rewrite U_SOff, H, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* the root node's shadow entry at atom 9: addressable, apart from the shadow band (wv_pobj's argument) *)
Lemma wvc_node_sh : forall ly S (W : world tfibsegs) memA md mem v E,
  AR tfibsegs B ly S W memA md -> FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  U E fs_Bx = SHADOW_OFF -> U E (SOff 9 0) = v ->
  shent_ok tfibsegs fs_Bx E (rdW W mem) (mkSHE 9 0 56).
Proof.
intros ly S W memA md mem v E HAR HPO HB Hv.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HPO as (Hpl & _).
destruct Hpl as [((cid & pos & Hin & Hc0 & Hal & Hlo & Hhi) & H8 & HRA) | ((b & m & Hin & Hlo & Hhi) & H8 & HRA)].
- split.
  + cbn [she_m she_lo she_hi]. rewrite Hv, Z.add_0_r.
    exact (obl_of_range tfibsegs (w_H W) mem E fs_Bx v 56 v 56 HRA HB ltac:(lia) ltac:(lia)).
  + destruct (shent_app_of_frame tfibsegs B LAWS ly S W memA md E fs_Bx 9 v cid pos 0 56 (rdW W mem) HAR Hin HB Hv
      ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Happ].
    exact Happ.
- split.
  + cbn [she_m she_lo she_hi]. rewrite Hv, Z.add_0_r.
    exact (obl_of_range tfibsegs (w_H W) mem E fs_Bx v 56 v 56 HRA HB ltac:(lia) ltac:(lia)).
  + destruct (shent_app_of_block tfibsegs B LAWS ly S W memA md E fs_Bx 9 v b m 0 56 (rdW W mem) HAR Hin HB Hv
      ltac:(unfold HEAD in Hlo; lia) ltac:(lia) ltac:(lia)) as [_ Happ].
    exact Happ.
Qed.

(* the key slot's shadow entry: inside the user bytes of the live keys block *)
Lemma wvc_keyR_sh : forall ly S UU (W : world tfibsegs) mem md ke E P q,
  ARU tfibsegs B ly S UU W mem md -> fs_heads B ly S UU ->
  In (P, q) (ablocks B ly S) -> P + 16 <= ke -> ke + 8 <= P + req_size q ->
  U E fs_Bx = SHADOW_OFF -> U E (SOff (xatom 18) 0) = ke ->
  shent_ok tfibsegs fs_Bx E (rdW W mem) (mkSHE (xatom 18) 0 8).
Proof.
intros ly S UU W mem md ke E P q HARU HFH Hin H1 H2 HB Hk.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_block_body_addressable B ly S UU W mem md P q ke 8 HARU HFH Hin H1 ltac:(lia) H2) as HRA.
split.
- cbn [she_m she_lo she_hi]. rewrite Hk, Z.add_0_r.
  exact (obl_of_range tfibsegs (w_H W) mem E fs_Bx ke 8 ke 8 HRA HB ltac:(lia) ltac:(lia)).
- destruct (shent_app_of_block tfibsegs B LAWS ly S W (unpoison UU mem) md E fs_Bx (xatom 18) ke P q 0 8 (rdW W mem)
    (proj1 HARU) Hin HB Hk ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Happ].
  exact Happ.
Qed.

(* ---- a loop state's register setting and its two conditions, from the plain resumed state ---- *)
Lemma wvc_st_ok_setr : forall E (l : list (bv 5 * sv)) ss ms,
  st_ok tfibsegs E ss ms ->
  Forall (fun q => fst q <> 0%bv /\ YK11.getr (ms_regs ms) (fst q) = sv_denot E (snd q)) l ->
  st_ok tfibsegs E (wvc_setr ss l) ms.
Proof.
intros E l. induction l as [|q l IH]; intros ss ms HS HF.
- exact HS.
- inversion HF as [|q0 l0 (Hq0 & Hq) HF' Eq]; subst.
  change (wvc_setr ss (q :: l)) with
    (wvc_setr (mkSS (ss_pc ss) (sr_set (ss_regs ss) (fst q) (snd q)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) l).
  apply IH; [|exact HF'].
  exact (st_ok_set_reg tfibsegs E ss ms (fst q) (snd q) HS Hq0 Hq).
Qed.

End C.
