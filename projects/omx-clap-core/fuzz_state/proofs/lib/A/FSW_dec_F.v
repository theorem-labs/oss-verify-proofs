(* preset_base64_decode (fs.asan 0x8481c), part F of the walk (a Theorem Labs lane): the call of fuzz_free on a
   refused text and the return, from FSW_dec_defs.v's dec_at_free into dec_post's second arm (cnt <> fail, the text
   does not decode, q's block freed, two events: the fuzz_malloc of part E and this fuzz_free).
   Steps: fuzz_free_spec's p <> 0 arm at the call (fpreU from the caller's journal by FSW_ret.fsw_fpreU_atFP; the callee's
   chain is achain_low since s0 = DEC_WSMASK < alloc_ceiling); the resume at DEC_RA_FREE 0x8497c by the kit step
   FSW_K3.fsw_after_callFPU_args (journal and ARU after the call; the symbolic state is built by FSW_rres
   fsw_resume_after_rtU_args_chunks over YCbq.ajournal_sub_init's journal at the entry sp, so the frame region has the
   concrete size 112 in both placements of *lenp); the engine's run 0x8497c .. 0x849bc (MEASURED: the epilogue reloads
   s11..s0 and ra from the frame, a0 = 0, no store, no shadow load); FSW_ret.fsw_retU into dec_post's second arm.
   SCRATCH part file during the walk; a Theorem Labs lane integrates it into lib/A/FSW_preset_base64_decode.v. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- list helpers ---- *)
Lemma decF_snoc_notin : forall {X Y : Type} (R : Y -> Y -> Prop) (f : X -> Y) (l : list X) (x : X),
  pairwise R (map f (l ++ [x])) -> ~ R (f x) (f x) -> ~ In x l.
Proof.
intros X Y R f l. induction l as [|y l IH]; intros x HP HR Hin; [destruct Hin|].
cbn [app map pairwise] in HP. destruct HP as [HF HP].
destruct Hin as [<-|Hin].
- apply HR. rewrite Forall_forall in HF. apply HF. rewrite map_app. apply in_or_app. right. left. reflexivity.
- exact (IH x HP HR Hin).
Qed.
Lemma decF_snoc_split : forall {X : Type} (l1 l2 l : list X) (x : X),
  l1 ++ x :: l2 = l ++ [x] -> ~ In x l -> l1 = l /\ l2 = [].
Proof.
intros X l1 l2 l x. revert l1 l. induction l2 as [|y l2' _] using rev_ind; intros l1 l E Hn.
- apply app_inj_tail in E as [E _]. split; [exact E | reflexivity].
- exfalso. rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as [E _]. apply Hn. rewrite <- E.
  apply in_or_app. right. left. reflexivity.
Qed.
Lemma decF_pw_app : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) (x y : X),
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
cbn [app pairwise] in HP. destruct HP as [HF HP]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
- exact (IH l2 x y HP Hx Hy).
Qed.

(* the last PT_LOAD of fs.asan, [0xa1000, 0x5fd000) (MEASURED: tfibsegs's fourth segment), holds fuzz/alloc.c's four
   statics (FS_PSTAT_FP) *)
Lemma decF_img : forall a, 659456 <= a < 6279168 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (H : option_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (nth_error tfibsegs 3) = Some (659456, 5619712))
  by (vm_compute; reflexivity).
destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate H].
exists sg. split; [exact (nth_error_In _ _ E)|].
cbn [option_map] in H. injection H as H1 H2. lia.
Qed.

Lemma decF_mbyte_unp : forall (H : word -> bool) (U : list (Z * Z)) (m : word -> option byte) a,
  unpoison U m (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte tfibsegs (mrestrict H (unpoison U m)) a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H U m a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.

(* the resume regions with an empty frame of size f >= 0 are well formed *)
Lemma decF_wf0 : forall f, 0 <= f -> regions_wf (fsT_ret_regions f [] []) = true.
Proof.
intros f Hf. unfold fsT_ret_regions. cbn [app regions_wf].
replace (region_wf fs_got_region) with true by (vm_compute; reflexivity).
replace (region_wf (fs_bcell_region 32)) with true by (vm_compute; reflexivity).
unfold region_wf, fstk_ret. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
rewrite (proj2 (Z.leb_le 0 f) Hf), (proj2 (Z.leb_le f f) (Z.le_refl f)), (proj2 (Z.leb_le 0 0) (Z.le_refl 0)).
rewrite !orb_true_r. reflexivity.
Qed.

(* split a hypothesis along its right-nested conjunction spine *)
Ltac decF_split H :=
  lazymatch type of H with
  | _ /\ _ => let a := fresh "HD" in destruct H as [a H]; decF_split H
  | _ => idtac
  end.

(* ---- the resumed frame at 0x8497c: base b = entry sp - 112 (atom 2 of fss_retT); word 1 + j (offset 8 + 8 j) holds the
   entry value of dec_saved's j-th register, extra atom 33 + j (xatom j) of the env Ereg regs (fs_extraT ++ decF_xs) ---- *)
Definition decF_cs : list YP09.chunk :=
  map (fun j => YP09.mkChunk (8 + 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 13).
Definition decF_xs (regs0 : bvmap 5 word) : list word := map (YK11.getr regs0) dec_saved.

Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* fuzz_free's contract (owner ALLOC, S0 lib/A/FSH_Fn_alloc.v fuzz_free_spec) *)
Hypothesis HFREE : fuzz_free_spec tfibsegs B.

Lemma dec_free_stage : dec_stage_free B.
Proof.
unfold dec_stage_free.
intros d q W3 ly3 S3 U3 regs3 mem3 md3 k3 HD HAF.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSS as [HGOT HCELL].
assert (HHEAD : HEAD = 16) by reflexivity.
assert (HDECF : DEC_F = 112) by reflexivity.
assert (HSTKd : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by (vm_compute; reflexivity).
assert (HSTKf : STK_fuzz_free = ltac:(let v := eval vm_compute in STK_fuzz_free in exact v)) by (vm_compute; reflexivity).
assert (Hdsp : d_sp d = spZ (d_regs d)) by reflexivity.
assert (HSTKJ : d_STKJ d = STK_preset_base64_decode + (d_ot d - spZ (d_regs d))) by reflexivity.
assert (HEVd : EV_preset_base64_decode = 2) by reflexivity.
(* ---- the entry facts ---- *)
(* split dec_entry_ok along its conjunction spine and take the three facts used by name by their types (the other
   conjuncts stay in context for lia), so a conjunct added to dec_entry_ok does not move them *)
unfold dec_entry_ok in HD. cbv zeta in HD. decF_split HD.
lazymatch goal with Hx : fpreU tfibsegs B STK_preset_base64_decode _ _ _ _ _ _ _ _ |- _ => rename Hx into HPRE end.
lazymatch goal with Hx : fs_glob tfibsegs (d_W d) (d_mem d) _ _ _ _ |- _ => rename Hx into HGLOB0 end.
lazymatch goal with Hx : (d_FP d = FS_PSTAT_FP /\ _) \/ _ |- _ => rename Hx into HPL end.
destruct HPRE as (HPREU & _).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hsp16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HGLOB0 as (_ & _ & _ & _ & Hlive0 & _ & Hcnt0 & _).
assert (HOT : spZ (d_regs d) <= d_ot d /\ d_ot d mod 16 = 0 /\ d_ot d <= 2 ^ 47).
{ destruct HPL as [(_ & H1 & H2 & H3 & H4 & _) | (_ & H1 & _)];
    [split; [lia | split; [exact H3 | lia]] | rewrite H1; split; [lia | split; [exact Hsp16 | lia]]]. }
destruct HOT as (Hspot & Hot16 & Hot47).
assert (HFPd : d_FP d = FS_PSTAT_FP \/ d_FP d = FS_PSTAT_FP ++ [(d_lenp d, d_lenp d + 8)])
  by (destruct HPL as [(H & _) | (H & _)]; [left | right]; exact H).
(* ---- the call site ---- *)
unfold dec_at_free in HAF.
destruct HAF as (HJ & HARU3 & -> & EU3 & HH3 & HAB3 & Hq & HRB & Hcf & Hdec & HG3 & R10 & R1 & Rsp & R3 & R4 & R8 & HFR
  & HLS & HKEPT).
unfold dec_J in HJ.
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & _).
pose proof HRB as (_ & _ & Hn0 & _).
assert (Hra3 : raZ regs3 = DEC_RA_FREE) by (unfold raZ; rewrite R1; unfold w64; apply wz; unfold DEC_RA_FREE; lia).
(* the callee's pre from the caller's journal (any FP / own, any start memory), ARU and the image read-only view of
   dec_kept at the call (FSW_ret.fsw_fpreU_atFP) *)
assert (HFPRE : fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 regs3 mem3 md3 []).
{ apply (fsw_fpreU_atFP B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) U3 (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) []
    ly3 S3 W3 mem3 md3 1 regs3 STK_fuzz_free (spZ regs3 - d_ot d) [] HJ HARU3 (proj2 (proj2 (proj2 HKEPT)))).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite R1. apply YK0s.ret_ok_even. unfold w64. rewrite wz by (unfold DEC_RA_FREE; lia). reflexivity.
  - rewrite Hra3. unfold DEC_RA_FREE. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite wz by (unfold DEC_WSMASK; lia). unfold DEC_WSMASK. lia. }
(* the event budget: dec_ev tb = EV_preset_base64_decode = 2 on a text that does not decode *)
assert (HEVt : dec_ev (d_tb d) = 2) by (unfold dec_ev; rewrite Hdec; reflexivity).
assert (HNEV : st_nev S3 + 1 <= EV_MAX) by lia.
(* ---- the call: fuzz_free_spec's p <> 0 arm, U1 = d_U d, U2 = [] ---- *)
eapply SRr_bind.
{ apply (HFREE ly3 S3 U3 W3 regs3 mem3 md3 [] q (d_n d) (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d))
    (d_cnt d + 1) (d_fail d)).
  - exact R10.
  - exact HG3.
  - exact HH3.
  - right. split; [lia|]. exists (d_U d), []. split; [exact EU3|]. split; [exact HFPRE|]. split; [exact HRB | lia].
  - intros _. exact HNEV. }
intros W4 c4 Hle4 HR.
destruct HR as [(Hq0 & _) | (_ & U1 & U2 & EU & HPOST)]; [lia|].
unfold apost_baseU, fpostU in HPOST.
destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Hsplit & _ & HG4)).
(* q's head occurs once in U3 (upoison_ok's disjointness), so the callee's U1 ++ U2 is d_U d *)
assert (HXU : ~ In (q - HEAD, HEAD) (d_U d)).
{ pose proof HARU3 as (_ & (_ & PWU) & _). rewrite EU3 in PWU.
  apply (decF_snoc_notin zdisjoint (fun y => y)); [rewrite map_id; exact PWU | cbv beta; unfold zdisjoint; cbn [fst snd]; lia]. }
destruct (decF_snoc_split U1 U2 (d_U d) (q - HEAD, HEAD) ltac:(rewrite <- EU; exact EU3) HXU) as [-> ->].
rewrite app_nil_r in HJc, OK4, PO4.
(* q's block is new since the entry (the blocks are pairwise disjoint at the call) *)
assert (HXB : ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d))).
{ destruct (al_blocks _ _ LAWS ly3 S3 W3 (unpoison U3 mem3) md3 (q - HEAD) (d_n d + HEAD) HAR3
    ltac:(rewrite HAB3; apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & _ & PWB & _).
  rewrite HAB3 in PWB.
  apply (decF_snoc_notin zdisjoint (fun b => (fst b, req_size (snd b))) _ _ PWB).
  cbv beta. unfold zdisjoint. cbn [fst snd].
  pose proof (req_size_pos (d_n d + HEAD) ltac:(lia)) as (RQ1 & _). lia. }
(* the callee's footprint: the statics by the image arm, q's block by the temporary-block arm *)
assert (FPSUB : fsw_fp_sub B (d_ly d) (d_S d) ly3 S3 [] (d_FP d) (FS_PSTAT_FP ++ ablocks_fp [(q - HEAD, d_n d + HEAD)])).
{ intros a (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr].
  - right. right. left. split.
    + exists r. split; [|exact Ha]. destruct HFPd as [-> | ->]; [exact Hr | apply in_or_app; left; exact Hr].
    + unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; apply decF_img; lia.
  - right. left. exists (q - HEAD), (d_n d + HEAD).
    split; [rewrite HAB3; apply in_or_app; right; left; reflexivity|].
    split; [exact HXB|]. cbn [ablocks_fp map In fst snd] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. exact Ha. }
(* ---- the resume at DEC_RA_FREE ---- *)
assert (HE2a : forall xs, bv_unsigned (ew (Ereg regs4 (fs_extraT ++ xs)) 2) = spZ regs4)
  by (intros xs; rewrite (ew_Ereg_nat regs4 (fs_extraT ++ xs) 2 2%bv eq_refl); reflexivity).
assert (Esp : YK11.getr regs4 2 = YK11.getr regs3 2) by exact (HP4 2 ltac:(unfold acallee_saved; lia)).
assert (Esp4 : spZ regs4 = spZ regs3) by (unfold spZ; rewrite Esp; reflexivity).
assert (HWF0 : regions_wf (fsT_ret_regions (d_ot d - spZ regs3) [] []) = true) by (apply decF_wf0; lia).
assert (HPD0 : pairwise_disjoint (Ereg regs4 (fs_extraT ++ [])) (fsT_ret_regions (d_ot d - spZ regs3) [] [])).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite HE2a, Esp4.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
destruct (fsw_after_callFPU_args B (d_STKJ d) (d_ot d) (d_FP d) [] (d_ly d) (d_S d) (d_U d) W3 (d_mem d) (d_md d) (d_W d)
  ly3 S3 U3 mem3 md3 1 STK_fuzz_free (FS_PSTAT_FP ++ ablocks_fp [(q - HEAD, d_n d + HEAD)]) (d_ot d - spZ regs3) regs3
  ly4 S4 (d_U d) W4 regs4 mem4 md4 1 [] [] [] [] DEC_RA_FREE HGOT HCELL HJ HARU3 HJc FPSUB OK4 PO4 HP4
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HWF0 ltac:(constructor) ltac:(constructor) ltac:(constructor) HPD0
  ltac:(first [exact I | constructor | cbn; exact I]))
  as (HJ4 & HARU4 & _).
(* the same journal's window presence, read at the entry sp: the frame [sp - 112, sp) has the size 112 in both
   placements of *lenp *)
pose proof (ajournal_sub_init tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d))
  (d_md d) [] ly4 S4 W4 (unpoison (d_U d) mem4) md4 (1 + 1) STK_preset_base64_decode (spZ (d_regs d)) []
  (spZ (d_regs d) - d_ot d) HJ4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HJr.
(* the callee keeps the bytes above its stack window (the caller's frame and window) and the caller's fake frames *)
pose proof HJc as (_ & Hly4 & _ & _ & _ & Hfrs4 & _ & _ & F1c & _ & _ & F4c & _).
assert (KEEP4 : forall a, alloc_ceiling <= a < 2 ^ 64 -> spZ regs3 <= a ->
  mbyte tfibsegs (mrestrict (w_H W4) mem4) a = mbyte tfibsegs (mrestrict (w_H W3) mem3) a).
{ intros a Ha Ha3. apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly4 S4 (d_U d) W4 mem4 md4 a HARU4) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly3 S3 U3 W3 mem3 md3 a HARU3) by lia.
  apply F1c; lia. }
assert (FKEEP : forall cid pos a, In (cid, pos) (frames (d_S d)) ->
  frame_addr (d_ly d) cid pos <= a < frame_addr (d_ly d) cid pos + fs_frame_bytes cid ->
  mbyte tfibsegs (mrestrict (w_H W4) mem4) a = mbyte tfibsegs (mrestrict (w_H W3) mem3) a).
{ intros cid pos a Hcp Ha.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR3 Hly4) as (_ & Efa4 & _).
  assert (Hcp3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact Hcp).
  assert (Hcp4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact Hcp3).
  assert (Ha3 : frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid) by (rewrite Efa3; exact Ha).
  assert (Ha4 : frame_addr ly4 cid pos <= a < frame_addr ly4 cid pos + fs_frame_bytes cid) by (rewrite Efa4; exact Ha3).
  pose proof (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR3 Hcp3) as (_ & _ & HFB3 & _).
  pose proof (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HARU4) Hcp4) as (_ & _ & HFB4 & _).
  pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (PWS & HFF).
  rewrite Forall_forall in HFF. pose proof (HFF (cid, pos) Hcp3) as (Hf1 & Hf2). cbn [fst snd] in Hf1, Hf2.
  assert (NFP : ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(q - HEAD, d_n d + HEAD)]) a).
  { intros (r & Hr & Hrr). apply in_app_or in Hr as [Hr|Hr].
    - apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR3
        (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hcp3 Ha3))))))).
      unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hrr; apply decF_img; lia.
    - cbn [ablocks_fp map In fst snd] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hrr.
      assert (Z : zdisjoint (q - HEAD, req_size (d_n d + HEAD)) (frame_addr ly3 cid pos, fs_frame_bytes cid)).
      { apply (decF_pw_app zdisjoint _ _ _ _ PWS).
        - apply in_map_iff. exists (q - HEAD, d_n d + HEAD). split; [reflexivity|].
          rewrite HAB3. apply in_or_app. right. left. reflexivity.
        - apply in_map_iff. exists (cid, pos). split; [reflexivity | exact Hcp3]. }
      unfold zdisjoint in Z. cbn [fst snd] in Z. lia. }
  assert (AV : aview tfibsegs (w_H W4) (unpoison (d_U d) mem4) a = aview tfibsegs (w_H W3) (unpoison U3 mem3) a).
  { apply (F4c cid pos a Hcp3); [left; unfold frame_rng, in_zr; cbn [fst snd]; lia | exact NFP]. }
  assert (U3a : unpoison U3 mem3 (Z_to_bv 64 a) = mem3 (Z_to_bv 64 a)).
  { apply unpoison_out. destruct (in_ush U3 (bv_unsigned (Z_to_bv 64 a))) eqn:EU0; [exfalso|reflexivity].
    destruct (ush_facts tfibsegs B ly3 S3 U3 W3 mem3 md3 _ HARU3 EU0) as (Hown & _).
    rewrite (wz a ltac:(lia)) in Hown. exact (proj2 (HFB3 a Ha3) Hown). }
  assert (U4a : unpoison (d_U d) mem4 (Z_to_bv 64 a) = mem4 (Z_to_bv 64 a)).
  { apply unpoison_out. destruct (in_ush (d_U d) (bv_unsigned (Z_to_bv 64 a))) eqn:EU0; [exfalso|reflexivity].
    destruct (ush_facts tfibsegs B ly4 S4 (d_U d) W4 mem4 md4 _ HARU4 EU0) as (Hown & _).
    rewrite (wz a ltac:(lia)) in Hown. exact (proj2 (HFB4 a Ha4) Hown). }
  rewrite <- (decF_mbyte_unp (w_H W4) (d_U d) mem4 a U4a), <- (decF_mbyte_unp (w_H W3) U3 mem3 a U3a).
  exact (mbyte_of_aview tfibsegs _ _ _ _ a AV). }
(* the resumed symbolic state: the 13 saved words read on the memory after the call *)
assert (HS : st_ok tfibsegs (Ereg regs4 (fs_extraT ++ decF_xs (d_regs d))) (fss_retT DEC_RA_FREE 112 decF_cs [] [])
  (restrict (w_H W4) (YK11.mkst regs4 (Z_to_bv 64 DEC_RA_FREE) mem4 (YK11.seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args_chunks B STK_preset_base64_decode (spZ (d_regs d)) [] ly4 S4 W4 (unpoison (d_U d) mem4)
    md4 [] ly4 S4 (d_U d) W4 mem4 md4 0 regs4 112 (decF_xs (d_regs d)) decF_cs [] [] DEC_RA_FREE HGOT HCELL HJr HARU4).
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_forall. intros c Hc. unfold decF_cs in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error dec_saved j) as [r|] eqn:Ej; [|apply nth_error_None in Ej; cbn [length dec_saved] in Ej; lia].
    pose proof (HFR j r Ej) as V.
    apply (chunk_ok_val tfibsegs _ _ _ _ 8 _ (bv_unsigned (YK11.getr (d_regs d) r))).
    + rewrite Z_to_bv_bv_unsigned. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
      cbn [nth fs_extraT app]. unfold decF_xs. apply nth_error_nth. rewrite nth_error_map, Ej. reflexivity.
    + pose proof (u64_range (YK11.getr (d_regs d) r)). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + intros i Hi. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hi.
      rewrite KEEP4 by lia.
      replace (spZ (d_regs d) - 112 + (8 + 8 * Z.of_nat j) + Z.of_nat i)
        with (d_sp d - DEC_F + 8 + 8 * Z.of_nat j + Z.of_nat i) by lia.
      exact (V i Hi).
  - constructor.
  - apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite HE2a, Esp4.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - first [exact I | constructor | cbn; exact I]. }
(* ---- the run 0x8497c .. 0x849bc and the return ---- *)
rewrite R1. unfold w64.
fsw_aj_runU fsw_wr_tbl_ok HS HJ4 HARU4.
- (* the writes of the run: only the frame, inside the journal's window *)
  cbv [fss_retT fsT_ret_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ (d_regs d) - 112 - d_ot d);
    [reflexivity | rewrite HE2a, Esp4; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- (* at the return instruction *)
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  (* every byte outside the frame [sp - 112, sp) is the byte after the call *)
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 112 <= a < spZ (d_regs d)) ->
    ms_mem ms (Z_to_bv 64 a) = mem4 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
    cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      try (rewrite HE2a, Esp4 in Hr); lia. }
  assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 112 <= a < spZ (d_regs d)) ->
    mrestrict (w_H W4) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W4) mem4 (Z_to_bv 64 a))
    by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
  assert (MB5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 112 <= a < spZ (d_regs d)) ->
    mbyte tfibsegs (mrestrict (w_H W4) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W4) mem4) a)
    by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
  assert (SB : same_below mem4 (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
  eapply SRr_mono.
  2:{ intros W5 c5 _ HP5. unfold dec_post. cbv beta zeta. right. left.
      split; [exact Hcf|]. split; [exact Hdec|]. exact HP5. }
  eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
  + exact HS.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + rewrite (fsw_reg_extra (w_H W4) regs4 (fs_extraT ++ decF_xs (d_regs d)) _ ms 1%bv 13 HS
      ltac:(vm_compute; reflexivity)).
    cbn [nth app fs_extraT decF_xs map dec_saved]. exact Hra.
  + exact HJ4.
  + exact HARU4.
  + lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      apply (fsw_preserved (w_H W4) _ ssf ms (d_regs d) (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
      [vm_compute; reflexivity|]
    end.
    intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      first
      [ apply fsw_sp_back; rewrite HE2a, Esp4; lia
      | rewrite fsw_SOff0, (ew_Ereg_nat regs4 _ 3 3%bv eq_refl),
          (fsw_pres regs3 regs4 3%bv HP4 ltac:(unfold acallee_saved; change (bv_unsigned 3%bv) with 3; lia)), R3;
        reflexivity
      | rewrite fsw_SOff0, (ew_Ereg_nat regs4 _ 4 4%bv eq_refl),
          (fsw_pres regs3 regs4 4%bv HP4 ltac:(unfold acallee_saved; change (bv_unsigned 4%bv) with 4; lia)), R4;
        reflexivity
      | rewrite fsw_SOff0;
        lazymatch goal with
        | |- ew _ ?n = _ => let j := eval vm_compute in (n - 32)%nat in change n with (32 + j)%nat
        end;
        rewrite ew_Ereg_extra; reflexivity ].
  + intros mat5. cbv beta.
    split; [unfold w64; exact (fsw_reg_lit (w_H W4) _ _ ms 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split.
    { (* q's block is the last one of the call-site list and is not in the entry's (HXB): the free removes exactly it *)
      destruct Hsplit as (l1 & l2 & E3 & E4). rewrite E4.
      destruct (decF_snoc_split l1 l2 (ablocks B (d_ly d) (d_S d)) (q - HEAD, d_n d + HEAD)
        ltac:(rewrite <- E3; exact HAB3) HXB) as [-> ->].
      apply app_nil_r. }
    split.
    { (* the window bytes outside *lenp (vacuous when ot = sp) *)
      intros a Ha Hna. pose proof HKEPT as (_ & WK3 & _).
      destruct (WK3 a Ha Hna) as [WK3m _].
      split.
      - rewrite MB5 by lia. rewrite KEEP4 by lia. exact WK3m.
      - split; intros _; apply (apresent_writable tfibsegs).
        + apply (fsw_apresent_unpoison B ly4 S4 (d_U d) W4 (ms_mem ms) _ a HARU4); [lia|]. apply Hpres5. lia.
        + destruct HPL as [(_ & _ & _ & _ & _ & HPR & _) | (_ & Hot & _)]; [apply HPR; lia | lia]. }
    split.
    { (* *lenp keeps its value: a window byte (decode_spec) or a byte of a caller fake frame (decode_spec_ff) *)
      pose proof HKEPT as (VL3 & _). intros i Hi.
      destruct HPL as [(_ & Hspl & Hlot & _) | (_ & Hot & (cid & pos & Hcp & Hfr) & _)].
      - rewrite MB5 by lia. rewrite KEEP4 by lia. exact (VL3 i Hi).
      - pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR0) as (_ & HFF0).
        rewrite Forall_forall in HFF0. pose proof (HFF0 (cid, pos) Hcp) as (Hf1 & Hf2). cbn [fst snd] in Hf1, Hf2.
        pose proof (Hfr (d_lenp d + Z.of_nat i) ltac:(lia)) as Hfa. unfold frame_rng, in_zr in Hfa. cbn [fst snd] in Hfa.
        rewrite MB5 by lia. rewrite (FKEEP cid pos _ Hcp Hfa). exact (VL3 i Hi). }
    (* the globals: g_live back to live, g_count + 1 *)
    pose proof HG4 as HG4'. replace (d_live d + d_n d - d_n d) with (d_live d) in HG4' by lia.
    rewrite Z.mod_small by lia.
    exact (fs_glob_below W4 mem4 (ms_mem ms) _ _ _ _ SB HG4').
Qed.
End P.
