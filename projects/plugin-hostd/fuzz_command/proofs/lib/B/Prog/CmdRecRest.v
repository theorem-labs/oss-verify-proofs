(* The remaining per-binary facts of fuzz_command.asan-ubsan (the B twin of lib/A/Prog/CmdRecRest.v): the whole of
   aread_ok for an image range (cmd_aread_ok_img),
   the read-only bytes apart from the program's statics (cmd_ro_prog_apart, cmd_prog_img), facts kept across a
   callee (cmd_ro_kept, cmd_atail_kept, cmd_rodata_kept: the names the recorder-B walks carry), the
   reader-to-memory bridge val_mem_of_aval, and for the pinned listing the PALib record (cmd_palib) and CmdObj.v's
   bridges (cmd_val_objs_PB, cmd_val_his_PB, cmd_sig_prog_PB, cmd_val_relro_PB). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YG05 YG0t YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YCeg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdObj CmdBase CmdRo CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaLibF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Every lemma below is closed over exactly `segs B LAWS HB`, the [IMG] ones over `segs B LAWS HB IMG`
   (the Section form of the per-binary facts' statements). *)
Section rest. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : CmdBSyms B.
(* a literal's word tail from cmd_ro_ok *)
Lemma cmd_tail_vis : forall (W : world segs) mem e, cmd_ro_ok (aview segs (w_H W) mem) -> In e cmd_ro_ends ->
atail_vis segs W mem e.
Proof using LAWS HB. intros W mem e [_ HT] He a Ha. exact (HT e He a Ha). Qed.
(* the whole of aread_ok for an image range whose bytes the caller knows to be present *)
Lemma cmd_aread_ok_img : forall stk ly S (W : world segs) regs mem md x n,
ecall_pre_stk segs B stk ly S W regs mem md ->
(forall a, x <= a < x + n -> aview segs (w_H W) mem a <> None) ->
cmd_rd_b x n = true -> aread_ok segs stk W regs mem x n.
Proof using LAWS HB.
intros stk ly S W regs mem md x n HP Hv H. unfold cmd_rd_b in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H0 H1]. apply Z.leb_le in H1. apply Z.leb_le in H3. apply Z.leb_le in H0.
pose proof HP as ((HAR & _) & _).
unfold aread_ok, kLowMemEnd in *. change (2 ^ 63) with 9223372036854775808. change (2 ^ 32) with 4294967296.
split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros a Ha. split; [exact (Hv a Ha)|]. apply (cmd_stk_above segs B stk ly S W regs mem md a HP). unfold kLowMemEnd. lia.
- split; [left; unfold kLowMemEnd; lia|]. split; [exact (cmd_addressable_chk segs B LAWS HB ly S W mem md x n HAR H4)|].
  intros Hn. apply orb_prop in H5 as [H5|H5]; [apply Z.leb_le in H5; lia | exact (cmd_hull_vis_chk segs B LAWS HB ly S W mem md x n HAR H5)].
Qed.
Hypothesis IMG : cmd_img_facts segs B.
(* read-only bytes are image bytes outside the program's statics (in the record's (lo, len) form: ts_prog makes it
   as_prog_static B) *)
Lemma cmd_ro_prog_apart : forall a, in_roP segs CMD_RLO CMD_RHI a ->
in_img segs a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC.
Proof using LAWS HB IMG.
intros a Ha. pose proof (cif_ro_end _ _ IMG a Ha) as Ba. split.
- destruct Ha as [(s & Hs & _ & Hr)|Hr]; [exists s; split; [exact Hs | exact Hr] | exact (cif_relro_img _ _ IMG a Hr)].
- intros HE. apply Exists_exists in HE as (r & Hr & Har). unfold TFIB_PROG_STATIC in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; unfold in_zr in Har; cbn [fst snd] in Har; lia.
Qed.
(* the program's statics, in the record's (lo, len) form, are image bytes *)
Lemma cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img segs a.
Proof using LAWS HB IMG.
intros a Ha. apply (cif_prog_img _ _ IMG). apply Exists_exists in Ha as (r & Hr & Har). unfold TFIB_PROG_STATIC in Hr.
unfold inFP, cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING.
destruct Hr as [<-|[<-|[<-|[]]]]; unfold in_zr in Har; cbn [fst snd] in Har.
- exists (0x5e32c0, 0x5e32c0 + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (0x5e3760, 0x5e3760 + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exists (0x5e37e0, 0x5e37e0 + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
(* cmd_ro_ok at a later state that also has arodata_okP *)
Lemma cmd_ro_kept : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md',
AR segs B ly S W mem md -> AR segs B ly' S' W' mem' md' ->
arodata_okP segs CMD_RLO CMD_RHI B (aview segs (w_H W) mem) -> arodata_okP segs CMD_RLO CMD_RHI B (aview segs (w_H W') mem') ->
cmd_ro_ok (aview segs (w_H W) mem) -> cmd_ro_ok (aview segs (w_H W') mem').
Proof using LAWS HB IMG.
intros ly S W mem md ly' S' W' mem' md' _ HAR' _ HR' _. exact (cmd_ro_ok_of_aro segs B LAWS HB IMG ly' S' W' mem' md' HAR' HR').
Qed.
(* a string tail's visibility at a later state: a live block's from AR there, a read-only byte's word from the
   image (the premise at the earlier state is not needed) *)
Lemma cmd_atail_kept : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' p n e,
AR segs B ly S W mem md -> AR segs B ly' S' W' mem' md' ->
((In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= e < p + n) \/
 (in_roP segs CMD_RLO CMD_RHI e /\ ~ Exists (in_zr e) (as_owned_static B))) ->
atail_vis segs W mem e -> atail_vis segs W' mem' e.
Proof using LAWS HB IMG.
intros ly S W mem md ly' S' W' mem' md' p n e _ HAR' [(_ & Hin' & He) | (Hro & _)] _ a Ha.
- pose proof (crf_req_size_ge n) as Hreq.
  exact (AR_block_word_vis segs B ly' S' W' mem' md' p n e a HAR' Hin' ltac:(lia) ltac:(lia)).
- apply crf_rom_view_some. exact (cif_ro_word_some _ _ IMG e a Hro Ha).
Qed.
(* arodata_okP across a callee journal whose footprint holds only program statics and live blocks (of the state
   before or after). The recorder-B walks' form plus the premise `AR segs B ly S W mem md` (the state before), which the
   blocks before the call need to be off the image. *)
Lemma cmd_rodata_kept : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' STK sp0 FP own k,
AR segs B ly S W mem md ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> Exists (in_zr a) TFIB_PROG_STATIC \/
   exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n) ->
arodata_okP segs CMD_RLO CMD_RHI B (aview segs (w_H W) mem) -> arodata_okP segs CMD_RLO CMD_RHI B (aview segs (w_H W') mem').
Proof using LAWS HB IMG.
intros ly S W mem md ly' S' W' mem' md' STK sp0 FP own k HAR HJ HFP HR a Hro Ho He.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
rewrite (F3 a Himg Ho He); [exact (HR a Hro Ho He)|].
apply fp_spares_below; [exact (cif_ro_below_ofl _ _ IMG a Hro)|].
intros HF. destruct (HFP a HF) as [Hp | (b & n & Hb & Hr)].
- exact (Hnp Hp).
- apply in_app_or in Hb as [Hb|Hb].
  + exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ n (conj Hb Hr))))) Himg).
  + exact (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' a HAR' (or_introl (ex_intro _ b (ex_intro _ n (conj Hb Hr))))) Himg).
Qed.
End rest.

(* a value read through the ASan reader is a value of the restricted memory (the pin_set_words walk's val_mem_of_aval,
   on the A side, an earlier version of lib/A/Prog/pin_set_words.v:86-99, over any segments) *)
Lemma val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk).
unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv.
f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(** * The pinned listing *)
Lemma crf_errno_img : crf_img_rangeb tfibsegs (TFIB_ERRNO, 4) = true.
Proof. vm_compute. reflexivity. Qed.
(* the program's statics (g_rec, record.spill, g_quitting) are readable through the image's rom at tfibsegs
   (LLVMFuzzerTestOneInput's entry builds rec_repA from GI_cmdA's zeros; the A twin's lemma of this name), from
   YB13.v's tfib_rom_all over [0x10000, 0x606000) *)
Lemma cmd_prog_rom : forall a, inFP cmd_PG a -> seg_rom tfibsegs (Z_to_bv 64 a) <> None.
Proof.
intros a (r & Hr & Ha). apply tfib_rom_all. unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; lia.
Qed.
(* the side-stack laws the side-stack walks carry (cgif's names: SMP, FFL, ASF), at tfibsegs:
   cgif_file_fuzzer's A/ACfi.v:74-91 (link_SMP, link_FFL, link_ASF) and A/ACed.v:129-144, from the model's
   stack_malloc_progress (YG05.v:71), AR's flag and client-image laws with the image cover (YCeg.v:87), and
   YG0t.v:474 (the A twin's lemmas of these names) *)
Section ss. Context {rc : YM05.RunCeil}.
Lemma cmd_stack_malloc_progress : forall B, stack_malloc_progressP B.
Proof. intros B s cid W Hc Hn. exact (YG05.stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma cmd_frame_flag_law : forall B, frame_flag_lawP tfibsegs B.
Proof.
intros B ly S W mem md cid pos HAR Hin. pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YCeg.tfib_img_cover ly S md L) as [C1 C2].
unfold YCeg.TFIB_IMG_LO, YCeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma cmd_astack_free_law : forall B, astack_free_law tfibsegs B.
Proof. intros B. exact (YG0t.astack_free_law_ok tfibsegs B). Qed.
End ss.
(* TLF: the use-after-return flag cell and its GOT word are the record's (aso_const_law names them among the
   constant cells, as cmd_shadow_cells does the shadow-base cell), and the side-stack entries are the listing's
   (crb_uar_cells / crb_palibf of an earlier version of lib/A/Prog/RecBClosed.v; the A
   twin's lemmas of these names, at B's addresses) *)
Definition cmd_z4_addrs (l : list acell) (v : Z) : list Z :=
flat_map (fun c => match c with ACell (ANum a) w (AV (ANum x)) => if Nat.eqb w 4 && Z.eqb x v then [a] else [] | _ => [] end) l.
Lemma cmd_z4_addrs_in : forall l a v, In (z4 (ANum a) v) l -> In a (cmd_z4_addrs l v).
Proof.
intros l a v H. unfold cmd_z4_addrs. apply in_flat_map. exists (z4 (ANum a) v). split; [exact H|].
cbn -[Z.eqb]. rewrite Z.eqb_refl. cbn. left. reflexivity.
Qed.
Lemma cmd_uar_addrs : cmd_z4_addrs (Tfib_const crf_ly0) 1 = [0xb0c40].
Proof. vm_compute. reflexivity. Qed.
Lemma cmd_got_uar_addrs : crf_z8_addrs (Tfib_const crf_ly0) 0xb0c40 = [0xa5fa8].
Proof. vm_compute. reflexivity. Qed.
Lemma cmd_uar_cells : forall B, CmdBSyms B -> as_uar_cell B = 0xb0c40 /\ as_got_uar B = 0xa5fa8.
Proof.
intros B HB. pose proof (aso_const_law _ (ts_ok B HB) crf_ly0) as (_ & H2 & _ & H4).
rewrite (ts_const B HB) in H2, H4.
apply cmd_z4_addrs_in in H2. rewrite cmd_uar_addrs in H2. destruct H2 as [H2|[]].
rewrite <- H2 in H4. apply crf_z8_addrs_in in H4. rewrite cmd_got_uar_addrs in H4. destruct H4 as [H4|[]].
split; [exact (eq_sym H2) | exact (eq_sym H4)].
Qed.
(* ML: the model's laws for the record's trace universe (YG05.model_laws_ok over the record's ts_universe) *)
Lemma cmd_model_laws : forall B, CmdBSyms B -> model_laws (as_universe B).
Proof. intros B HB. exact (YG05.model_laws_ok (as_universe B) (ts_universe B HB)). Qed.
Section pb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cmd_palibf : forall B, CmdBSyms B -> PaLibF.PALibF (PI := PB_cmd) B.
Proof.
intros B HB. destruct (cmd_uar_cells B HB) as [U G]. constructor.
- rewrite G. vm_compute. reflexivity.
- rewrite U. lia.
- rewrite U. reflexivity.
- intros cid Hc. rewrite (ts_code B HB).
  destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; reflexivity.
- rewrite U. cbn [PaLibF.zseps PaLibF.zseps_from fst snd]. repeat split;
  first [left; apply Z.leb_le; vm_compute; reflexivity | right; apply Z.leb_le; vm_compute; reflexivity].
Qed.
Lemma cmd_palib : forall B, CmdBSyms B -> PALib (PI := PB_cmd) B.
Proof.
intros B HB. destruct (cmd_shadow_cells B HB) as [C1 C2]. constructor.
- rewrite C2. vm_compute. reflexivity.
- rewrite C1. vm_compute. reflexivity.
- left. apply Z.leb_le. vm_compute. reflexivity.
- change (api_env tfibsegs B). split; [rewrite (ts_errno B HB); unfold TFIB_ERRNO, kLowMemEnd; lia|]. split.
  + intros a Ha. rewrite (ts_errno B HB) in Ha. apply (crf_img_rangeb_ok tfibsegs (TFIB_ERRNO, 4) a crf_errno_img).
    unfold in_zr. cbn [fst snd]. lia.
  + rewrite (ts_code B HB). split; apply (ts_universe_drv B HB); unfold DRV_TRACES; cbn;
    repeat (first [left; reflexivity | right]).
- rewrite (ts_code B HB). reflexivity.
- rewrite (ts_code B HB). reflexivity.
- rewrite (ts_code B HB). split; apply Z.ltb_lt; vm_compute; reflexivity.
Qed.
(* the bridges of CmdObj.v for the pinned listing *)
Lemma crf_val_obj : forall i, (i < length cmd_objs)%nat -> cmd_val (A_OBJ i) = nth i cmd_objs 0.
Proof.
intros i Hi. assert (L : (length cmd_objs < 159)%nat) by (apply Nat.ltb_lt; vm_compute; reflexivity).
unfold cmd_val.
destruct (Nat.eqb (A_OBJ i) A_TEXT) eqn:E1; [apply Nat.eqb_eq in E1; unfold A_OBJ, A_TEXT in E1; lia|].
destruct (Nat.ltb (A_OBJ i) (A_HI 0)) eqn:E2; [|apply Nat.ltb_ge in E2; unfold A_OBJ, A_HI in E2; lia].
unfold cmd_obj. f_equal. unfold A_OBJ. lia.
Qed.
Lemma crf_val_hi : forall j, (j < length cmd_his)%nat -> cmd_val (A_HI j) = nth j cmd_his 0.
Proof.
intros j Hj. unfold cmd_val.
destruct (Nat.eqb (A_HI j) A_TEXT) eqn:E1; [apply Nat.eqb_eq in E1; unfold A_HI, A_TEXT in E1; lia|].
destruct (Nat.ltb (A_HI j) (A_HI 0)) eqn:E2; [apply Nat.ltb_lt in E2; unfold A_HI in E2; lia|].
unfold cmd_hi. f_equal. unfold A_HI. lia.
Qed.
Lemma cmd_val_objs_PB : cmd_val_objs (PI := PB_cmd).
Proof. intros i Hi. exact (crf_val_obj i Hi). Qed.
Lemma cmd_val_his_PB : cmd_val_his (PI := PB_cmd).
Proof. intros j Hj. exact (crf_val_hi j Hj). Qed.
(* PRW: the program's statics (g_rec, record.spill, g_quitting: 0x5e32c0 .. 0x5e37e4) lie in tfibsegs' read-write
   window (crb_prw_tfib of an earlier version of lib/A/Prog/RecBClosed.v, at B's addresses;
   one copy for every walk's closed file) *)
Lemma cmd_prw_tfib : forall B, CmdBSyms B -> prog_rw tfibsegs B.
Proof.
intros B HB m a Ha. rewrite (ts_prog B HB) in Ha. unfold TFIB_PROG_STATIC in Ha.
assert (Hr : 0x5e32c0 <= a < 0x5e37e4).
{ apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hra; lia. }
unfold writable_at. apply tfib_rw_window.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma cmd_sig_prog_PB : cmd_sig_prog (PI := PB_cmd).
Proof.
intros s _. change (cmd_sigma s = cmd_val A_TEXT + (cmd_sigma s - cmd_text)). unfold cmd_val. rewrite Nat.eqb_refl. lia.
Qed.
Lemma cmd_val_relro_PB : cmd_val_relro (PI := PB_cmd).
Proof. split; reflexivity. Qed.
End pb.
Print Assumptions cmd_tail_vis.
Print Assumptions cmd_aread_ok_img.
Print Assumptions cmd_ro_prog_apart.
Print Assumptions cmd_prog_img.
Print Assumptions cmd_ro_kept.
Print Assumptions cmd_atail_kept.
Print Assumptions cmd_rodata_kept.
Print Assumptions val_mem_of_aval.
Print Assumptions cmd_palib.
Print Assumptions cmd_palibf.
Print Assumptions cmd_model_laws.
Print Assumptions cmd_val_objs_PB.
Print Assumptions cmd_val_his_PB.
Print Assumptions cmd_sig_prog_PB.
Print Assumptions cmd_val_relro_PB.
Print Assumptions cmd_prw_tfib.
