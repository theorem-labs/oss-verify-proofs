(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths and module names changed; 1342 of its 1436 lines of code are new or changed and 2592 lines of the source are left out. *)
(* pj_set_holds : FSH_Fn_reader.pj_set_spec for fs.asan's pj_set (0x838e8, pf.c:373-391), the success form with the
   key absent. rule 24: pj_set proved new (a Theorem Labs lane's lookup 03:15Z, CONFIRM a Theorem Labs lane 04:16Z; bump's
   lib/A/Prog/pj_set.v on a working branch 955803f9b2e read as template only). The chain: stage A ->
   pj_get (pj_set_get_call) -> stage B -> grow (pj_set_grow_call) -> stage C -> fuzz_strdup (pj_set_sd_call) -> stage D,
   __asan_memcpy, stage E, __asan_memset, stage F, ret (FSW_pj_set_tail.pS_tail), closed by the data post
   (FSW_pj_set_fn.pSf_post). The composed journal count is pj_get 0 + grow's rd_ev (grow_tr 6 n cap) + fuzz_strdup 1,
   which is rd_ev (set_trace n cap klen) (FSW_pj_set_num.pSn_ev_split: EV_fuzz_malloc = 1). Callee contracts are Section
   hypotheses (pj_get, grow, fuzz_strdup, and the runtime's memcpy / memset realizers / fs_img_facts); pj_set_holds_s0
   below discharges grow by S0's FSW_grow_holds.grow_holds. The kept-across-a-call facts are FSW_rd.v's (a Theorem Labs lane)
   and FSW_strkit.v's. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj FSW_K3 FSW_rd FSW_rres FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require Import FSW_pj_set_tbl FSW_pj_set FSW_rdx
  FSW_pj_set_num FSW_pj_set_heads FSW_pj_set_rt FSW_pj_set_tail FSW_pj_set_fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSW_grow_holds.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct pj_set_shape parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* regression test: no plain sink_head instance is resolvable in this file's import cone (fuzz_decode's defect) *)
Fail Definition probe_sk : YI16.sink_head := _.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Notation wvb md mat := (with_vm_backing (m_vm_lazy md) mat md).

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* callee: pj_get (RUNTIME's strcmp inside; walk: a Theorem Labs lane) *)
Hypothesis GET : pj_get_spec tfibsegs B.

(* ---- helpers shared by pj_set's five calls ---- *)
(* the saved-register chunks of pj_set's frame, from pj_set_frame, under any env whose xatoms 9..14 hold them *)
Lemma pS_frame_chunks : forall regs2 xs m sp regs,
  firstn 6 (skipn 9 xs) = map (YK11.getr regs) pj_set_saved_regs -> pj_set_frame m sp regs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) m (sp - 48)) pS_cs.
Proof.
intros regs2 xs m sp regs HX Hfr.
assert (EX : forall i, (i < 6)%nat -> ew (Ereg regs2 (fs_extraT ++ xs)) (xatom (9 + i)) =
  nth i (map (YK11.getr regs) pj_set_saved_regs) (Z_to_bv 64 0)).
{ intros i Hi. rewrite fsw_ew_xatom, <- fpj_nth_skipn, <- HX. symmetry. exact (fpj_nth_firstn _ 6 i _ Hi). }
unfold pj_set_frame, pj_set_saved in Hfr.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
cbn [fst snd] in *. unfold pS_cs.
repeat (apply Forall_cons; [
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff (xatom ?j) 0))) =>
    let i := eval vm_compute in (j - 9)%nat in
    let r := eval vm_compute in (nth i pj_set_saved_regs 0%bv) in
    apply (chunk_ok_val tfibsegs _ _ _ off 8 _ (bv_unsigned (YK11.getr regs r)));
    [ rewrite fsw_SOff0; change j with (9 + i)%nat; rewrite (EX i ltac:(lia)); symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range | cbn; lia
    | replace (sp - 48 + off) with (sp + (off - 48)) by lia; assumption ] end|]).
apply Forall_nil.
Qed.
(* fsT_ret_regions at pj_set's frame is pairwise disjoint *)
Lemma pS_ret_disj : forall E sp rs, bv_unsigned (ew E 2) = sp - 48 -> alloc_ceiling + 48 <= sp ->
  rs = [] -> pairwise_disjoint E (fsT_ret_regions 48 pS_cs rs).
Proof.
intros E sp rs E2 Hc ->. pose proof asan_consts as (C1 & _).
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region. cbn [app pairwise_disjoint all_disjoint].
unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.


(* ---- the call of pj_get (obj, key) at 0x83920, through to stage B's resume state at 0x83924 ---- *)
Lemma pj_set_get_call : forall ly S U (W : world tfibsegs) regs mem md ch (FP : list (Z * Z)) o k w ms D tv Dw kname
  live peak cnt fail regsC memC mat (xs : list word) num str kids keys n cap (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK_pj_set ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  rtree tfibsegs B ly S W mem o (PjTree.JObj ms) D -> pobj tfibsegs B ly S W mem o ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) o 6 num str kids keys n cap ->
  rtree tfibsegs B ly S W mem w tv Dw -> pobj tfibsegs B ly S W mem w ->
  cstr_ok tfibsegs W mem k kname -> cstr_kept B ly S U k kname -> ~ In kname (map fst ms) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  pj_set_call_get W regs regsC memC o k w ->
  ajournal tfibsegs B STK_pj_set (spZ regs) FP ly S W (unpoison U mem) md [] ly S W (unpoison U memC) (wvb md mat) 0 ->
  ARU tfibsegs B ly S U W memC (wvb md mat) ->
  same_below mem memC alloc_ceiling ->
  firstn 6 (skipn 9 xs) = map (YK11.getr regs) pj_set_saved_regs ->
  (forall ly1 S1 W1 regs1 mem1 md1,
     ajournal tfibsegs B STK_pj_set (spZ regs) FP ly S W (unpoison U mem) md [] ly1 S1 W1 (unpoison U mem1) md1 0 ->
     ARU tfibsegs B ly1 S1 U W1 mem1 md1 ->
     st_ok tfibsegs (Ereg regs1 (fs_extraT ++ xs)) ss_pB0
       (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 0x83924) mem1 (seg_rom tfibsegs))) ->
     spZ regs1 = spZ regs - 48 -> pS_a0_zero regs1 -> aregs_preserved regsC regs1 ->
     ablocks B ly1 S1 = ablocks B ly S -> FSupoisonU.fs_heads B ly1 S1 U ->
     rtree tfibsegs B ly1 S1 W1 mem1 o (PjTree.JObj ms) D -> pobj tfibsegs B ly1 S1 W1 mem1 o ->
     rtree tfibsegs B ly1 S1 W1 mem1 w tv Dw -> pobj tfibsegs B ly1 S1 W1 mem1 w ->
     cstr_ok tfibsegs W1 mem1 k kname -> cstr_kept B ly1 S1 U k kname -> fs_glob tfibsegs W1 mem1 live peak cnt fail ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) mem1) ->
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W1) mem1) o 6 num str kids keys n cap ->
     SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 0x83924) mem1 (seg_rom tfibsegs)) md1) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_get regsC memC (wvb md mat)) Q.
Proof.
intros ly S U W regs mem md ch FP o k w ms D tv Dw kname live peak cnt fail regsC memC mat xs num str kids keys n cap Q
  HPRE HHEADS HTo HPo HHo HTw HPw HK HKk HKEY HG HC HJ HARU SB HXS KB.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct HC as (R1 & Rsp & R10 & R11 & R8 & R9 & R18 & R20 & Rkeep & Hfr).
pose proof HPRE as ((HAP & HUOK & HUP) & HRO). pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & _).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem o HAR HPo) as (Lo1 & Lo2).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem w HAR HPw) as (Lw1 & Lw2).
assert (Hsw : s0Z regsC = w) by (unfold s0Z; rewrite R8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HPREc : fpreU tfibsegs B STK_pj_get ly S U W regsC memC (wvb md mat) []).
{ refine (fsw_fpreU_atFP B STK_pj_set (spZ regs) FP ly S U W (unpoison U mem) md [] ly S W memC (wvb md mat) 0 regsC
    STK_pj_get (-48) [] HJ HARU (arodata_below B W mem memC SB HRO) ltac:(lia) eq_refl ltac:(lia) _ _ _ _ _ _ _).
  - unfold STK_pj_get, FRAME_pj_get, zmaxl, STK_RT_STR. cbn. lia.
  - unfold STK_pj_get, STK_pj_set. vm_compute. congruence.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite Forall_forall in Rkeep. rewrite (Rkeep 3%bv ltac:(cbn; tauto)). exact Hgp.
  - rewrite Forall_forall in Rkeep. rewrite (Rkeep 4%bv ltac:(cbn; tauto)). exact Htp.
  - apply achain_low. rewrite Hsw. lia. }

(* ---- pj_get's contract ---- *)
assert (HTo' : rnode tfibsegs B ly S W memC D o (PjTree.JObj ms) D)
  by exact (rnode_below B ly S W (unpoison U mem) md mem memC D o (PjTree.JObj ms) D HAR SB ltac:(lia) Lo2 HTo).
pose proof (pobj_below B ly S W (unpoison U mem) md mem memC o HAR SB HPo) as HPo'.
pose proof (pobj_below B ly S W (unpoison U mem) md mem memC w HAR SB HPw) as HPw'.
assert (HTw' : rtree tfibsegs B ly S W memC w tv Dw)
  by exact (rnode_below B ly S W (unpoison U mem) md mem memC Dw w tv Dw HAR SB ltac:(lia) Lw2 HTw).
eapply SRr_bind.
{ exact (GET ly S U W regsC memC (wvb md mat) [] o k kname (PjTree.JObj ms) D D live peak cnt fail HPREc HHEADS R10 R11
    (or_intror (conj HTo' HPo')) (cstr_ok_below W mem memC k kname SB HK) HKk (fs_glob_below W mem memC live peak cnt fail SB HG)). }
intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HP2 & (Hbl & HK2 & HKk2 & HG2 & Hres)).
destruct Hres as [(Ho0 & _) | (_ & HTo2 & z & Hz & Hres)]; [lia|].
assert (Ez : z = 0).
{ cbn [rd_get_res] in Hres. destruct Hres as [(_ & Ez)|(i & u & kd & Di & Hi & _)]; [exact Ez|].
  exfalso. apply HKEY. apply in_map_iff. exists (kname, u). split; [reflexivity|]. exact (nth_error_In ms i Hi). }
subst z.
(* ---- back at 0x83924: stage B's resume state ---- *)
pose proof (fsw_sp B _ ly S U W regs mem md ch (proj1 HPRE)) as (_ & Hceil & _ & _).
assert (STK48 : 48 <= STK_pj_set) by (vm_compute; congruence).
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) memC) (spZ regs - 48)) pS_cs)
  by exact (pS_frame_chunks regs2 xs _ (spZ regs) regs HXS Hfr).
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = spZ regs - 48).
{ rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl). rewrite (fsw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)).
  exact Rsp. }
destruct (fsw_after_callFPU_args B STK_pj_set (spZ regs) FP [] ly S U W mem md W ly S U memC (wvb md mat) 0 STK_pj_get []
  48 regsC ly2 S2 U W2 regs2 mem2 md2 0 xs pS_cs [] [] 0x83924 (proj1 HSS) (proj2 HSS) HJ HARU HJc
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) OK2 PO2 HP2 Rsp ltac:(lia) ltac:(vm_compute; congruence)
  ltac:(vm_compute; congruence) eq_refl ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK
  (Forall_nil _) (pS_ret_disj _ (spZ regs) [] E2 ltac:(lia) eq_refl) I)
  as (HJ2 & HARU2 & HS2).
assert (HH2 : FSupoisonU.fs_heads B ly2 S2 U) by (unfold FSupoisonU.fs_heads; rewrite Hbl; exact HHEADS).
assert (NF1 : forall a, ~ inFP [] a) by (intros a Ha; exact (inFP_nil a Ha)).
rewrite R1. change (w64 538916) with (Z_to_bv 64 538916).
change (0 + 0) with 0 in HJ2.
apply (KB ly2 S2 W2 regs2 mem2 md2 HJ2 HARU2 HS2).
- unfold spZ at 1. rewrite (fsw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). exact Rsp.
- exact Hz.
- exact HP2.
- exact Hbl.
- exact HH2.
- exact HTo2.
- exact (pobj_kept_call B STK_pj_get (spZ regsC) [] ly S U W memC (wvb md mat) ly2 S2 U W2 mem2 md2 0 o HJc HARU OK2 PO2
    (fun a _ => NF1 a) (fun a Ha => False_ind _ (NF1 a Ha)) HH2 HPo').
- exact (rtree_kept_call B STK_pj_get (spZ regsC) [] ly S U W memC (wvb md mat) ly2 S2 U W2 mem2 md2 0 w tv Dw HJc HARU OK2 PO2
    (fun a _ => NF1 a) (fun a kk x _ _ => NF1 x) HPw' HTw').
- exact (pobj_kept_call B STK_pj_get (spZ regsC) [] ly S U W memC (wvb md mat) ly2 S2 U W2 mem2 md2 0 w HJc HARU OK2 PO2
    (fun a _ => NF1 a) (fun a Ha => False_ind _ (NF1 a Ha)) HH2 HPw').
- exact HK2.
- exact HKk2.
- exact HG2.
- apply (arodata_kept B STK_pj_get (spZ regsC) [] ly S U W memC (wvb md mat) ly2 S2 U W2 mem2 md2 0 HJc HARU OK2 PO2
    ltac:(intros (r & Hr & _); destruct Hr) (fun a _ => NF1 a) (arodata_below B W mem memC SB HRO)).
- exact (pS_hdr_kept_call B STK_pj_get (spZ regsC) [] ly S U W memC (wvb md mat) ly2 S2 U W2 mem2 md2 0 o 6 num str kids keys n cap
    HJc HARU OK2 PO2 (fun a _ => NF1 a) HPo' (pS_hdr_below W mem memC o 6 num str kids keys n cap SB ltac:(lia) Lo2 HHo)).
Qed.

End H.

(* ================= pj_set's own and grow's footprints, named once =================
   pj_set_spec's FP: obj's written fields [o + 24, o + 56), all of val, the old kids / keys blocks (written at slot
   n, or freed by grow) and fuzz/alloc.c's four statics. grow's FP at this call is the same list with obj's three
   written fields only. *)
Definition pS_Dold0 (kids keys cap : Z) : list (Z * Z) :=
  ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap.
Definition pS_FP (o w kids keys cap : Z) : list (Z * Z) :=
  [(o + 24, o + 56); (w, w + 56)] ++ ablocks_fp (rd_hblocks (pS_Dold0 kids keys cap)) ++ FS_PSTAT_FP.
Definition pS_FPg (o kids keys cap : Z) : list (Z * Z) :=
  [(o + 24, o + 40); (o + 48, o + 56)] ++ ablocks_fp (rd_hblocks (pS_Dold0 kids keys cap)) ++ FS_PSTAT_FP.

(* fuzz/alloc.c's four statics are image bytes: they lie in fs.asan's last PT_LOAD, [0xa1000, 0x5fd000) (MEASURED:
   tfibsegs's fourth segment). Same statement and proof as the writer lane's decF_img (a working branch
   lib/A/FSW_dec_F.v:69), restated here because that file is another lane's. *)
Lemma pS_img : forall a, 659456 <= a < 6279168 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (H : option_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (nth_error tfibsegs 3)
  = Some (659456, 5619712)) by (vm_compute; reflexivity).
destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate H].
exists sg. split; [exact (nth_error_In _ _ E)|].
cbn [option_map] in H. injection H as H1 H2. lia.
Qed.
Lemma pS_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; apply pS_img; lia.
Qed.
(* fs's four alloc.c statics are not read-only (a writable segment, outside [FS_RLO, FS_RHI)), and their footprint
   holds the sink closed. Same statements and proofs as the writer lane's decK_ro_not_pstat / decK_pstat_closed
   (a working branch 1539d84e32c lib/A/FSW_dec_E.v:719, :746), restated: that file is another lane's. *)
Lemma pS_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => forallb (fun s => seg_writable s ||
  (snd r <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) tfibsegs)
  FS_PSTAT_FP = true) by (vm_compute; reflexivity).
assert (Hlo : forallb (fun r : Z * Z => (FS_RHI <=? fst r) || (snd r <=? FS_RLO)) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
destruct Hro as [(s & Hs & Hw & Hseg) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H1. cbn beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 s Hs) as H2. cbn beta in H2.
  rewrite Hw in H2. cbn [orb] in H2.
  apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
- pose proof (proj1 (forallb_forall _ _) Hlo r Hr) as H1. cbn beta in H1.
  apply orb_prop in H1 as [H | H]; apply Z.leb_le in H; lia.
Qed.
Lemma pS_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. Qed.

(* ================= the call of grow (obj) at 0x8395c, through to stage C's resume state at 0x83960 =================
   Stage B leaves the walk at the call with a0 = obj; grow_spec answers 0 (every allocation granted, under `quiet`),
   and FSW_K3's fsw_after_callFPU_args composes the journals and builds ss_pC0. The resume env's extras are pj_xs at
   the POST-grow header fields (6, k', y', n, cap'), which is what stage D's object region pD_obj reads.
   Written against the CTX-FREE reader specs (a working branch faa7e2570e5): grow_spec takes no CTX. *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* callee: grow (owner: the Theorem Labs lane) *)
Hypothesis GROW : grow_spec tfibsegs B.

Lemma pj_set_grow_call : forall ly S U (W : world tfibsegs) regs mem md
  ly1 S1 (W1 : world tfibsegs) memC md2 regsC
  o w num str kids keys n cap
  live peak cnt fail (Q : world tfibsegs -> config -> Prop),
  (* the caller's journal to the call (pj_get spent no event), and ARU there *)
  ajournal tfibsegs B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) ly S W (unpoison U mem) md []
    ly1 S1 W1 (unpoison U memC) md2 0 ->
  ARU tfibsegs B ly1 S1 U W1 memC md2 ->
  FSupoisonU.fs_heads B ly1 S1 U ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) memC) ->
  (* the registers at the call, and pj_set's saved-register frame *)
  spZ regsC = spZ regs - 48 ->
  YK11.getr regsC 1 = w64 0x83960 -> YK11.getr regsC 10 = w64 o -> YK11.getr regsC 8 = w64 w ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  pj_set_frame (mrestrict (w_H W1) memC) (spZ regs) regs ->
  (* pj_get moved no fake frame: the caller reads this off the entry AR and the journal's layout_le *)
  (forall cid pos, frame_addr ly1 cid pos = frame_addr ly cid pos) ->
  (* obj at the call *)
  pobj tfibsegs B ly1 S1 W1 memC o ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W1) memC) o 6 num str kids keys n cap ->
  PjStruct.pj_slots_at (fun a kk => In (a, kk) (pS_Dold0 kids keys cap)) 6 kids keys n cap ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 memC (pS_Dold0 kids keys cap) ->
  PjStruct.pj_apart (pS_Dold0 kids keys cap) o -> incl (rd_heads (pS_Dold0 kids keys cap)) U ->
  (o + 56 <= spZ regs - STK_pj_set \/ spZ regs <= o) ->
  pobj tfibsegs B ly1 S1 W1 memC w ->
  (* the callee's budget, all of it discharged by the caller *)
  fs_glob tfibsegs W1 memC live peak cnt fail ->
  quiet cnt fail (Z.of_nat (length (grow_tr 6 n cap))) ->
  rd_sum (pS_Dold0 kids keys cap) <= live ->
  (n = cap -> 56 * ReaderRes.cap2 cap + HEAD < MALLOC_MAX) ->
  live + rd_live (grow_tr 6 n cap) < 2 ^ 64 ->
  st_nev S1 + rd_ev (grow_tr 6 n cap) <= EV_MAX ->
  blocks_bytes S1 + rd_live (grow_tr 6 n cap) <= LIVE_MAX ->
  (* the resume at 0x83960 *)
  (forall ly3 S3 Ug (W3 : world tfibsegs) regs3 mem3 md3 (k' y' cap' : Z) (Dold Dnew : list (Z * Z)) (peak3 : Z),
     grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
     ajournal tfibsegs B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) ly S W (unpoison U mem) md []
       ly3 S3 W3 (unpoison Ug mem3) md3 (rd_ev (grow_tr 6 n cap)) ->
     ARU tfibsegs B ly3 S3 Ug W3 mem3 md3 ->
     st_ok tfibsegs (Ereg regs3 (fs_extraT ++ pj_xs cnt fail live peak 6 k' y' n cap' regs)) ss_pC0
       (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x83960) mem3 (seg_rom tfibsegs))) ->
     spZ regs3 = spZ regs - 48 -> pS_a0_zero regs3 -> aregs_preserved regsC regs3 ->
     Permutation (ablocks B ly3 S3 ++ rd_hblocks Dold) (ablocks B ly1 S1 ++ rd_hblocks Dnew) ->
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem3) o 6 num str k' y' n cap' ->
     PjStruct.pj_slots_at
       (fun a kk => In (a, kk) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap')) 6 k' y' n cap' ->
     rd_blocks_ok tfibsegs B ly3 S3 W3 mem3 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
     rd_moved tfibsegs W1 W3 memC mem3 kids k' (56 * cap) ->
     rd_moved tfibsegs W1 W3 memC mem3 keys y' (8 * cap) ->
     pobj tfibsegs B ly3 S3 W3 mem3 o ->
     peak <= peak3 ->
     fs_glob tfibsegs W3 mem3 (live + PjGrammar.held (grow_tr 6 n cap)) peak3
       (cnt + Z.of_nat (length (grow_tr 6 n cap))) fail ->
     (* what grow kept, for the caller's own data (FSW_rd.fsw_journal_kept_byte / fsw_journal_block_live) *)
     (forall x, ~ inFP (pS_FPg o kids keys cap) x ->
        ((exists p nn, In (p, nn) (ablocks B ly1 S1) /\ p <= x < p + req_size nn) \/
         (exists cid pos, In (cid, pos) (frames S1) /\
            frame_addr ly1 cid pos <= x < frame_addr ly1 cid pos + fs_frame_bytes cid)) ->
        mrestrict (w_H W3) mem3 (Z_to_bv 64 x) = mrestrict (w_H W1) memC (Z_to_bv 64 x)) ->
     (forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn ->
        ~ inFP (pS_FPg o kids keys cap) x -> In (p, nn) (ablocks B ly3 S3)) ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3) ->
     (* grow's own journal, for the caller's FSW_rd kept-across-the-call lemmas *)
     ajournal tfibsegs B STK_grow (spZ regs - 48) (pS_FPg o kids keys cap) ly1 S1 W1 (unpoison U memC) md2 []
       ly3 S3 W3 (unpoison Ug mem3) md3 (rd_ev (grow_tr 6 n cap)) ->
     SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 0x83960) mem3 (seg_rom tfibsegs)) md3) Q) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC md2) Q.
Proof.
intros ly S U W regs mem md ly1 S1 W1 memC md2 regsC o w num str kids keys n cap
  live peak cnt fail Q HJ HARU HHEADS HRO Rsp R1 R10 R8 R3 R4 HFR HFA HPo HHo HSL0 HBO HAP HINC HPL HPw
  HG HQT HRS HMX HLV HEV HBB KC.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR1 & _ & _ & _ & _ & Hfrs1 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & _).
destruct (fsw_pobj_low B ly1 S1 W1 (unpoison U memC) md2 memC o HAR1 HPo) as (Lo1 & Lo2).
destruct (fsw_pobj_low B ly1 S1 W1 (unpoison U memC) md2 memC w HAR1 HPw) as (Lw1 & Lw2).
assert (STK48 : 48 <= STK_pj_set) by (vm_compute; congruence).
assert (HSTKg : STK_grow + 48 <= STK_pj_set) by (vm_compute; congruence).
assert (HSTKg0 : 0 <= STK_grow) by (vm_compute; congruence).
(* ---- grow's pre at the call ---- *)
assert (HPREg : fpreU tfibsegs B STK_grow ly1 S1 U W1 regsC memC md2 []).
{ refine (fsw_fpreU_atFP B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) ly S U W (unpoison U mem) md []
    ly1 S1 W1 memC md2 0 regsC STK_grow (-48) [] HJ HARU HRO ltac:(lia) eq_refl ltac:(lia) _ _ _ _ _ _ _).
  - unfold STK_grow, FRAME_grow, zmaxl. cbn. lia.
  - unfold STK_grow, STK_pj_set. vm_compute. congruence.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* ---- the call ---- *)
eapply SRr_bind.
{ exact (GROW ly1 S1 U W1 regsC memC md2 [] o 6 num str kids keys n cap live peak cnt fail
    HPREg HHEADS R10 HPo ltac:(destruct HPL as [HPL'|HPL']; [left; lia | right; lia])
    HHo HSL0 HBO HAP HINC HG HQT HRS HMX HLV HEV HBB). }
cbv beta. intros W3 c3 Hwle (k' & y' & cap' & Dold & Dnew & Ug & HGR &
  (ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HJc & OK3 & PO3 & HP3 &
   (Ra0 & HPERM & HHDR & HSLOT & HBLK & HMVK & HMVY & HPO3 & peak3 & Hpk & HG3))).
subst c3.
(* ---- grow's footprint is the caller's to write ---- *)
assert (HFPSUB : fsw_fp_sub B ly S ly1 S1 [] (pS_FP o w kids keys cap) (pS_FPg o kids keys cap)).
{ intros a ((rlo, rhi) & Hr & Ha). unfold pS_FPg in Hr. cbn [In app] in Hr.
  assert (HinFP : forall lo hi, In (lo, hi) (pS_FPg o kids keys cap) -> lo <= a < hi ->
    inFP (pS_FP o w kids keys cap) a).
  { intros lo hi Hlo Hah. unfold pS_FPg, pS_FP in *. cbn [In app] in Hlo.
    destruct Hlo as [E|[E|Hlo]].
    - injection E as <- <-. exists (o + 24, o + 56). split; [left; reflexivity | cbn [fst snd]; lia].
    - injection E as <- <-. exists (o + 24, o + 56). split; [left; reflexivity | cbn [fst snd]; lia].
    - exists (lo, hi). split; [right; right; exact Hlo | cbn [fst snd]; lia]. }
  destruct Hr as [E|[E|Hr]].
  - (* obj's kids / keys fields *)
    injection E as <- <-. cbn [fst snd] in Ha.
    destruct HPo as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & m & Hin & H1 & H2) & _)] _].
    + right. right. right. right. split; [eapply HinFP; [left; reflexivity | cbn [fst snd]; lia]|].
      exists cid, pos. split; [rewrite Hfrs1 in Hin; cbn [app] in Hin; exact Hin|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- (HFA cid pos). lia.
    + left. split; [eapply HinFP; [left; reflexivity | cbn [fst snd]; lia]|].
      exists b, m. split; [exact Hin | unfold HEAD in H1; lia].
  - injection E as <- <-. cbn [fst snd] in Ha.
    destruct HPo as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & m & Hin & H1 & H2) & _)] _].
    + right. right. right. right.
      split; [eapply HinFP; [right; left; reflexivity | cbn [fst snd]; lia]|].
      exists cid, pos. split; [rewrite Hfrs1 in Hin; cbn [app] in Hin; exact Hin|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- (HFA cid pos). lia.
    + left. split; [eapply HinFP; [right; left; reflexivity | cbn [fst snd]; lia]|].
      exists b, m. split; [exact Hin | unfold HEAD in H1; lia].
  - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
    + (* the old kids / keys blocks *)
      left. split; [eapply HinFP; [unfold pS_FPg; apply in_or_app; right; apply in_or_app; left; exact Hr
                                  | exact Ha]|].
      unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
      apply in_map_iff in Hb1 as ((aa, kk) & Eaa & Haa). subst b1. cbn [fst snd] in Eb. injection Eb as <- <-.
      destruct (HBO aa kk Haa) as (Hin & _ & Hk0 & _). cbn [fst snd] in Ha.
      exists (aa - HEAD), (kk + HEAD). split; [exact Hin | lia].
    + (* fuzz/alloc.c's statics *)
      right. right. left.
      split; [eapply HinFP; [unfold pS_FPg; apply in_or_app; right; apply in_or_app; right; exact Hr
                            | exact Ha]|].
      apply pS_pstat_img. exists (rlo, rhi). split; [exact Hr | exact Ha]. }
(* ---- the resume at 0x83960 ---- *)
assert (Hsp3 : spZ regs3 = spZ regs - 48)
  by (unfold spZ; rewrite (fsw_pres regsC regs3 2%bv HP3 ltac:(unfold acallee_saved; vm_compute; lia)); exact Rsp).
assert (HX : firstn 6 (skipn 9 (pj_xs cnt fail live peak 6 k' y' n cap' regs))
  = map (YK11.getr regs) pj_set_saved_regs)
  by (unfold pj_xs, pj_fields, pj_set_saved_regs; cbn [app map firstn skipn]; reflexivity).
assert (CHK : Forall (YP09.chunk_ok tfibsegs
  (Ereg regs3 (fs_extraT ++ pj_xs cnt fail live peak 6 k' y' n cap' regs)) (mrestrict (w_H W1) memC)
  (spZ regs - 48)) pS_cs)
  by exact (pS_frame_chunks regs3 _ (mrestrict (w_H W1) memC) (spZ regs) regs HX HFR).
assert (E2 : bv_unsigned (ew (Ereg regs3 (fs_extraT ++ pj_xs cnt fail live peak 6 k' y' n cap' regs)) 2)
  = spZ regs - 48)
  by (rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact Hsp3).
assert (HCEIL : alloc_ceiling + 48 <= spZ regs) by lia.
destruct (fsw_after_callFPU_args B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) [] ly S U W1 mem md W
  ly1 S1 U memC md2 0 STK_grow (pS_FPg o kids keys cap) 48 regsC ly3 S3 Ug W3 regs3 mem3 md3
  (rd_ev (grow_tr 6 n cap)) (pj_xs cnt fail live peak 6 k' y' n cap' regs) pS_cs [] [] 0x83960
  (proj1 HSS) (proj2 HSS) HJ HARU HJc HFPSUB OK3 PO3 HP3 Rsp ltac:(lia) ltac:(vm_compute; congruence)
  ltac:(vm_compute; congruence) eq_refl ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK
  (Forall_nil _) (pS_ret_disj _ (spZ regs) [] E2 HCEIL eq_refl) I)
  as (HJ3 & HARU3 & HS3).
(* ---- what grow kept ---- *)
assert (KEPT : forall x, ~ inFP (pS_FPg o kids keys cap) x ->
  ((exists p nn, In (p, nn) (ablocks B ly1 S1) /\ p <= x < p + req_size nn) \/
   (exists cid pos, In (cid, pos) (frames S1) /\
      frame_addr ly1 cid pos <= x < frame_addr ly1 cid pos + fs_frame_bytes cid)) ->
  mrestrict (w_H W3) mem3 (Z_to_bv 64 x) = mrestrict (w_H W1) memC (Z_to_bv 64 x)).
{ intros x Hf Hx.
  exact (proj2 (fsw_journal_kept_byte B STK_grow (spZ regsC) (pS_FPg o kids keys cap) ly1 S1 U W1 memC md2
    ly3 S3 Ug W3 mem3 md3 (rd_ev (grow_tr 6 n cap)) x HJc HARU OK3 PO3 Hx Hf)). }
assert (LIVEB : forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn ->
  ~ inFP (pS_FPg o kids keys cap) x -> In (p, nn) (ablocks B ly3 S3)).
{ intros p nn x Hin Hx Hf.
  exact (fsw_journal_block_live B STK_grow (spZ regsC) (pS_FPg o kids keys cap) ly1 S1 W1 (unpoison U memC) md2
    ly3 S3 W3 (unpoison Ug mem3) md3 (rd_ev (grow_tr 6 n cap)) p nn x HJc Hin Hx Hf). }
(* the read-only view after grow: grow's footprint (obj's fields, the old kids / keys blocks, the statics) holds no
   read-only byte, and its sink is closed (every range starts above 0) *)
assert (HRO3 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3)).
{ apply (arodata_kept B STK_grow (spZ regsC) (pS_FPg o kids keys cap) ly1 S1 U W1 memC md2 ly3 S3 Ug W3 mem3 md3
    (rd_ev (grow_tr 6 n cap)) HJc HARU OK3 PO3); [| | exact HRO].
  - apply sink_closed_pos. unfold pS_FPg. apply Forall_app. split; [repeat constructor; cbn [fst]; lia|].
    apply Forall_app. split.
    + apply Forall_forall. intros r Hr. unfold ablocks_fp, rd_hblocks in Hr.
      apply in_map_iff in Hr as (b1 & <- & Hb1). apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa).
      destruct (HBO aa kk Haa) as (Hin & _ & _ & _). cbn [fst snd].
      destruct (fsw_ablock_low B ly1 S1 W1 (unpoison U memC) md2 (aa - HEAD) (kk + HEAD) HAR1 Hin) as (Hb4 & _).
      lia.
    + unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
  - intros a Hro Hin. pose proof (fsw_roP_img a Hro) as Himg.
    destruct Hin as ((rlo, rhi) & Hr & Ha). cbn [fst snd] in Ha. unfold pS_FPg in Hr.
    apply in_app_or in Hr as [Hr | Hr].
    + (* obj's fields: client memory, no image byte *)
      assert (Hoa : o <= a < o + 56) by (cbn [In] in Hr; destruct Hr as [E|[E|[]]]; injection E as <- <-; lia).
      refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 (unpoison U memC) md2 a HAR1 _) Himg).
      destruct HPo as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
      * right. left. exists cid, pos. split; [exact Hcp | lia].
      * left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
    + apply in_app_or in Hr as [Hr | Hr].
      * (* the old kids / keys blocks: client memory *)
        unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
        apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa). cbn [fst snd] in Eb. injection Eb as <- <-.
        destruct (HBO aa kk Haa) as (Hin & _ & _ & _).
        refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 (unpoison U memC) md2 a HAR1 _) Himg).
        left. exists (aa - HEAD), (kk + HEAD). split; [exact Hin | lia].
      * exact (pS_ro_not_pstat a Hro (ex_intro _ (rlo, rhi) (conj Hr Ha))). }
rewrite R1. change (w64 538976) with (Z_to_bv 64 538976).
rewrite Z.add_0_l in HJ3.
exact (KC ly3 S3 Ug W3 regs3 mem3 md3 k' y' cap' Dold Dnew peak3 HGR HJ3 HARU3 HS3 Hsp3 Ra0 HP3
  HPERM HHDR HSLOT HBLK HMVK (HMVY eq_refl) HPO3 Hpk HG3 KEPT LIVEB HRO3 ltac:(rewrite <- Rsp; exact HJc)).
Qed.

End G.

(* ================= the call of fuzz_strdup (key) at 0x83994, through to stage D's state at 0x83998 =================
   Stage C leaves the walk at the call with a0 = key; fuzz_strdup_spec answers the new block (the cnt = fail arm is
   dead under `quiet`), and fsw_after_callFPU_args builds ss_pD0 - the resume state stage D consumes, whose extra
   region is obj (pD_obj, write window [24, 56) = pj_set's own FP on obj) and whose atom facts pD_gf pin obj, the
   shadow base (s4) and the new block (a0). *)
Section SD. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* callee: fuzz_strdup (owner ALLOC, a Theorem Labs lane) *)
Hypothesis SD : fuzz_strdup_spec tfibsegs B.

(* the resume regions of stage D are pairwise disjoint: the frame lies at or above alloc_ceiling, obj below it, and
   obj is no image byte (FSW_rd.fsw_pobj_off_img), so it misses the two shadow-base cells. *)
Lemma pS_ret_disj_obj : forall E sp o,
  bv_unsigned (ew E 2) = sp - 48 -> alloc_ceiling + 48 <= sp ->
  bv_unsigned (ew E 9) = o -> 4096 <= o -> o + 56 <= alloc_ceiling ->
  (o + 56 <= 0x10000 \/ FS_IMG_END <= o) ->
  pairwise_disjoint E (fsT_ret_regions 48 pS_cs [pD_obj]).
Proof.
intros E sp o E2 Hc E9 Ho1 Ho2 Himg. pose proof asan_consts as (C1 & _).
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pD_obj, pj_obj_regionWX, pj_obj_regionW.
cbn [app pairwise_disjoint all_disjoint].
unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma pj_set_sd_call : forall ly S U (W : world tfibsegs) regs mem md
  ly3 S3 Ug (W3 : world tfibsegs) mem3 md3 kg regsD
  o k w kids keys cap num str k' y' cap' n (kname : list Z)
  live3 peak3 cnt3 fail (Q : world tfibsegs -> config -> Prop),
  let klen := Z.of_nat (length kname) in
  (* the caller's journal to the call and ARU there *)
  ajournal tfibsegs B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) ly S W (unpoison U mem) md []
    ly3 S3 W3 (unpoison Ug mem3) md3 kg ->
  ARU tfibsegs B ly3 S3 Ug W3 mem3 md3 ->
  FSupoisonU.fs_heads B ly3 S3 Ug ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3) ->
  (* the registers at the call *)
  spZ regsD = spZ regs - 48 ->
  YK11.getr regsD 1 = w64 0x83998 -> YK11.getr regsD 10 = w64 k ->
  YK11.getr regsD 9 = w64 o -> YK11.getr regsD 8 = w64 w -> YK11.getr regsD 20 = w64 SHADOW_OFF ->
  YK11.getr regsD 3 = w64 (as_gp B) -> YK11.getr regsD 4 = w64 (as_tp B) ->
  pj_set_frame (mrestrict (w_H W3) mem3) (spZ regs) regs ->
  (* the key *)
  cstr_ok tfibsegs W3 mem3 k kname -> cstr_kept B ly3 S3 Ug k kname ->
  (* obj, for stage D's object region and its atom facts *)
  pobj tfibsegs B ly3 S3 W3 mem3 o -> pobj tfibsegs B ly3 S3 W3 mem3 w ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem3) o 6 num str k' y' n cap' ->
  0 <= k' < 2 ^ 64 -> 0 <= y' < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= cap' < 2 ^ 64 ->
  (* the callee's budget *)
  fs_glob tfibsegs W3 mem3 live3 peak3 cnt3 fail -> cnt3 <> fail ->
  live3 + (klen + 1) < 2 ^ 64 -> cnt3 + 1 < 2 ^ 64 -> klen + 1 + HEAD < MALLOC_MAX ->
  st_nev S3 + 1 <= EV_MAX -> blocks_bytes S3 + (klen + 1 + HEAD) <= LIVE_MAX ->
  (* the resume at 0x83998 *)
  (forall ly4 S4 (W4 : world tfibsegs) regs4 mem4 md4 a,
     ajournal tfibsegs B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) ly S W (unpoison U mem) md []
       ly4 S4 W4 (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) md4 (kg + 1) ->
     ARU tfibsegs B ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 ->
     st_ok tfibsegs (Ereg regs4 (fs_extraT ++ pj_xs cnt3 fail live3 peak3 6 k' y' n cap' regs)) ss_pD0
       (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 0x83998) mem4 (seg_rom tfibsegs))) ->
     spZ regs4 = spZ regs - 48 -> aregs_preserved regsD regs4 ->
     YK11.getr regs4 10 = w64 a -> 4096 + HEAD <= a ->
     ablocks B ly4 S4 = ablocks B ly3 S3 ++ [(a - HEAD, klen + 1 + HEAD)] ->
     FSupoisonU.fs_heads B ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) ->
     fs_rblock tfibsegs B ly4 S4 W4 mem4 a (klen + 1) ->
     zbytes_at tfibsegs W4 mem4 a (kname ++ [0]) ->
     fs_glob tfibsegs W4 mem4 (live3 + (klen + 1)) (Z.max peak3 (live3 + (klen + 1))) (cnt3 + 1) fail ->
     (* what fuzz_strdup kept (its footprint is fuzz/alloc.c's four statics) *)
     (forall x, ~ inFP FS_PSTAT_FP x ->
        ((exists p nn, In (p, nn) (ablocks B ly3 S3) /\ p <= x < p + req_size nn) \/
         (exists cid pos, In (cid, pos) (frames S3) /\
            frame_addr ly3 cid pos <= x < frame_addr ly3 cid pos + fs_frame_bytes cid)) ->
        mrestrict (w_H W4) mem4 (Z_to_bv 64 x) = mrestrict (w_H W3) mem3 (Z_to_bv 64 x)) ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W4) mem4) ->
     (* fuzz_strdup's own journal, for the caller's FSW_rd kept-across-the-call lemmas *)
     ajournal tfibsegs B STK_fuzz_strdup (spZ regs - 48) FS_PSTAT_FP ly3 S3 W3 (unpoison Ug mem3) md3 []
       ly4 S4 W4 (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) md4 1 ->
     SRr tfibsegs W4 (mkCfg (mkst regs4 (Z_to_bv 64 0x83998) mem4 (seg_rom tfibsegs)) md4) Q) ->
  SRr tfibsegs W3 (YG0d.cfg_at tfibsegs A_fuzz_strdup regsD mem3 md3) Q.
Proof.
intros ly S U W regs mem md ly3 S3 Ug W3 mem3 md3 kg regsD o k w kids keys cap num str k' y' cap' n kname
  live3 peak3 cnt3 fail Q klen HJ HARU HHEADS HRO Rsp R1 R10 R9 R8 R20 R3 R4 HFR HK HKk HPo HPw HHo
  Hk'0 Hy'0 Hn0 Hcap0 HG HCF HLV HCN HMX HEV HBB KD.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs3 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & _).
destruct (fsw_pobj_low B ly3 S3 W3 (unpoison Ug mem3) md3 mem3 o HAR3 HPo) as (Lo1 & Lo2).
destruct (fsw_pobj_low B ly3 S3 W3 (unpoison Ug mem3) md3 mem3 w HAR3 HPw) as (Lw1 & Lw2).
pose proof (fsw_pobj_off_img B ly3 S3 W3 (unpoison Ug mem3) md3 mem3 o HAR3 HPo) as HoIMG.
assert (STK48 : 48 <= STK_pj_set) by (vm_compute; congruence).
assert (HSTKs : STK_fuzz_strdup + 48 <= STK_pj_set) by (vm_compute; congruence).
assert (HSTKs0 : 0 <= STK_fuzz_strdup) by (vm_compute; congruence).
assert (HCEIL : alloc_ceiling + 48 <= spZ regs) by lia.
pose proof HK as (_ & Hk4096 & Hkhi & Hklen32 & _).
(* obj's own bytes are no image byte, so fuzz_strdup's footprint (the four statics) misses them *)
assert (HoFP : forall x, o <= x < o + 56 -> ~ inFP FS_PSTAT_FP x).
{ intros x Hx Hin. destruct Hin as (r & Hr & Har). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
  unfold FS_IMG_END in HoIMG.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Har; lia. }
(* ---- fuzz_strdup's pre at the call ---- *)
assert (HPREs : fpreU tfibsegs B STK_fuzz_strdup ly3 S3 Ug W3 regsD mem3 md3 []).
{ refine (fsw_fpreU_atFP B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) ly S Ug W (unpoison U mem) md []
    ly3 S3 W3 mem3 md3 kg regsD STK_fuzz_strdup (-48) [] HJ HARU HRO ltac:(lia) eq_refl ltac:(lia)
    _ _ _ _ _ _ _).
  - lia.
  - lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* ---- the call: the cnt = fail arm is dead (the caller's `quiet`) ---- *)
eapply SRr_bind.
{ exact (SD ly3 S3 Ug W3 regsD mem3 md3 [] k kname live3 peak3 cnt3 fail HPREs HHEADS R10 HK HKk
    ltac:(intros x Hx; lia) HG (fun _ => HLV) HCN HMX HEV (fun _ => HBB)). }
cbv beta. intros W4 c4 Hwle [(Hcf & _) | (_ & a & (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HJc & OK4 & PO4 & HP4 &
  (R10' & Ha4096 & HAB4 & HH4 & HRB4 & HZB4 & HG4)))]; [exfalso; exact (HCF Hcf)|].
subst c4.
(* ---- fuzz_strdup's footprint is the caller's to write: the four statics are image bytes in pj_set's FP ---- *)
assert (HFPSUB : fsw_fp_sub B ly S ly3 S3 [] (pS_FP o w kids keys cap) FS_PSTAT_FP).
{ intros x Hx. right. right. left. split.
  - destruct Hx as (r & Hr & Hxr). exists r.
    split; [unfold pS_FP; apply in_or_app; right; apply in_or_app; right; exact Hr | exact Hxr].
  - exact (pS_pstat_img x Hx). }
(* ---- the resume at 0x83998 ---- *)
assert (Hsp4 : spZ regs4 = spZ regs - 48)
  by (unfold spZ; rewrite (fsw_pres regsD regs4 2%bv HP4 ltac:(unfold acallee_saved; vm_compute; lia)); exact Rsp).
assert (R9' : YK11.getr regs4 9 = w64 o)
  by (rewrite (fsw_pres regsD regs4 9%bv HP4 ltac:(unfold acallee_saved; vm_compute; lia)); exact R9).
assert (R20' : YK11.getr regs4 20 = w64 SHADOW_OFF)
  by (rewrite (fsw_pres regsD regs4 20%bv HP4
        ltac:(unfold acallee_saved; vm_compute; right; right; right; right; right;
              split; first [exact I | congruence | discriminate])); exact R20).
assert (HX : firstn 6 (skipn 9 (pj_xs cnt3 fail live3 peak3 6 k' y' n cap' regs))
  = map (YK11.getr regs) pj_set_saved_regs)
  by (unfold pj_xs, pj_fields, pj_set_saved_regs; cbn [app map firstn skipn]; reflexivity).
assert (CHK : Forall (YP09.chunk_ok tfibsegs
  (Ereg regs4 (fs_extraT ++ pj_xs cnt3 fail live3 peak3 6 k' y' n cap' regs)) (mrestrict (w_H W3) mem3)
  (spZ regs - 48)) pS_cs)
  by exact (pS_frame_chunks regs4 _ (mrestrict (w_H W3) mem3) (spZ regs) regs HX HFR).
(* obj's header survives the call (its bytes are off the statics), and stage D's region reads it on mem4 *)
assert (HHo4 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W4) mem4) o 6 num str k' y' n cap')
  by exact (pS_hdr_kept_call B STK_fuzz_strdup (spZ regsD) FS_PSTAT_FP ly3 S3 Ug W3 mem3 md3
              ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 1 o 6 num str k' y' n cap'
              HJc HARU OK4 PO4 HoFP HPo HHo).
set (Er := Ereg regs4 (fs_extraT ++ pj_xs cnt3 fail live3 peak3 6 k' y' n cap' regs)) in *.
assert (E2 : bv_unsigned (ew Er 2) = spZ regs - 48)
  by (unfold Er; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Hsp4).
assert (E9 : ew Er 9 = Z_to_bv 64 o)
  by (unfold Er; rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl), R9'; reflexivity).
assert (E9u : bv_unsigned (ew Er 9) = o) by (rewrite E9; apply wz; lia).
assert (E20 : ew Er 20 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl), R20'; reflexivity).
assert (E10 : ew Er 10 = Z_to_bv 64 a)
  by (unfold Er; rewrite (ew_Ereg_nat regs4 _ 10 10%bv eq_refl), R10'; reflexivity).
assert (Exa : forall j, ew Er (xatom j) = nth j (pj_xs cnt3 fail live3 peak3 6 k' y' n cap' regs) (Z_to_bv 64 0))
  by (intros j; unfold Er; apply fsw_ew_xatom).
assert (E4 : ew Er (xatom 4) = Z_to_bv 64 6) by (rewrite (Exa 4%nat); reflexivity).
assert (E5 : ew Er (xatom 5) = Z_to_bv 64 k') by (rewrite (Exa 5%nat); reflexivity).
assert (E6 : ew Er (xatom 6) = Z_to_bv 64 y') by (rewrite (Exa 6%nat); reflexivity).
assert (E7 : ew Er (xatom 7) = Z_to_bv 64 n) by (rewrite (Exa 7%nat); reflexivity).
assert (E8 : ew Er (xatom 8) = Z_to_bv 64 cap') by (rewrite (Exa 8%nat); reflexivity).
(* the new block: its user pointer is 16-aligned and below the ceiling *)
pose proof HRB4 as (HinA & Ha16 & Hklen0 & _).
assert (HARU4' : ARU tfibsegs B ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4)
  by (split; [exact (proj1 HJc) | split; [exact OK4 | exact PO4]]).
destruct (fsw_ablock_low B ly4 S4 W4 (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) md4 (a - HEAD)
  (klen + 1 + HEAD) (proj1 HARU4') HinA) as (_ & Hahi & _).
assert (HOAL : o mod 8 = 0) by (destruct HPo as [[(_ & Hal & _)|(_ & Hal & _)] _]; exact Hal).
assert (HWIN : 56 <= 24 \/ 0 <= 24 /\ 56 <= 56) by (right; split; lia).
assert (RSOK : Forall (YP09.region_ok tfibsegs Er (mrestrict (w_H W4) mem4)) [pD_obj]).
{ constructor; [|constructor]. unfold pD_obj, pj_obj_regionWX.
  exact (fsw_pj_obj_regionW_ok tfibsegs Er (mrestrict (w_H W4) mem4) 9 24 56 (xatom 4) (xatom 5) (xatom 6)
    (xatom 7) (xatom 8) o 6 num str k' y' n cap' HHo4 HWIN E9 E4 E5 E6 E7 E8). }
assert (GFOK : atoms_ok Er pD_gf).
{ pose proof asan_consts as ((AC1 & AC2) & _).
  destruct (fsw_rblock_low B ly4 S4 W4 (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) md4 mem4 a (klen + 1)
    (proj1 HARU4') HRB4) as (Ha1' & Ha2').
  assert (Hp47 : (2:Z) ^ 47 = 140737488355328) by (vm_compute; reflexivity).
  assert (Ha2 : a <= 2 ^ 47) by (rewrite Hp47; unfold HEAD in *; lia).
  assert (Ho2' : o <= 0x7fffff800000 - 56) by (unfold HEAD in *; lia).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold HEAD in *; lia).
  assert (Ho64 : 0 <= o < 2 ^ 64) by (unfold HEAD in *; lia).
  unfold pD_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E20, E10.
  rewrite (unsigned_lit_small o) by lia. rewrite (unsigned_lit_small a) by lia.
  rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite Z.pow_0_r. unfold HEAD in *.
  split; [split; [split; [lia | exact Ho2'] | split; [exact HOAL | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [|exact I]. split; [split; [exact Ha1' | exact Ha2] | split; [exact Ha16 | lia]]. }
destruct (fsw_after_callFPU_args B STK_pj_set (spZ regs) (pS_FP o w kids keys cap) [] ly S U W3 mem md W
  ly3 S3 Ug mem3 md3 kg STK_fuzz_strdup FS_PSTAT_FP 48 regsD ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 regs4 mem4 md4 1
  (pj_xs cnt3 fail live3 peak3 6 k' y' n cap' regs) pS_cs [pD_obj] pD_gf 0x83998
  (proj1 HSS) (proj2 HSS) HJ HARU HJc HFPSUB OK4 PO4 HP4 Rsp ltac:(lia) ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK RSOK
  (pS_ret_disj_obj Er (spZ regs) o E2 HCEIL E9u ltac:(lia) ltac:(lia) HoIMG) GFOK)
  as (HJ4 & HARU4 & HS4).
assert (KEPT : forall x, ~ inFP FS_PSTAT_FP x ->
  ((exists p nn, In (p, nn) (ablocks B ly3 S3) /\ p <= x < p + req_size nn) \/
   (exists cid pos, In (cid, pos) (frames S3) /\
      frame_addr ly3 cid pos <= x < frame_addr ly3 cid pos + fs_frame_bytes cid)) ->
  mrestrict (w_H W4) mem4 (Z_to_bv 64 x) = mrestrict (w_H W3) mem3 (Z_to_bv 64 x)).
{ intros x Hf Hx.
  exact (proj2 (fsw_journal_kept_byte B STK_fuzz_strdup (spZ regsD) FS_PSTAT_FP ly3 S3 Ug W3 mem3 md3
    ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 1 x HJc HARU OK4 PO4 Hx Hf)). }
assert (HRO4 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W4) mem4))
  by exact (arodata_kept B STK_fuzz_strdup (spZ regsD) FS_PSTAT_FP ly3 S3 Ug W3 mem3 md3
              ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 1 HJc HARU OK4 PO4 pS_pstat_closed pS_ro_not_pstat HRO).
rewrite R1. change (w64 539032) with (Z_to_bv 64 539032).
exact (KD ly4 S4 W4 regs4 mem4 md4 a HJ4 HARU4 HS4 Hsp4 HP4 R10' Ha4096 HAB4 HH4 HRB4 HZB4 HG4 KEPT HRO4
  ltac:(rewrite <- Rsp; exact HJc)).
Qed.

End SD.

(* ================= helpers of the chain ================= *)
(* the released plain proof's object slots are pj_set_spec's Dold0 *)
Lemma pS_slots_Dold0 : forall kids keys cap,
  parse_items_shape.pis_slots true kids keys cap = pS_Dold0 kids keys cap.
Proof.
intros kids keys cap. unfold parse_items_shape.pis_slots, parse_items_shape.pis_oz, pS_Dold0,
  ReaderRes.kids_blk, ReaderRes.keys_blk. destruct (cap =? 0); reflexivity.
Qed.
Lemma pS_slots_at_Dold0 : forall (L : list (Z * Z)) kids keys n cap,
  PjStruct.pj_slots_at (fun a kk => In (a, kk) L) 6 kids keys n cap ->
  PjStruct.pj_slots_at (fun a kk => In (a, kk) (pS_Dold0 kids keys cap)) 6 kids keys n cap.
Proof.
intros L kids keys n cap (Hty & Hn & H0 & _). split; [exact Hty|]. split; [exact Hn|]. split; [exact H0|].
intros Hc. assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
unfold pS_Dold0, ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite Ec. cbn.
split; [left; reflexivity | intros _; right; left; reflexivity].
Qed.

Section KO. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the key's bytes and NUL miss grow's footprint, in the key's BLOCK arm (cstr_kept's first disjunct): obj's fields are
   in obj's footprint (pj_set_spec's key apartness), the old kids / keys blocks' bodies are blocks of D (same
   apartness), their 16-byte heads are ranges of U (incl rd_heads Dold0 U) which the key avoids, and the statics are
   image bytes while the key lies in a live block *)
Lemma pS_key_off_FPg : forall B ly1 S1 (W1 : world tfibsegs) mx md m0 U o (D : list (Z * Z)) kids keys cap k
  (kname : list Z) b m,
  AR tfibsegs B ly1 S1 W1 mx md ->
  incl (rd_heads (pS_Dold0 kids keys cap)) U -> incl (pS_Dold0 kids keys cap) D ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ PjStruct.pj_foot o D x) ->
  In (b, m) (ablocks B ly1 S1) -> b <= k -> k + Z.of_nat (length kname) + 1 <= b + m ->
  (forall r, In r U -> k + Z.of_nat (length kname) + 1 <= fst r \/ fst r + snd r <= k) ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 m0 (pS_Dold0 kids keys cap) ->
  forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ inFP (pS_FPg o kids keys cap) x.
Proof.
intros B ly1 S1 W1 mx md m0 U o D kids keys cap k kname b m HAR HINC HSUB Hfoot Hb Hbk Hkm HUk HBO x Hx
  ((rlo, rhi) & Hr & Hxr). cbn [fst snd] in Hxr.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
unfold pS_FPg in Hr. apply in_app_or in Hr as [Hr | Hr].
- apply (Hfoot x Hx). left. cbn [In] in Hr. destruct Hr as [E|[E|[]]]; injection E as <- <-; lia.
- apply in_app_or in Hr as [Hr | Hr].
  + unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
    apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa). cbn [fst snd] in Eb. injection Eb as <- <-.
    destruct (HBO aa kk Haa) as (_ & _ & Hk0 & _).
    assert (Hrq : req_size (kk + HEAD) = kk + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (kk + 16) 0); lia).
    rewrite Hrq in Hxr.
    destruct (Z_lt_le_dec x aa) as [Hlt | Hge].
    * (* the head: a range of U the key avoids *)
      assert (HU : In (aa - HEAD, HEAD) U).
      { apply HINC. unfold rd_heads. apply in_map_iff. exists (aa, kk). split; [reflexivity | exact Haa]. }
      destruct (HUk _ HU) as [H1 | H1]; cbn [fst snd] in H1; unfold HEAD in *; lia.
    * apply (Hfoot x Hx). right. exists (aa, kk). split; [exact (HSUB _ Haa) | unfold PjStruct.pj_holds; cbn [fst snd]; unfold HEAD in *; lia].
  + (* the statics are image bytes; the key's byte is a live block's *)
    refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 mx md x HAR _) (pS_pstat_img x (ex_intro _ (rlo, rhi) (conj Hr Hxr)))).
    left. exists b, m. split; [exact Hb|].
    assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
Qed.
(* ... and in its TABLE arms (an FS_RO_STRS literal or an FS_SN_FMTS format): those are image bytes, obj's fields and
   the old blocks are client memory, and no table entry meets fuzz/alloc.c's statics (MEASURED: vm_compute over the
   two tables) *)
Lemma pS_key_off_FPg_tbl : forall B ly1 S1 (W1 : world tfibsegs) mx md m0 m1 o kids keys cap k (kname : list Z),
  AR tfibsegs B ly1 S1 W1 mx md -> pobj tfibsegs B ly1 S1 W1 m1 o ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 m0 (pS_Dold0 kids keys cap) ->
  (In (k, kname) FS_RO_STRS \/ (exists ps, In (k, ps) FS_SN_FMTS /\ kname = fmt_bytes ps)) ->
  forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ inFP (pS_FPg o kids keys cap) x.
Proof.
intros B ly1 S1 W1 mx md m0 m1 o kids keys cap k kname HAR HPo HBO Htbl x Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Himg : in_img tfibsegs x).
{ destruct Htbl as [Hs | (ps & Hf & ->)];
    [exact (FSW_strkit.fs_ro_strs_img k kname x Hs Hx) | exact (FSW_strkit.fs_sn_fmts_img k ps x Hf Hx)]. }
intros ((rlo, rhi) & Hr & Hxr). cbn [fst snd] in Hxr.
unfold pS_FPg in Hr. apply in_app_or in Hr as [Hr | Hr].
- assert (Hox : o <= x < o + 56) by (cbn [In] in Hr; destruct Hr as [E|[E|[]]]; injection E as <- <-; lia).
  refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 mx md x HAR _) Himg).
  destruct HPo as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  + right. left. exists cid, pos. split; [exact Hcp | lia].
  + left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
- apply in_app_or in Hr as [Hr | Hr].
  + unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
    apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa). cbn [fst snd] in Eb. injection Eb as <- <-.
    destruct (HBO aa kk Haa) as (Hin & _ & _ & _).
    refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 mx md x HAR _) Himg).
    left. exists (aa - HEAD), (kk + HEAD). split; [exact Hin | lia].
  + destruct Htbl as [Hs | (ps & Hf & ->)].
    * assert (Hb : forallb (fun t : Z * list Z => forallb (fun s : Z * Z =>
        (fst t + Z.of_nat (length (snd t)) + 1 <=? fst s) || (snd s <=? fst t)) FS_PSTAT_FP) FS_RO_STRS = true)
        by (vm_compute; reflexivity).
      pose proof (proj1 (forallb_forall _ _) Hb (k, kname) Hs) as H1. cbn beta in H1.
      pose proof (proj1 (forallb_forall _ _) H1 (rlo, rhi) Hr) as H2. cbn [fst snd] in H2.
      apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
    * assert (Hb : forallb (fun t : Z * list fpiece => forallb (fun s : Z * Z =>
        (fst t + Z.of_nat (length (fmt_bytes (snd t))) + 1 <=? fst s) || (snd s <=? fst t)) FS_PSTAT_FP) FS_SN_FMTS = true)
        by (vm_compute; reflexivity).
      pose proof (proj1 (forallb_forall _ _) Hb (k, ps) Hf) as H1. cbn beta in H1.
      pose proof (proj1 (forallb_forall _ _) H1 (rlo, rhi) Hr) as H2. cbn [fst snd] in H2.
      apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
Qed.
End KO.

(* ================= carry helpers for the chain ================= *)
Ltac pS_csv := unfold acallee_saved; vm_compute;
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | do 3 right; left; reflexivity | do 4 right; left; reflexivity
        | do 5 right; split; discriminate ].
Section CR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* a call keeps every callee-saved register pj_set reads *)
Lemma pS_pres : forall (rA rB : bvmap 5 word) (r : bv 5), aregs_preserved rA rB ->
  In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> YK11.getr rB r = YK11.getr rA r.
Proof.
intros rA rB r HP Hr. apply (fsw_pres rA rB r HP).
cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pS_csv |]). destruct Hr.
Qed.
(* fuzz/alloc.c's statics lie in the image, far below the shadow *)
Lemma pS_pstat_off_shadow : forall a, inFP FS_PSTAT_FP a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros a (r & Hr & Ha) Hs. unfold FS_PSTAT_FP in Hr. cbn [In] in Hr. unfold SHADOW_OFF in Hs.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
Qed.
(* grow's footprint holds no shadow byte: obj's fields and the old blocks are client memory, the statics image *)
Lemma pS_FPg_off_shadow : forall B ly1 S1 (W1 : world tfibsegs) mx md m0 m1 o kids keys cap,
  AR tfibsegs B ly1 S1 W1 mx md -> pobj tfibsegs B ly1 S1 W1 m1 o ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 m0 (pS_Dold0 kids keys cap) ->
  forall a, inFP (pS_FPg o kids keys cap) a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros B ly1 S1 W1 mx md m0 m1 o kids keys cap HAR HPo HBO a ((rlo, rhi) & Hr & Ha). cbn [fst snd] in Ha.
unfold pS_FPg in Hr. apply in_app_or in Hr as [Hr | Hr].
- apply (fsw_pobj_off_shadow B ly1 S1 W1 mx md m1 o HAR HPo a).
  cbn [In] in Hr. destruct Hr as [E|[E|[]]]; injection E as <- <-; lia.
- apply in_app_or in Hr as [Hr | Hr].
  + unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
    apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa). cbn [fst snd] in Eb. injection Eb as <- <-.
    destruct (HBO aa kk Haa) as (Hin & _ & Hk0 & _).
    exact (fsw_ablock_off_shadow B ly1 S1 W1 mx md (aa - HEAD) (kk + HEAD) HAR Hin a Ha).
  + exact (pS_pstat_off_shadow a (ex_intro _ (rlo, rhi) (conj Hr Ha))).
Qed.
(* a pobj apart from obj's footprint misses grow's: obj's fields by the apartness, an old block's body by the same,
   its head because the pobj's own block (or fake frame) is another one, the statics because they are image bytes *)
Lemma pS_pobj_off_FPg : forall B ly1 S1 (W1 : world tfibsegs) mx md m0 m1 o v kids keys cap (D : list (Z * Z)),
  AR tfibsegs B ly1 S1 W1 mx md -> pobj tfibsegs B ly1 S1 W1 m1 v ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 m0 (pS_Dold0 kids keys cap) -> incl (pS_Dold0 kids keys cap) D ->
  (forall x, v <= x < v + 56 -> ~ PjStruct.pj_foot o D x) ->
  forall x, v <= x < v + 56 -> ~ inFP (pS_FPg o kids keys cap) x.
Proof.
intros B ly1 S1 W1 mx md m0 m1 o v kids keys cap D HAR HPv HBO HSUB Hfoot x Hx ((rlo, rhi) & Hr & Hxr).
cbn [fst snd] in Hxr. pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HCL : (exists p nn, In (p, nn) (ablocks B ly1 S1) /\ p <= x < p + req_size nn) \/
  (exists cid pos, In (cid, pos) (frames S1) /\
     frame_addr ly1 cid pos <= x < frame_addr ly1 cid pos + fs_frame_bytes cid)).
{ destruct HPv as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  - right. exists cid, pos. split; [exact Hcp | lia].
  - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
unfold pS_FPg in Hr. apply in_app_or in Hr as [Hr | Hr].
- apply (Hfoot x Hx). left. cbn [In] in Hr. destruct Hr as [E|[E|[]]]; injection E as <- <-; lia.
- apply in_app_or in Hr as [Hr | Hr].
  + unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
    apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa). cbn [fst snd] in Eb. injection Eb as <- <-.
    destruct (HBO aa kk Haa) as (Hin & _ & Hk0 & _).
    assert (Hrq : req_size (kk + HEAD) = kk + HEAD)
      by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (kk + 16) 0); lia).
    rewrite Hrq in Hxr.
    destruct (Z_lt_le_dec x aa) as [Hlt | Hge].
    * destruct HPv as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
      -- pose proof (sep_block_frame tfibsegs B LAWS ly1 S1 W1 mx md (aa - HEAD) (kk + HEAD) cid pos HAR Hin Hcp)
           as Dj.
         unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite Hrq in Dj. lia.
      -- destruct (Z.eq_dec b (aa - HEAD)) as [Eb | Nb]; [unfold HEAD in *; lia|].
         assert (NE : (b, m) <> (aa - HEAD, kk + HEAD)) by (intros E; injection E as E1 _; exact (Nb E1)).
         pose proof (sep_blocks tfibsegs B LAWS ly1 S1 W1 mx md b m (aa - HEAD) (kk + HEAD) HAR Hb Hin NE) as Dj.
         unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite Hrq in Dj.
         assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
         unfold HEAD in *. lia.
    * apply (Hfoot x Hx). right. exists (aa, kk).
      split; [exact (HSUB _ Haa) | unfold PjStruct.pj_holds; cbn [fst snd]; lia].
  + refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 mx md x HAR _)
      (pS_pstat_img x (ex_intro _ (rlo, rhi) (conj Hr Hxr)))).
    destruct HCL as [HCL | HCL]; [left; exact HCL | right; left; exact HCL].
Qed.
(* the key across grow: cstr_ok and cstr_kept at grow's end state. Block arm: FSW_strkit.cstr_ok_kept_blkU (the key's
   block survives: its byte k is off grow's footprint), with the callee's U' rule: a head grow added is the head of a
   block live after grow and not before (pSh_fresh_after_grow), so it misses the key (pSh_newhead_apart). Table arms:
   FSW_strkit.cstr_ok_kept_tbl at the new state. (FSW_rd.cstr_ok_kept_call asks the key's tail word off the footprint
   too, [k, k + len + 8); that is not derivable for a key that ends its block next to an old kids / keys block, so the
   strkit lemmas, which ask [k, k + len + 1), are used directly.) *)
Lemma pS_key_after_grow : forall B (IMG : fs_img_facts tfibsegs B) sp1 ly1 S1 U (W1 : world tfibsegs) mem1 md1
  ly3 S3 Ug (W3 : world tfibsegs) mem3 md3 kc o n cap kids keys k' y' cap' Dold Dnew k (kname : list Z),
  ajournal tfibsegs B STK_grow sp1 (pS_FPg o kids keys cap) ly1 S1 W1 (unpoison U mem1) md1 []
    ly3 S3 W3 (unpoison Ug mem3) md3 kc ->
  ARU tfibsegs B ly1 S1 U W1 mem1 md1 -> ARU tfibsegs B ly3 S3 Ug W3 mem3 md3 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3) ->
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem3 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  (n = cap -> ~ In (k' - HEAD, 56 * cap' + HEAD) (ablocks B ly1 S1) /\
              ~ In (y' - HEAD, 8 * cap' + HEAD) (ablocks B ly1 S1)) ->
  (forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn ->
     ~ inFP (pS_FPg o kids keys cap) x -> In (p, nn) (ablocks B ly3 S3)) ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ inFP (pS_FPg o kids keys cap) x) ->
  cstr_kept B ly1 S1 U k kname -> cstr_ok tfibsegs W1 mem1 k kname ->
  cstr_ok tfibsegs W3 mem3 k kname /\ cstr_kept B ly3 S3 Ug k kname.
Proof.
intros B IMG sp1 ly1 S1 U W1 mem1 md1 ly3 S3 Ug W3 mem3 md3 kc o n cap kids keys k' y' cap' Dold Dnew k kname
  HJ HU1 HU3 HRO3 G RB3 Hfr SURV HkF Hk Hc.
pose proof HU3 as (HAR3 & OK3 & PO3).
assert (Hl : 0 <= Z.of_nat (length kname)) by lia.
assert (HkF0 : ~ inFP (pS_FPg o kids keys cap) k) by (apply HkF; lia).
assert (HUr : forall r, In r Ug -> In r U \/ fst r + snd r <= k \/ k + Z.of_nat (length kname) + 1 <= fst r).
{ intros r Hr. pose proof G as G'.
  destruct G' as [(_ & _ & _ & _ & _ & _ & EUg) | (Hn & Ec & _)].
  - left. rewrite <- EUg. exact Hr.
  - assert (Hc' : cap' <> 0) by (rewrite Ec; unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia).
    pose proof RB3 as RB3'. rewrite (pSh_blk_ne0 k' y' cap' Hc') in RB3'.
    destruct (Hfr Hn) as (F1 & F2).
    destruct (pSh_ug_sub _ _ _ _ _ _ _ _ _ _ _ G r Hr) as [H | [-> | ->]]; [left; exact H | right | right].
    + destruct (RB3' k' (56 * cap') (or_introl eq_refl)) as (Hin3 & _ & Hpos & _).
      assert (HM : 16 <= req_size (56 * cap' + HEAD))
        by (unfold req_size, HEAD; destruct (Z.eqb_spec (56 * cap' + 16) 0); lia).
      destruct (pSh_newhead_apart B ly1 S1 U ly3 S3 W3 _ md3 _ k' (56 * cap' + HEAD) k kname
        HAR3 Hin3 F1 HM Hk HkF0 SURV) as [L | L]; cbn [fst snd]; unfold HEAD in *; lia.
    + destruct (RB3' y' (8 * cap') (or_intror (or_introl eq_refl))) as (Hin3 & _ & Hpos & _).
      assert (HM : 16 <= req_size (8 * cap' + HEAD))
        by (unfold req_size, HEAD; destruct (Z.eqb_spec (8 * cap' + 16) 0); lia).
      destruct (pSh_newhead_apart B ly1 S1 U ly3 S3 W3 _ md3 _ y' (8 * cap' + HEAD) k kname
        HAR3 Hin3 F2 HM Hk HkF0 SURV) as [L | L]; cbn [fst snd]; unfold HEAD in *; lia. }
destruct Hk as [(b & m & Hb & Hbk & Hkm & HD) | [Htbl | (ps & Hps & ->)]].
- assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hkx : b <= k < b + req_size m) by lia.
  pose proof (SURV b m k Hb Hkx HkF0) as Hb3.
  split.
  + exact (FSW_strkit.cstr_ok_kept_blkU B STK_grow sp1 (pS_FPg o kids keys cap) ly1 S1 U W1 mem1 md1 []
      ly3 S3 Ug W3 mem3 md3 kc k kname b m HU1 HJ OK3 PO3 Hb Hb3 Hbk Hkm HkF HUr Hc).
  + left. exists b, m. split; [exact Hb3|]. split; [exact Hbk|]. split; [exact Hkm|].
    intros r Hr. destruct (HUr r Hr) as [HrU | [H | H]]; [exact (HD r HrU) | right; exact H | left; exact H].
- split; [exact (FSW_strkit.cstr_ok_kept_tbl B ly3 S3 Ug W3 mem3 md3 k kname IMG HU3 HRO3 (or_introl Htbl))
         | right; left; exact Htbl].
- split.
  + exact (FSW_strkit.cstr_ok_kept_tbl B ly3 S3 Ug W3 mem3 md3 k _ IMG HU3 HRO3
      (or_intror (ex_intro _ ps (conj Hps eq_refl)))).
  + right; right. exists ps. split; [exact Hps | reflexivity].
Qed.
End CR.
(* two byte ranges, one of which has no byte in the other, are apart *)
Lemma pS_apart_of : forall a n b m, 0 < n -> 0 < m -> (forall x, a <= x < a + n -> ~ (b <= x < b + m)) ->
  a + n <= b \/ b + m <= a.
Proof.
intros a n b m Hn Hm H.
destruct (Z_le_gt_dec (a + n) b) as [L | L]; [left; exact L|].
destruct (Z_le_gt_dec (b + m) a) as [L' | L']; [right; exact L'|].
exfalso. apply (H (Z.max a b)); lia.
Qed.
Section GE. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* a pobj misses fuzz/alloc.c's statics: it is client memory, they are image bytes *)
Lemma pS_pobj_off_pstat : forall B ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> forall x, v <= x < v + 56 -> ~ inFP FS_PSTAT_FP x.
Proof.
intros B ly S W mx md m v HAR HPv x Hx (r & Hr & Har).
pose proof (fsw_pobj_off_img B ly S W mx md m v HAR HPv) as HvIMG.
unfold FS_PSTAT_FP in Hr. cbn [In] in Hr. unfold FS_IMG_END in HvIMG.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Har; lia.
Qed.
(* obj's first byte misses grow's footprint: obj's written fields start at o + 24, the old blocks' bodies by the
   apartness, their heads because obj's own block (or fake frame) is another one, the statics are image bytes *)
Lemma pS_obj_off_FPg0 : forall B ly1 S1 (W1 : world tfibsegs) mx md m0 m1 o kids keys cap,
  AR tfibsegs B ly1 S1 W1 mx md -> pobj tfibsegs B ly1 S1 W1 m1 o ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 m0 (pS_Dold0 kids keys cap) -> PjStruct.pj_apart (pS_Dold0 kids keys cap) o ->
  ~ inFP (pS_FPg o kids keys cap) o.
Proof.
intros B ly1 S1 W1 mx md m0 m1 o kids keys cap HAR HPo HBO HAP ((rlo, rhi) & Hr & Hxr).
cbn [fst snd] in Hxr. pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HCL : (exists p nn, In (p, nn) (ablocks B ly1 S1) /\ p <= o < p + req_size nn) \/
  (exists cid pos, In (cid, pos) (frames S1) /\
     frame_addr ly1 cid pos <= o < frame_addr ly1 cid pos + fs_frame_bytes cid)).
{ destruct HPo as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  - right. exists cid, pos. split; [exact Hcp | lia].
  - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
unfold pS_FPg in Hr. apply in_app_or in Hr as [Hr | Hr].
- cbn [In] in Hr. destruct Hr as [E|[E|[]]]; injection E as <- <-; lia.
- apply in_app_or in Hr as [Hr | Hr].
  + unfold ablocks_fp, rd_hblocks in Hr. apply in_map_iff in Hr as (b1 & Eb & Hb1).
    apply in_map_iff in Hb1 as ((aa, kk) & <- & Haa). cbn [fst snd] in Eb. injection Eb as <- <-.
    destruct (HBO aa kk Haa) as (Hin & _ & Hk0 & _).
    assert (Hrq : req_size (kk + HEAD) = kk + HEAD)
      by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (kk + 16) 0); lia).
    rewrite Hrq in Hxr.
    destruct (Z_lt_le_dec o aa) as [Hlt | Hge].
    * destruct HPo as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
      -- pose proof (sep_block_frame tfibsegs B LAWS ly1 S1 W1 mx md (aa - HEAD) (kk + HEAD) cid pos HAR Hin Hcp)
           as Dj.
         unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite Hrq in Dj. lia.
      -- destruct (Z.eq_dec b (aa - HEAD)) as [Eb | Nb]; [unfold HEAD in *; lia|].
         assert (NE : (b, m) <> (aa - HEAD, kk + HEAD)) by (intros E; injection E as E1 _; exact (Nb E1)).
         pose proof (sep_blocks tfibsegs B LAWS ly1 S1 W1 mx md b m (aa - HEAD) (kk + HEAD) HAR Hb Hin NE) as Dj.
         unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite Hrq in Dj.
         assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
         unfold HEAD in *. lia.
    * refine (HAP (aa, kk) o Haa _ _); [unfold PjStruct.pj_holds; cbn [fst snd]; lia | lia].
  + refine (proj2 (al_client_img tfibsegs B LAWS ly1 S1 W1 mx md o HAR _)
      (pS_pstat_img o (ex_intro _ (rlo, rhi) (conj Hr Hxr)))).
    destruct HCL as [HCL | HCL]; [left; exact HCL | right; left; exact HCL].
Qed.
(* a block live after grow and not before misses a pobj that was live before (its own block survives grow, being off
   grow's footprint at its first byte, and is another block; or it is in a fake frame) *)
Lemma pS_new_apart : forall B ly1 S1 ly3 S3 (W1 W3 : world tfibsegs) mx3 md3 m1 v (FPg : list (Z * Z)) c M,
  AR tfibsegs B ly3 S3 W3 mx3 md3 -> pobj tfibsegs B ly1 S1 W1 m1 v ->
  frames S3 = frames S1 -> (forall cid pos, frame_addr ly3 cid pos = frame_addr ly1 cid pos) ->
  ~ inFP FPg v ->
  (forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn -> ~ inFP FPg x ->
     In (p, nn) (ablocks B ly3 S3)) ->
  In (c, M) (ablocks B ly3 S3) -> ~ In (c, M) (ablocks B ly1 S1) ->
  c + req_size M <= v \/ v + 56 <= c.
Proof.
intros B ly1 S1 ly3 S3 W1 W3 mx3 md3 m1 v FPg c M HAR3 HPv Hfr HFA HvF SURV Hc3 Hc1.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HPv as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
- assert (Hcp3 : In (cid, pos) (frames S3)) by (rewrite Hfr; exact Hcp).
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 mx3 md3 c M cid pos HAR3 Hc3 Hcp3) as Dj.
  unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite (HFA cid pos) in Dj. lia.
- assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hvx : b <= v < b + req_size m) by (unfold HEAD in H1; lia).
  pose proof (SURV b m v Hb Hvx HvF) as Hb3.
  assert (NE : (b, m) <> (c, M)) by (intros E; rewrite E in Hb; exact (Hc1 Hb)).
  pose proof (sep_blocks tfibsegs B LAWS ly3 S3 W3 mx3 md3 b m c M HAR3 Hb3 Hc3 NE) as Dj.
  unfold zdisjoint in Dj. cbn [fst snd] in Dj. unfold HEAD in H1. lia.
Qed.
(* pj_set may write a byte of a pobj inside its footprint range (lo, hi): a live block byte, or a frame byte *)
Lemma pS_awr_pobj : forall B STK sp0 (FP : list (Z * Z)) ly S ly4 S4 (W4 : world tfibsegs) m v lo hi x,
  pobj tfibsegs B ly4 S4 W4 m v -> frames S4 = frames S -> In (lo, hi) FP -> lo <= x < hi -> v <= x < v + 56 ->
  awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x.
Proof.
intros B STK sp0 FP ly S ly4 S4 W4 m v lo hi x HPv Hfr Hin Hlh Hvx.
assert (HF : inFP FP x) by (exists (lo, hi); split; [exact Hin | cbn [fst snd]; lia]).
destruct HPv as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & m' & Hb & H1 & H2) & _)] _].
- right; right. split; [exact HF|]. exists cid, pos. split; [rewrite <- Hfr; exact Hcp|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- left. right; left. split; [exact HF|]. exists b, m'. split; [exact Hb | unfold HEAD in H1; lia].
Qed.
(* ... and a byte of a live block that is in its footprint or that the walk's callees made *)
Lemma pS_awr_blk : forall B STK sp0 (FP : list (Z * Z)) ly S ly4 S4 p nn x,
  In (p, nn) (ablocks B ly4 S4) -> p <= x < p + req_size nn ->
  inFP FP x \/ ~ In (p, nn) (ablocks B ly S) ->
  awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x.
Proof.
intros B STK sp0 FP ly S ly4 S4 p nn x Hin Hx [HF | Hn].
- left. right; left. split; [exact HF | exists p, nn; split; [exact Hin | exact Hx]].
- left. right; right; left. exists p, nn. split; [exact Hin|]. split; [exact Hn | exact Hx].
Qed.
(* a byte of an old kids / keys block (head included) is in pj_set's footprint *)
Lemma pS_inFP_old : forall o w kids keys cap aa kk x, In (aa, kk) (pS_Dold0 kids keys cap) -> 0 <= kk ->
  aa - HEAD <= x < aa + kk -> inFP (pS_FP o w kids keys cap) x.
Proof.
intros o w kids keys cap aa kk x Hin Hk Hx.
exists (aa - HEAD, aa - HEAD + req_size (kk + HEAD)). split.
- unfold pS_FP. apply in_or_app; right. apply in_or_app; left.
  unfold ablocks_fp, rd_hblocks. rewrite map_map. apply in_map_iff. exists (aa, kk). split; [reflexivity | exact Hin].
- cbn [fst snd]. unfold req_size, HEAD in *. destruct (Z.eqb_spec (kk + 16) 0); lia.
Qed.
(* fuzz/alloc.c's statics lie in the image's data, between 0x10000 and FS_IMG_END *)
Lemma pS_pstat_range : forall x, inFP FS_PSTAT_FP x -> 0x10000 <= x < FS_IMG_END.
Proof.
intros x (r & Hr & Hx). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr. unfold FS_IMG_END.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hx; lia.
Qed.
(* fuzz/alloc.c's statics read the same in two memories that agree on their bytes *)
Lemma pS_glob_eq : forall (W : world tfibsegs) m m' live peak cnt fail,
  fs_glob tfibsegs W m live peak cnt fail ->
  (forall x, inFP FS_PSTAT_FP x -> mbyte tfibsegs (mrestrict (w_H W) m') x = mbyte tfibsegs (mrestrict (w_H W) m) x) ->
  fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail (G1 & G2 & G3 & G4 & R) E.
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv j Hj.
  assert (Hin : inFP FS_PSTAT_FP (g + Z.of_nat j)) by (apply (inFP_FS_PSTAT_FP g Hg); lia).
  rewrite (E (g + Z.of_nat j) Hin). exact (Hv j Hj). }
split; [apply V; [unfold FS_PSTAT_FP; right; left; reflexivity | exact G1]|].
split; [apply V; [unfold FS_PSTAT_FP; right; right; left; reflexivity | exact G2]|].
split; [apply V; [unfold FS_PSTAT_FP; right; right; right; left; reflexivity | exact G3]|].
split; [apply V; [unfold FS_PSTAT_FP; left; reflexivity | exact G4]|].
exact R.
Qed.
(* an all-zero pj below alloc_ceiling is kept by same_below *)
Lemma pS_zero_below : forall (W : world tfibsegs) m m' v, same_below m m' alloc_ceiling -> 0 <= v ->
  v + 56 <= alloc_ceiling -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) m) v ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) m') v.
Proof.
intros W m m' v SB H0 H1 ((Hal & (Hs1 & Hs2 & Hs)) & (Hb1 & Hb2 & Hb)).
assert (E : forall a, v <= a < v + 56 ->
  mrestrict (w_H W) m' (OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa a) =
  mrestrict (w_H W) m (OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa a))
  by (intros a Ha; unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.wa;
      apply (fsw_mrestrict_belowZ (w_H W) m m' a SB); lia).
split; [split; [exact Hal|] |].
- split; [exact Hs1|]. split; [exact Hs2|]. intros a Ha. destruct (Hs a Ha) as (Hw & bb & Hr).
  split.
  + unfold wview in *. rewrite (E a Ha). exact Hw.
  + exists bb. unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd in *. rewrite (E a Ha). exact Hr.
- split; [exact Hb1|]. split; [exact Hb2|]. intros i Hi. pose proof (Hb i Hi) as Hbi.
  rewrite repeat_length in Hi. unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.mrd in *.
  rewrite (E (v + Z.of_nat i) ltac:(lia)). exact Hbi.
Qed.
(* the key string misses fuzz/alloc.c's statics: a heap string is client memory, a table string is checked
   (MEASURED: vm_compute over FS_RO_STRS and FS_SN_FMTS) *)
Lemma pS_key_off_pstat : forall B ly S (W : world tfibsegs) mx md U k (kname : list Z),
  AR tfibsegs B ly S W mx md -> cstr_kept B ly S U k kname ->
  forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ inFP FS_PSTAT_FP x.
Proof.
intros B ly S W mx md U k kname HAR Hk x Hx ((rlo, rhi) & Hr & Har). cbn [fst snd] in Har.
destruct Hk as [(b & m & Hb & Hbk & Hkm & _) | [Htbl | (ps & Hps & ->)]].
- assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  destruct (fsw_ablock_off_img B ly S W mx md b m HAR Hb) as [L | L];
    unfold FS_PSTAT_FP in Hr; cbn [In] in Hr; unfold FS_IMG_END in L;
    destruct Hr as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- assert (Hb : forallb (fun t : Z * list Z => forallb (fun s : Z * Z =>
    (fst t + Z.of_nat (length (snd t)) + 1 <=? fst s) || (snd s <=? fst t)) FS_PSTAT_FP) FS_RO_STRS = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb (k, kname) Htbl) as H1. cbn beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 (rlo, rhi) Hr) as H2. cbn [fst snd] in H2.
  apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
- assert (Hb : forallb (fun t : Z * list fpiece => forallb (fun s : Z * Z =>
    (fst t + Z.of_nat (length (fmt_bytes (snd t))) + 1 <=? fst s) || (snd s <=? fst t)) FS_PSTAT_FP) FS_SN_FMTS = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb (k, ps) Hps) as H1. cbn beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 (rlo, rhi) Hr) as H2. cbn [fst snd] in H2.
  apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
Qed.
(* the key across fuzz_strdup: its footprint is the four statics, which the key misses; the one head it adds is the
   head of a block live after it and not before (the new key block), so it misses the key (pSh_newhead_apart) *)
Lemma pS_key_after_sd : forall B (IMG : fs_img_facts tfibsegs B) sp1 ly3 S3 Ug (W3 : world tfibsegs) mem3 md3
  ly4 S4 (W4 : world tfibsegs) mem4 md4 kc a k (kname : list Z),
  ajournal tfibsegs B STK_fuzz_strdup sp1 FS_PSTAT_FP ly3 S3 W3 (unpoison Ug mem3) md3 []
    ly4 S4 W4 (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) md4 kc ->
  ARU tfibsegs B ly3 S3 Ug W3 mem3 md3 -> ARU tfibsegs B ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W4) mem4) ->
  In (a - HEAD, Z.of_nat (length kname) + 1 + HEAD) (ablocks B ly4 S4) ->
  ~ In (a - HEAD, Z.of_nat (length kname) + 1 + HEAD) (ablocks B ly3 S3) ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ inFP FS_PSTAT_FP x) ->
  cstr_kept B ly3 S3 Ug k kname -> cstr_ok tfibsegs W3 mem3 k kname ->
  cstr_ok tfibsegs W4 mem4 k kname.
Proof.
intros B IMG sp1 ly3 S3 Ug W3 mem3 md3 ly4 S4 W4 mem4 md4 kc a k kname HJ HU3 HU4 HRO4 Hn4 Hn3 HkF Hk Hc.
pose proof HU4 as (HAR4 & OK4 & PO4).
assert (HkF0 : ~ inFP FS_PSTAT_FP k) by (apply HkF; lia).
assert (SURV : forall p nn x, In (p, nn) (ablocks B ly3 S3) -> p <= x < p + req_size nn -> ~ inFP FS_PSTAT_FP x ->
  In (p, nn) (ablocks B ly4 S4)).
{ intros p nn x Hin Hx Hf.
  exact (fsw_journal_block_live B STK_fuzz_strdup sp1 FS_PSTAT_FP ly3 S3 W3 (unpoison Ug mem3) md3
    ly4 S4 W4 (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) md4 kc p nn x HJ Hin Hx Hf). }
assert (HUr : forall r, In r (Ug ++ [(a - HEAD, HEAD)]) ->
  In r Ug \/ fst r + snd r <= k \/ k + Z.of_nat (length kname) + 1 <= fst r).
{ intros r Hr. apply in_app_or in Hr as [Hr | [<- | []]]; [left; exact Hr | right].
  assert (HM : 16 <= req_size (Z.of_nat (length kname) + 1 + HEAD))
    by (unfold req_size, HEAD; destruct (Z.eqb_spec (Z.of_nat (length kname) + 1 + 16) 0); lia).
  destruct (pSh_newhead_apart B ly3 S3 Ug ly4 S4 W4 _ md4 FS_PSTAT_FP a _ k kname HAR4 Hn4 Hn3 HM Hk HkF0 SURV)
    as [L | L]; cbn [fst snd]; unfold HEAD in *; lia. }
destruct Hk as [(b & m & Hb & Hbk & Hkm & HD) | [Htbl | (ps & Hps & ->)]].
- assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hkx : b <= k < b + req_size m) by lia.
  pose proof (SURV b m k Hb Hkx HkF0) as Hb4.
  exact (FSW_strkit.cstr_ok_kept_blkU B STK_fuzz_strdup sp1 FS_PSTAT_FP ly3 S3 Ug W3 mem3 md3 []
    ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 kc k kname b m HU3 HJ OK4 PO4 Hb Hb4 Hbk Hkm HkF HUr Hc).
- exact (FSW_strkit.cstr_ok_kept_tbl B ly4 S4 _ W4 mem4 md4 k kname IMG HU4 HRO4 (or_introl Htbl)).
- exact (FSW_strkit.cstr_ok_kept_tbl B ly4 S4 _ W4 mem4 md4 k _ IMG HU4 HRO4
    (or_intror (ex_intro _ ps (conj Hps eq_refl)))).
Qed.
End GE.

(* ================= pj_set_holds: the chain ================= *)
Section MAIN. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* the image facts (FSH_Rt.v): a stated interface proved once for fs's TfibB (owner a Theorem Labs lane) *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* callees: pj_get (a Theorem Labs lane), grow (a Theorem Labs lane), fuzz_strdup (ALLOC, a Theorem Labs lane) *)
Hypothesis GET : pj_get_spec tfibsegs B.
Hypothesis GROW : grow_spec tfibsegs B.
Hypothesis SD : fuzz_strdup_spec tfibsegs B.
(* the runtime's realizers __asan_memcpy / __asan_memset (FSH_Rt.FsRt's fr_memcpy / fr_memset field types, nothing
   else of FsRt), a stated interface of the fs unit (owner: RUNTIME, a Theorem Labs lane, as fs_img_facts) *)
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis RT_memset : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

Theorem pj_set_holds : pj_set_spec tfibsegs B.
Proof.
unfold pj_set_spec. intros ly S U W regs mem md ch o k w ms tv D Dw num str kids keys n cap kname live peak cnt fail.
cbv zeta.
intros HPRE HHEADS R10 R11 R12 HTo HPo HHo Hcap HINC HTw HPw HDw Hfootw Hapart HPLo HPLw HK HKk Hfootk HKEY
  HG HQT HRS Hkl HMX HLV HEV HBB.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as ((AC1 & AC2) & _).
pose proof HPRE as ((HAP & HUOK & HUP) & HRO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & _).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem o HAR HPo) as (Lo1 & Lo2).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem w HAR HPw) as (Lw1 & Lw2).
pose proof HK as (_ & Hk4096 & Hkhi & _).
assert (STK48 : 48 <= STK_pj_set) by (vm_compute; congruence).
set (FP := pS_FP o w kids keys cap).
(* ---- stage A, to the pj_get call ---- *)
assert (Ho64 : 0 <= o < 2 ^ 64) by lia. assert (Hk64 : 0 <= k < 2 ^ 64) by lia. assert (Hw64 : 0 <= w < 2 ^ 64) by lia.
apply (pj_set_stageA B HSS ly S U W regs mem md ch FP o k w _ (proj1 HPRE) R10 R11 R12 Ho64 Hk64 Hw64).
intros regsC memC mat HC HJ HARU SB.
(* ---- the pj_get call, to stage B's resume state ---- *)
assert (HXS : firstn 6 (skipn 9 (pj_xs cnt fail live peak 6 kids keys n cap regs))
  = map (YK11.getr regs) pj_set_saved_regs)
  by (unfold pj_xs, pj_fields, pj_set_saved_regs; cbn [app map firstn skipn]; reflexivity).
apply (pj_set_get_call B HSS GET ly S U W regs mem md ch FP o k w ms D tv Dw kname live peak cnt fail regsC memC mat
  _ num str kids keys n cap _ HPRE HHEADS HTo HPo HHo HTw HPw HK HKk HKEY HG HC HJ HARU SB HXS).
intros ly1 S1 W1 regs1 mem1 md1 HJ1 HARU1 HS1 Hsp1 Ha01 HP1 Hbl1 HH1 HTo1 HPo1 HTw1 HPw1 HK1 HKk1 HG1 HRO1 HHo1.
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & Hfrs1 & Hnev1 & _).
destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md ly1 HAR Hly1) as (_ & HFA1 & _).
(* obj opened at mem1 (the released plain proof's lemma, generic in the memory) *)
pose proof HTo1 as (HN1 & HBK1 & _).
destruct (pj_set_shape.ps_node_open tfibsegs _ _ o ms D num str kids keys n cap HN1 HHo1 Hcap)
  as (Di & ED & Estr & En & HOPEN1).
rewrite pS_slots_Dold0 in ED.
(* ---- stage B, to the grow call ---- *)
apply (pj_set_stageB B ly S W (unpoison U mem) md [] ly1 S1 U W1 regs regs1 mem1 md1 STK_pj_set (spZ regs) FP 0
  cnt fail live peak 6 kids keys n cap _ Ha01 HS1 HJ1 HARU1 Hsp1 STK48).
intros regsC2 memC2 mat2 (R1g & Rsp2 & Rkeep2 & HFR2) Hargs2 SB2 HJ2 HARU2.
destruct HC as (RC1 & RCsp & RC10 & RC11 & RC8 & RC9 & RC18 & RC20 & RCkeep & HCfr).
rewrite Forall_forall in Rkeep2, RCkeep.
assert (R9g1 : YK11.getr regs1 9 = w64 o)
  by (rewrite (fsw_pres regsC regs1 9%bv HP1 ltac:(unfold acallee_saved; vm_compute; lia)); exact RC9).
assert (R8g1 : YK11.getr regs1 8 = w64 w)
  by (rewrite (fsw_pres regsC regs1 8%bv HP1 ltac:(unfold acallee_saved; vm_compute; lia)); exact RC8).
assert (R3g : YK11.getr regsC2 3 = w64 (as_gp B)).
{ rewrite (Rkeep2 3%bv ltac:(cbn; tauto)), (fsw_pres regsC regs1 3%bv HP1 ltac:(unfold acallee_saved; vm_compute; lia)),
    (RCkeep 3%bv ltac:(cbn; tauto)). exact Hgp. }
assert (R4g : YK11.getr regsC2 4 = w64 (as_tp B)).
{ rewrite (Rkeep2 4%bv ltac:(cbn; tauto)), (fsw_pres regsC regs1 4%bv HP1 ltac:(unfold acallee_saved; vm_compute; lia)),
    (RCkeep 4%bv ltac:(cbn; tauto)). exact Htp. }
assert (R10g : YK11.getr regsC2 10 = w64 o) by (unfold pB_args in Hargs2; rewrite Hargs2; exact R9g1).
assert (R8g : YK11.getr regsC2 8 = w64 w) by (rewrite (Rkeep2 8%bv ltac:(cbn; tauto)); exact R8g1).
assert (Rspg : spZ regsC2 = spZ regs - 48) by lia.
replace (spZ regs1 + 48) with (spZ regs) in HFR2 by lia.
(* the data at the grow call *)
assert (HSUB : forall bk, In bk (pS_Dold0 kids keys cap) -> In bk D) by (intros bk Hb; rewrite ED; apply in_or_app; left; exact Hb).
assert (HSLOT : PjStruct.pj_slots_at (fun a kk => In (a, kk) (pS_Dold0 kids keys cap)) 6 kids keys n cap)
  by (destruct HOPEN1 as (_ & _ & _ & Hs & _); exact (pS_slots_at_Dold0 D kids keys n cap Hs)).
assert (HBO2 : rd_blocks_ok tfibsegs B ly1 S1 W1 memC2 (pS_Dold0 kids keys cap)).
{ apply (rd_blocks_ok_below B ly1 S1 W1 (unpoison U mem1) md1 mem1 memC2 _ HAR1 SB2).
  intros aa kk Hin. exact (HBK1 aa kk (HSUB _ Hin)). }
assert (HAPD : PjStruct.pj_apart (pS_Dold0 kids keys cap) o)
  by (destruct HN1 as (_ & HA & _); intros b x Hb; exact (HA b x (HSUB b Hb))).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) memC2))
  by exact (arodata_below B W1 mem1 memC2 SB2 HRO1).
assert (HPo2 : pobj tfibsegs B ly1 S1 W1 memC2 o)
  by exact (pobj_below B ly1 S1 W1 (unpoison U mem1) md1 mem1 memC2 o HAR1 SB2 HPo1).
assert (HPw2 : pobj tfibsegs B ly1 S1 W1 memC2 w)
  by exact (pobj_below B ly1 S1 W1 (unpoison U mem1) md1 mem1 memC2 w HAR1 SB2 HPw1).
assert (HHo2 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W1) memC2) o 6 num str kids keys n cap)
  by exact (pS_hdr_below W1 mem1 memC2 o 6 num str kids keys n cap SB2 ltac:(lia) Lo2 HHo1).
assert (HG2 : fs_glob tfibsegs W1 memC2 live peak cnt fail)
  by exact (fs_glob_below W1 mem1 memC2 live peak cnt fail SB2 HG1).
assert (Hcap0 : 0 <= cap) by (destruct HHo as (_ & _ & _ & _ & _ & _ & _ & (Hc & _)); lia).
assert (Hklen0 : 0 <= Z.of_nat (length kname)) by lia.
assert (HQTg : quiet cnt fail (Z.of_nat (length (grow_tr 6 n cap)))).
{ apply (pSn_quiet_mono cnt fail _ _ HQT). pose proof (pSn_len_le n cap (Z.of_nat (length kname))). lia. }
assert (HLVg : live + rd_live (grow_tr 6 n cap) < 2 ^ 64)
  by (rewrite (pSn_live_split n cap _ Hklen0) in HLV; unfold HEAD in HLV; lia).
assert (HEVg : st_nev S1 + rd_ev (grow_tr 6 n cap) <= EV_MAX)
  by (rewrite (pSn_ev_split n cap _ Hcap0) in HEV; unfold EV_fuzz_malloc in HEV; lia).
assert (HBBg : blocks_bytes S1 + rd_live (grow_tr 6 n cap) <= LIVE_MAX).
{ rewrite (pSn_bb_eq B ly1 S1 ly S Hbl1). rewrite (pSn_live_split n cap _ Hklen0) in HBB. unfold HEAD in HBB. lia. }
(* ---- the grow call, to stage C's resume state ---- *)
apply (pj_set_grow_call B HSS GROW ly S U W regs mem md ly1 S1 W1 memC2 (with_vm_backing (m_vm_lazy md1) mat2 md1)
  regsC2 o w num str kids keys n cap live peak cnt fail _ HJ2 HARU2 HH1 HRO2 Rspg R1g R10g R8g R3g R4g HFR2 HFA1
  HPo2 HHo2 HSLOT HBO2 HAPD HINC HPLo HPw2 HG2 HQTg HRS HMX HLVg HEVg HBBg).
intros ly3 S3 Ug W3 regs3 mem3 md3 k' y' cap' Dold Dnew peak3 HGR HJ3 HARU3 HS3 Hsp3 Ha03 HP3 HPERM HHDR HSLOT3
  HBLK HMVK HMVY HPO3 Hpk HG3 KEPTg LIVEg HRO3 HJg.
(* ---- stage C, to the fuzz_strdup call ---- *)
apply (pj_set_stageC B ly S W (unpoison U mem) md [] ly3 S3 Ug W3 regs regs3 mem3 md3 STK_pj_set (spZ regs) FP
  (rd_ev (grow_tr 6 n cap)) cnt fail live peak 6 k' y' n cap' _ Ha03 HS3 HJ3 HARU3 Hsp3 STK48).
intros regsC3 memC3 mat3 (R1c & Rsp3c & Rkeep3 & HFR3) Hargs3 SB3 HJ3c HARU3c.
rewrite Forall_forall in Rkeep3.
pose proof HARU3 as (HAR3 & OK3 & PO3).
pose proof HARU2 as (HAR2 & _ & _).
(* ---- the registers at the fuzz_strdup call: every callee-saved one back to stage A's call ---- *)
assert (RG : forall r, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  YK11.getr regsC3 r = YK11.getr regsC r).
{ intros r Hr. rewrite (Rkeep3 r Hr), (pS_pres regsC2 regs3 r HP3 Hr), (Rkeep2 r Hr), (pS_pres regsC regs1 r HP1 Hr).
  reflexivity. }
assert (R10s : YK11.getr regsC3 10 = w64 k).
{ unfold pC_args in Hargs3. rewrite Hargs3, (pS_pres regsC2 regs3 18%bv HP3 ltac:(cbn; tauto)),
    (Rkeep2 18%bv ltac:(cbn; tauto)), (pS_pres regsC regs1 18%bv HP1 ltac:(cbn; tauto)). exact RC18. }
assert (R9s : YK11.getr regsC3 9 = w64 o) by (rewrite (RG 9%bv ltac:(cbn; tauto)); exact RC9).
assert (R8s : YK11.getr regsC3 8 = w64 w) by (rewrite (RG 8%bv ltac:(cbn; tauto)); exact RC8).
assert (R20s : YK11.getr regsC3 20 = w64 SHADOW_OFF) by (rewrite (RG 20%bv ltac:(cbn; tauto)); exact RC20).
assert (R3s : YK11.getr regsC3 3 = w64 (as_gp B))
  by (rewrite (RG 3%bv ltac:(cbn; tauto)), (RCkeep 3%bv ltac:(cbn; tauto)); exact Hgp).
assert (R4s : YK11.getr regsC3 4 = w64 (as_tp B))
  by (rewrite (RG 4%bv ltac:(cbn; tauto)), (RCkeep 4%bv ltac:(cbn; tauto)); exact Htp).
assert (Rsps : spZ regsC3 = spZ regs - 48) by lia.
replace (spZ regs3 + 48) with (spZ regs) in HFR3 by lia.
(* ---- the key, obj and val across grow ---- *)
assert (HINCD : incl (pS_Dold0 kids keys cap) D) by (intros bk Hb; exact (HSUB bk Hb)).
assert (HfootkD : forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ PjStruct.pj_foot o D x)
  by (intros x Hx; exact (proj1 (Hfootk x Hx))).
assert (HkFg : forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ inFP (pS_FPg o kids keys cap) x).
{ destruct HKk1 as [(b & m & Hb & Hbk & Hkm & HD) | Htbl].
  - exact (pS_key_off_FPg B ly1 S1 W1 (unpoison U mem1) md1 memC2 U o D kids keys cap k kname b m
      HAR1 HINC HINCD HfootkD Hb Hbk Hkm HD HBO2).
  - apply (pS_key_off_FPg_tbl B ly1 S1 W1 (unpoison U mem1) md1 memC2 memC2 o kids keys cap k kname HAR1 HPo2 HBO2).
    destruct Htbl as [Hs | (ps & Hps & ->)]; [left; exact Hs | right; exists ps; split; [exact Hps | reflexivity]]. }
assert (HFRg : n = cap -> ~ In (k' - HEAD, 56 * cap' + HEAD) (ablocks B ly1 S1) /\
                          ~ In (y' - HEAD, 8 * cap' + HEAD) (ablocks B ly1 S1))
  by exact (pSh_fresh_after_grow B ly1 S1 ly3 S3 W3 (unpoison Ug mem3) md3 n cap kids keys k' y' cap' Dold Dnew U Ug
              HAR3 HGR HPERM).
destruct (pS_key_after_grow B IMG (spZ regs - 48) ly1 S1 U W1 memC2 (wvb md1 mat2) ly3 S3 Ug W3 mem3 md3
  (rd_ev (grow_tr 6 n cap)) o n cap kids keys k' y' cap' Dold Dnew k kname HJg HARU2 HARU3 HRO3 HGR HBLK HFRg LIVEg
  HkFg HKk1 (cstr_ok_below W1 mem1 memC2 k kname SB2 HK1)) as (HK3 & HKk3).
assert (HH3 : FSupoisonU.fs_heads B ly3 S3 Ug)
  by exact (pSh_heads_after_grow B ly1 S1 U ly3 S3 Ug W1 W3 memC2 mem3 (wvb md1 mat2) md3 o kids keys n cap
              k' y' cap' Dold Dnew HARU2 HARU3 HH1 HGR HINC HBO2 HBLK LIVEg
              (pSh_obj_apart B ly1 S1 W1 (unpoison U memC2) (wvb md1 mat2) memC2 o HAR2 HPo2)).
assert (HPw3 : pobj tfibsegs B ly3 S3 W3 mem3 w)
  by exact (pobj_kept_call B STK_grow (spZ regs - 48) (pS_FPg o kids keys cap) ly1 S1 U W1 memC2 (wvb md1 mat2)
              ly3 S3 Ug W3 mem3 md3 (rd_ev (grow_tr 6 n cap)) w HJg HARU2 OK3 PO3
              (pS_pobj_off_FPg B ly1 S1 W1 (unpoison U memC2) (wvb md1 mat2) memC2 memC2 o w kids keys cap D
                 HAR2 HPw2 HBO2 HINCD Hfootw)
              (pS_FPg_off_shadow B ly1 S1 W1 (unpoison U memC2) (wvb md1 mat2) memC2 memC2 o kids keys cap HAR2 HPo2 HBO2)
              HH3 HPw2).
(* ---- the data at the fuzz_strdup call (stage C wrote only its frame, above alloc_ceiling) ---- *)
assert (HPoD : pobj tfibsegs B ly3 S3 W3 memC3 o)
  by exact (pobj_below B ly3 S3 W3 (unpoison Ug mem3) md3 mem3 memC3 o HAR3 SB3 HPO3).
assert (HPwD : pobj tfibsegs B ly3 S3 W3 memC3 w)
  by exact (pobj_below B ly3 S3 W3 (unpoison Ug mem3) md3 mem3 memC3 w HAR3 SB3 HPw3).
destruct (fsw_pobj_low B ly3 S3 W3 (unpoison Ug mem3) md3 mem3 o HAR3 HPO3) as (Lo3 & Lo4).
assert (HHoD : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) memC3) o 6 num str k' y' n cap')
  by exact (pS_hdr_below W3 mem3 memC3 o 6 num str k' y' n cap' SB3 ltac:(lia) Lo4 HHDR).
pose proof HHoD as (_ & _ & _ & _ & (Hk'r & _) & (Hy'r & _) & (Hnr & _) & (Hcapr & _)).
assert (HGD : fs_glob tfibsegs W3 memC3 (live + PjGrammar.held (grow_tr 6 n cap)) peak3
  (cnt + Z.of_nat (length (grow_tr 6 n cap))) fail) by exact (fs_glob_below W3 mem3 memC3 _ _ _ _ SB3 HG3).
assert (HKD : cstr_ok tfibsegs W3 memC3 k kname) by exact (cstr_ok_below W3 mem3 memC3 k kname SB3 HK3).
assert (HROD : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) memC3))
  by exact (arodata_below B W3 mem3 memC3 SB3 HRO3).
(* ---- fuzz_strdup's budget: what pj_set_spec gave for its whole trace, less grow's part ---- *)
pose proof HQT as (Hfail & Hcnt0 & Hcntlt).
rewrite (pSn_len_split n cap (Z.of_nat (length kname))) in Hcntlt.
assert (SMZ : SIZE_MAXZ = 18446744073709551615) by reflexivity.
assert (HCF : cnt + Z.of_nat (length (grow_tr 6 n cap)) <> fail) by (rewrite Hfail, SMZ; lia).
assert (HLVs : live + PjGrammar.held (grow_tr 6 n cap) + (Z.of_nat (length kname) + 1) < 2 ^ 64).
{ pose proof (pSn_held_le_live (grow_tr 6 n cap)). rewrite (pSn_live_split n cap _ Hklen0) in HLV.
  unfold HEAD in HLV. lia. }
assert (HCNs : cnt + Z.of_nat (length (grow_tr 6 n cap)) + 1 < 2 ^ 64) by lia.
assert (HEVs : st_nev S3 + 1 <= EV_MAX).
{ pose proof HJ3c as (_ & _ & _ & _ & _ & _ & Hnev3 & _). rewrite (pSn_ev_split n cap _ Hcap0) in HEV.
  unfold EV_fuzz_malloc in HEV. lia. }
assert (HBBs : blocks_bytes S3 + (Z.of_nat (length kname) + 1 + HEAD) <= LIVE_MAX).
{ pose proof (pSn_bb_after_grow B ly1 S1 ly3 S3 Dold Dnew HPERM) as E1.
  destruct (pSn_bb_grow_bound n cap kids keys k' y' cap' Dold Dnew U Ug HGR Hcap0) as (G1 & G2).
  rewrite (pSn_bb_eq B ly1 S1 ly S Hbl1) in E1.
  rewrite (pSn_live_split n cap _ Hklen0) in HBB. lia. }
(* ---- the fuzz_strdup call, to stage D's resume state ---- *)
apply (pj_set_sd_call B HSS SD ly S U W regs mem md ly3 S3 Ug W3 memC3 (wvb md3 mat3) (rd_ev (grow_tr 6 n cap)) regsC3
  o k w kids keys cap num str k' y' cap' n kname
  (live + PjGrammar.held (grow_tr 6 n cap)) peak3 (cnt + Z.of_nat (length (grow_tr 6 n cap))) fail _
  HJ3c HARU3c HH3 HROD Rsps R1c R10s R9s R8s R20s R3s R4s HFR3 HKD HKk3 HPoD HPwD HHoD Hk'r Hy'r Hnr Hcapr
  HGD HCF HLVs HCNs Hkl HEVs HBBs).
intros ly4 S4 W4 regs4 mem4 md4 a HJ4 HARU4 HS4 Hsp4 HP4 R10' Ha4096 HAB4 HH4 HRB4 HZB4 HG4 KEPTs HRO4 HJs.
pose proof HARU4 as (HAR4 & OK4 & PO4).
pose proof HARU3c as (HAR3c & _ & _).
(* ---- the registers at 0x83998 ---- *)
assert (R9t : YK11.getr regs4 9 = w64 o) by (rewrite (pS_pres regsC3 regs4 9%bv HP4 ltac:(cbn; tauto)); exact R9s).
assert (R8t : YK11.getr regs4 8 = w64 w) by (rewrite (pS_pres regsC3 regs4 8%bv HP4 ltac:(cbn; tauto)); exact R8s).
assert (R20t : YK11.getr regs4 20 = w64 SHADOW_OFF)
  by (rewrite (pS_pres regsC3 regs4 20%bv HP4 ltac:(cbn; tauto)); exact R20s).
assert (RKt : Forall (fun r => YK11.getr regs4 r = YK11.getr regs r) [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv).
{ apply Forall_forall. intros r Hr.
  rewrite (pS_pres regsC3 regs4 r HP4 ltac:(cbn in Hr |- *; tauto)), (RG r ltac:(cbn in Hr |- *; tauto)),
    (RCkeep r ltac:(cbn in Hr |- *; tauto)). reflexivity. }
(* ---- obj and val across fuzz_strdup (its footprint is the four statics, image bytes) ---- *)
assert (HPo4 : pobj tfibsegs B ly4 S4 W4 mem4 o)
  by exact (pobj_kept_call B STK_fuzz_strdup (spZ regs - 48) FS_PSTAT_FP ly3 S3 Ug W3 memC3 (wvb md3 mat3)
              ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 1 o HJs HARU3c OK4 PO4
              (pS_pobj_off_pstat B ly3 S3 W3 (unpoison Ug memC3) (wvb md3 mat3) memC3 o HAR3c HPoD)
              pS_pstat_off_shadow HH4 HPoD).
assert (HPw4 : pobj tfibsegs B ly4 S4 W4 mem4 w)
  by exact (pobj_kept_call B STK_fuzz_strdup (spZ regs - 48) FS_PSTAT_FP ly3 S3 Ug W3 memC3 (wvb md3 mat3)
              ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 mem4 md4 1 w HJs HARU3c OK4 PO4
              (pS_pobj_off_pstat B ly3 S3 W3 (unpoison Ug memC3) (wvb md3 mat3) memC3 w HAR3c HPwD)
              pS_pstat_off_shadow HH4 HPwD).
(* ---- frames: no call made or freed one ---- *)
pose proof HJ4 as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
pose proof HJg as (_ & Hly3 & _ & _ & _ & Hfrs3 & _). cbn [app] in Hfrs3.
destruct (al_layout tfibsegs B LAWS ly1 S1 W1 (unpoison U memC2) (wvb md1 mat2) ly3 HAR2 Hly3) as (_ & HFA3 & _).
(* ---- the new kids / keys blocks: kids[n] and keys[n] are inside them ---- *)
assert (Hncap : n < cap').
{ destruct HGR as [(Hlt & _ & _ & Ec & _) | (Enc & Ec & _)]; rewrite Ec;
    [lia | unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia]. }
assert (Hcap'0 : cap' <> 0) by lia.
pose proof HBLK as HBLK'. rewrite (pSh_blk_ne0 k' y' cap' Hcap'0) in HBLK'.
destruct (HBLK' k' (56 * cap') (or_introl eq_refl)) as (HinK & HkA & _ & _).
destruct (HBLK' y' (8 * cap') (or_intror (or_introl eq_refl))) as (HinY & HyA & _ & _).
assert (HinK4 : In (k' - HEAD, 56 * cap' + HEAD) (ablocks B ly4 S4)) by (rewrite HAB4; apply in_or_app; left; exact HinK).
assert (HinY4 : In (y' - HEAD, 8 * cap' + HEAD) (ablocks B ly4 S4)) by (rewrite HAB4; apply in_or_app; left; exact HinY).
assert (Hrq : forall z, 0 <= z -> req_size (z + HEAD) = z + HEAD)
  by (intros z Hz; unfold req_size, HEAD; destruct (Z.eqb_spec (z + 16) 0); lia).
assert (HKY : zdisjoint (k' - HEAD, req_size (56 * cap' + HEAD)) (y' - HEAD, req_size (8 * cap' + HEAD))).
{ apply (sep_blocks tfibsegs B LAWS ly3 S3 W3 (unpoison Ug mem3) md3 _ _ _ _ HAR3 HinK HinY).
  intros E. injection E as _ E2. lia. }
unfold zdisjoint in HKY. cbn [fst snd] in HKY. rewrite !Hrq in HKY by lia.
(* ---- obj and val apart from kids[n] / keys[n], and from each other ---- *)
assert (HoFg : ~ inFP (pS_FPg o kids keys cap) o)
  by exact (pS_obj_off_FPg0 B ly1 S1 W1 (unpoison U memC2) (wvb md1 mat2) memC2 memC2 o kids keys cap HAR2 HPo2 HBO2 HAPD).
assert (HwFg : ~ inFP (pS_FPg o kids keys cap) w)
  by (apply (pS_pobj_off_FPg B ly1 S1 W1 (unpoison U memC2) (wvb md1 mat2) memC2 memC2 o w kids keys cap D
               HAR2 HPw2 HBO2 HINCD Hfootw); lia).
assert (HAPART : forall c M, In (c, M) (ablocks B ly3 S3) -> In (c + HEAD, M - HEAD) (pS_Dold0 kids keys cap) \/
    ~ In (c, M) (ablocks B ly1 S1) -> 0 <= M - HEAD ->
  forall lo len, c + HEAD <= lo -> lo + len <= c + M -> 0 < len ->
  (lo + len <= o \/ o + 56 <= lo) /\ (lo + len <= w \/ w + 56 <= lo)).
{ intros c M Hc3 [HcD | Hc1] HM lo len Hlo Hhi Hlen.
  - split.
    + apply pS_apart_of; [lia | lia |]. intros x Hx Ho.
      refine (HAPD (c + HEAD, M - HEAD) x HcD _ Ho). unfold PjStruct.pj_holds. cbn [fst snd]. lia.
    + destruct (pS_apart_of w 56 lo len ltac:(lia) Hlen) as [H | H]; [| right; lia | left; lia].
      intros x Hx Hl. apply (Hfootw x Hx). right. exists (c + HEAD, M - HEAD).
      split; [exact (HINCD _ HcD) | unfold PjStruct.pj_holds; cbn [fst snd]; lia].
  - assert (HM' : req_size M = M) by (replace M with ((M - HEAD) + HEAD) by lia; apply Hrq; exact HM).
    split.
    + destruct (pS_new_apart B ly1 S1 ly3 S3 W1 W3 (unpoison Ug mem3) md3 memC2 o (pS_FPg o kids keys cap) c M
        HAR3 HPo2 Hfrs3 HFA3 HoFg LIVEg Hc3 Hc1) as [H | H]; try rewrite HM' in H; unfold HEAD in *; lia.
    + destruct (pS_new_apart B ly1 S1 ly3 S3 W1 W3 (unpoison Ug mem3) md3 memC2 w (pS_FPg o kids keys cap) c M
        HAR3 HPw2 Hfrs3 HFA3 HwFg LIVEg Hc3 Hc1) as [H | H]; try rewrite HM' in H; unfold HEAD in *; lia. }
assert (HOLD : forall c M, (c = k' - HEAD /\ M = 56 * cap' + HEAD) \/ (c = y' - HEAD /\ M = 8 * cap' + HEAD) ->
  In (c + HEAD, M - HEAD) (pS_Dold0 kids keys cap) \/ ~ In (c, M) (ablocks B ly1 S1)).
{ intros c M HcM. destruct HGR as [(Hlt & Ek & Ey & Ec & _) | (Enc & _)].
  - left. assert (Hc0 : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold pS_Dold0, ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite Hc0. cbn [app In].
    destruct HcM as [(-> & ->) | (-> & ->)]; [left | right; left]; f_equal; lia.
  - right. destruct (HFRg Enc) as (F1 & F2). destruct HcM as [(-> & ->) | (-> & ->)]; assumption. }
destruct (HAPART (y' - HEAD) (8 * cap' + HEAD) HinY (HOLD _ _ (or_intror (conj eq_refl eq_refl))) ltac:(lia)
  (y' + 8 * n) 8 ltac:(unfold HEAD; lia) ltac:(lia) ltac:(lia)) as (Dso & Dsw).
destruct (HAPART (k' - HEAD) (56 * cap' + HEAD) HinK (HOLD _ _ (or_introl (conj eq_refl eq_refl))) ltac:(lia)
  (k' + 56 * n) 56 ltac:(unfold HEAD; lia) ltac:(lia) ltac:(lia)) as (Ddo & Ddw).
assert (Dwo : w + 56 <= o \/ o + 56 <= w).
{ apply pS_apart_of; [lia | lia |]. intros x Hx Ho. apply (Hfootw x Hx). left. exact Ho. }
(* ---- the key at fuzz_strdup's return ---- *)
assert (HnewA : ~ In (a - HEAD, Z.of_nat (length kname) + 1 + HEAD) (ablocks B ly3 S3)).
{ intros Hin. pose proof (pSh_ablocks_nodup B ly4 S4 W4 _ _ HAR4) as ND. rewrite HAB4 in ND.
  apply (List.NoDup_remove_2 (ablocks B ly3 S3) [] _ ND). rewrite app_nil_r. exact Hin. }
assert (HK4 : cstr_ok tfibsegs W4 mem4 k kname)
  by exact (pS_key_after_sd B IMG (spZ regs - 48) ly3 S3 Ug W3 memC3 (wvb md3 mat3) ly4 S4 W4 mem4 md4 1 a k kname
              HJs HARU3c HARU4 HRO4 (proj1 HRB4) HnewA
              (pS_key_off_pstat B ly3 S3 W3 _ _ Ug k kname HAR3c HKk3) HKk3 HKD).
(* ---- the tail: stage D, the memcpy, stage E, the memset, stage F, the ret (FSW_pj_set_tail.pS_tail) ---- *)
destruct (fsw_ablock_low B ly4 S4 W4 _ _ _ _ HAR4 (proj1 HRB4)) as (La1 & La2 & _).
assert (Ha47 : 4096 + HEAD <= a < 2 ^ 47).
{ split; [exact Ha4096|]. assert (Hp47 : (2:Z) ^ 47 = 140737488355328) by reflexivity.
  assert (Hrqa : req_size (Z.of_nat (length kname) + 1 + HEAD) = Z.of_nat (length kname) + 1 + HEAD) by (apply Hrq; lia).
  rewrite Hrqa in La2. unfold HEAD in *. lia. }
assert (Hs8 : (y' + 8 * n) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in HyA; [|lia]. destruct HyA as [q Hq]. exists (2 * q + n). lia. }
assert (HSB : exists p nn, In (p, nn) (ablocks B ly4 S4) /\ p + HEAD <= y' + 8 * n /\ y' + 8 * n + 8 <= p + req_size nn).
{ exists (y' - HEAD), (8 * cap' + HEAD). split; [exact HinY4|]. rewrite Hrq by lia. lia. }
assert (HDB : exists p nn, In (p, nn) (ablocks B ly4 S4) /\ p + HEAD <= k' + 56 * n /\
  k' + 56 * n + 56 <= p + req_size nn).
{ exists (k' - HEAD), (56 * cap' + HEAD). split; [exact HinK4|]. rewrite Hrq by lia. lia. }
assert (Dds : k' + 56 * n + 56 <= y' + 8 * n \/ y' + 8 * n + 8 <= k' + 56 * n) by (unfold HEAD in HKY; lia).
assert (AWB : forall c M, (c = k' - HEAD /\ M = 56 * cap' + HEAD) \/ (c = y' - HEAD /\ M = 8 * cap' + HEAD) ->
  In (c, M) (ablocks B ly4 S4) -> forall x, c <= x < c + M ->
  awr_byte tfibsegs B STK_pj_set (spZ regs) FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x).
{ intros c M HcM Hin4 x Hx.
  assert (HM : 0 <= M - HEAD) by (destruct HcM as [(_ & ->) | (_ & ->)]; lia).
  apply (pS_awr_blk B STK_pj_set (spZ regs) FP ly S ly4 S4 c M x Hin4).
  { replace M with ((M - HEAD) + HEAD) by lia. rewrite Hrq by exact HM. lia. }
  destruct (HOLD c M HcM) as [HD0 | Hn1].
  - left. apply (pS_inFP_old o w kids keys cap (c + HEAD) (M - HEAD) x HD0 HM). lia.
  - right. rewrite <- Hbl1. exact Hn1. }
pose (Qf := fun (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) =>
  ly' = ly4 /\ S' = S4 /\ W' = W4 /\ YK11.getr regs' 10 = w64 0 /\
  exists m5 m6 m6' m7,
    val_mem tfibsegs (mrestrict (w_H W4) m5) (y' + 8 * n) 8 a /\
    val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 24) 8 k' /\
    val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 32) 8 y' /\
    val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 40) 8 (n + 1) /\
    val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 48) 8 cap' /\
    (forall x, 0 <= x < alloc_ceiling -> ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
       m5 (Z_to_bv 64 x) = mem4 (Z_to_bv 64 x)) /\
    (forall i, 0 <= i < 56 ->
       aview tfibsegs (w_H W4) m6 (k' + 56 * n + i) = aview tfibsegs (w_H W4) m5 (w + i)) /\
    (forall x, 0 <= x < alloc_ceiling -> ~ (k' + 56 * n <= x < k' + 56 * n + 56) ->
       aview tfibsegs (w_H W4) m6 x = aview tfibsegs (w_H W4) m5 x) /\
    same_below m6 m6' alloc_ceiling /\
    (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m7 (w + i) = Some 0) /\
    (forall x, 0 <= x < alloc_ceiling -> ~ (w <= x < w + 56) ->
       aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m6' x) /\
    same_below m7 mem' alloc_ceiling).
eapply SRr_mono.
{ apply (pS_tail B HSS RT_memcpy RT_memset ly S U W regs mem md ly4 S4 (Ug ++ [(a - HEAD, HEAD)]) W4 regs4 mem4 md4
    (rd_ev (grow_tr 6 n cap) + 1) FP (cnt + Z.of_nat (length (grow_tr 6 n cap))) fail
    (live + PjGrammar.held (grow_tr 6 n cap)) peak3 k' y' n cap' o w a Qf
    Hra Hgp Htp HJ4 HARU4 HH4 HS4 Hsp4 R9t R8t R10' R20t RKt HPo4 HPw4 Ha47 (proj1 (proj2 HRB4))
    Hy'r (proj1 Hnr) (proj1 Hk'r) Hcapr HSB Hs8 HDB Dso Dsw Ddo Ddw Dds Dwo).
  - intros x Hx. exact (AWB (y' - HEAD) (8 * cap' + HEAD) (or_intror (conj eq_refl eq_refl)) HinY4 x
      ltac:(unfold HEAD in *; lia)).
  - intros x Hx. apply (pS_awr_pobj B STK_pj_set (spZ regs) FP ly S ly4 S4 W4 mem4 o (o + 24) (o + 56) x HPo4 Hfrs4);
      [unfold FP, pS_FP; left; reflexivity | lia | lia].
  - intros x Hx. exact (AWB (k' - HEAD) (56 * cap' + HEAD) (or_introl (conj eq_refl eq_refl)) HinK4 x
      ltac:(unfold HEAD in *; lia)).
  - intros x Hx. apply (pS_awr_pobj B STK_pj_set (spZ regs) FP ly S ly4 S4 W4 mem4 w w (w + 56) x HPw4 Hfrs4);
      [unfold FP, pS_FP; right; left; reflexivity | lia | lia].
  - intros m5 m6 m6' m7 regsF memF mdF V1 V2 V3 V4 V5 M5 C6 M6 SB6 Z7 M7 SBF RF.
    unfold Qf. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RF|].
    exists m5, m6, m6', m7. repeat split; assumption. }
intros W' c' _ HP.
destruct HP as (ly' & S' & regsF & memF & mdF & Ec & HJf & OKf & POf & HPf & HQf).
destruct HQf as (-> & -> & -> & RF & m5 & m6 & m6' & m7 & V1 & V2 & V3 & V4 & V5 & M5 & C6 & M6 & SB6 & Z7 & M7 & SBF).
(* ---- the data side (FSW_pj_set_fn.pSf_post) ---- *)
assert (M7' : forall x, 0 <= x < alloc_ceiling -> ~ (w <= x < w + 56) ->
  aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m6 x).
{ intros x Hx Hw. rewrite (M7 x Hx Hw). unfold aview, mbyte, mrestrict. rewrite (SB6 x Hx). reflexivity. }
assert (G5 : forall x, 0 <= x < alloc_ceiling ->
  mbyte tfibsegs (mrestrict (w_H W4) mem4) x <> None -> mbyte tfibsegs (mrestrict (w_H W4) m5) x <> None).
{ intros x Hx H4.
  assert (S5 : forall a0 v, val_mem tfibsegs (mrestrict (w_H W4) m5) a0 8 v -> a0 <= x < a0 + 8 ->
    mbyte tfibsegs (mrestrict (w_H W4) m5) x <> None).
  { intros a0 v Hv Hr. assert (Hr8 : a0 <= x < a0 + Z.of_nat 8) by (change (Z.of_nat 8) with 8; lia).
    destruct (fn_val_some _ a0 8 v Hv x Hr8) as (bb & Eb). rewrite Eb. discriminate. }
  assert (Dsl : (y' + 8 * n <= x < y' + 8 * n + 8) \/ ~ (y' + 8 * n <= x < y' + 8 * n + 8)) by lia.
  assert (Dob : (o + 24 <= x < o + 56) \/ ~ (o + 24 <= x < o + 56)) by lia.
  destruct Dsl as [Ds | Ds]; [exact (S5 _ _ V1 Ds)|].
  destruct Dob as [Dob | Dob].
  - assert (D4 : o + 24 <= x < o + 32 \/ o + 32 <= x < o + 40 \/ o + 40 <= x < o + 48 \/ o + 48 <= x < o + 56) by lia.
    destruct D4 as [D4 | [D4 | [D4 | D4]]];
      [exact (S5 _ _ V2 ltac:(lia)) | exact (S5 _ _ V3 ltac:(lia)) | exact (S5 _ _ V4 ltac:(lia))
      | exact (S5 _ _ V5 ltac:(lia))].
  - unfold mbyte, mrestrict in *. rewrite (M5 x Hx Ds Dob). exact H4. }
assert (KEPTs' : forall x, ~ inFP FS_PSTAT_FP x ->
  ((exists p nn, In (p, nn) (ablocks B ly3 S3) /\ p <= x < p + req_size nn) \/
   (exists cid pos, In (cid, pos) (frames S3) /\
      frame_addr ly3 cid pos <= x < frame_addr ly3 cid pos + fs_frame_bytes cid)) ->
  mrestrict (w_H W4) mem4 (Z_to_bv 64 x) = mrestrict (w_H W3) mem3 (Z_to_bv 64 x)).
{ intros x Hf Hx. rewrite (KEPTs x Hf Hx). apply (fsw_mrestrict_belowZ (w_H W3) mem3 memC3 x SB3).
  destruct Hx as [(p & nn & Hin & Hpx) | (cid & pos & Hin & Hfx)].
  - destruct (fsw_ablock_low B ly3 S3 W3 _ _ p nn HAR3 Hin) as (L1 & L2 & _). lia.
  - destruct (al_sep tfibsegs B LAWS ly3 S3 W3 _ _ HAR3) as [_ HF]. rewrite Forall_forall in HF.
    destruct (HF (cid, pos) Hin) as (F1 & F2). cbn [fst snd] in F1, F2. lia. }
assert (Hfrs41 : frames S4 = frames S1) by (rewrite Hfrs4, Hfrs1; reflexivity).
pose proof HJs as (_ & Hly4 & _).
destruct (al_layout tfibsegs B LAWS ly3 S3 W3 (unpoison Ug memC3) (wvb md3 mat3) ly4 HAR3c Hly4) as (_ & HFA4 & _).
assert (HFA41 : forall cid pos, frame_addr ly4 cid pos = frame_addr ly1 cid pos)
  by (intros cid pos; rewrite (HFA4 cid pos); exact (HFA3 cid pos)).
assert (HTo2 : rtree tfibsegs B ly1 S1 W1 memC2 o (PjTree.JObj ms) D)
  by exact (rnode_below B ly1 S1 W1 (unpoison U mem1) md1 mem1 memC2 D o (PjTree.JObj ms) D HAR1 SB2 ltac:(lia) Lo2 HTo1).
assert (HTw2 : rtree tfibsegs B ly1 S1 W1 memC2 w tv Dw)
  by exact (rnode_below B ly1 S1 W1 (unpoison U mem1) md1 mem1 memC2 Dw w tv Dw HAR1 SB2 ltac:(lia) Lw2 HTw1).
destruct (pSf_post B ly1 ly3 ly4 S1 S3 S4 W1 W3 W4 memC2 mem3 mem4 m5 m6 m7 (unpoison U memC2)
  (unpoison (Ug ++ [(a - HEAD, HEAD)]) mem4) (wvb md1 mat2) md4
  o k w num str kids keys n cap k' y' cap' a ms tv D Dw Dold Dnew U Ug kname
  HTo2 HPo2 HHo2 Hcap HINC HTw2 HPw2 HDw Hfootw Hapart HKk1 Hfootk HKEY HAR2
  HGR HPERM HHDR HSLOT3 HBLK HMVK HMVY KEPTg Hfrs3 HFA3
  HAB4 HRB4 HZB4 KEPTs' Hfrs41 HFA41 HAR4 HPo4 HPw4 HK4
  V1 V2 V3 V4 V5 G5 M5 C6 M6 Z7 M7') as (Dr & Do & PD & PDo & HTF & HZF & HPoF & HPwF & HKF).
(* ---- fuzz/alloc.c's statics: only fuzz_strdup touched them after grow ---- *)
assert (HGF : forall lv pk cn fl, fs_glob tfibsegs W4 mem4 lv pk cn fl -> fs_glob tfibsegs W4 memF lv pk cn fl).
{ intros lv pk cn fl HG0. apply (fs_glob_below W4 m7 memF _ _ _ _ SBF). apply (pS_glob_eq W4 mem4 m7 _ _ _ _ HG0).
  intros x Hx. destruct (pS_pstat_range x Hx) as (Hx1 & Hx2).
  assert (Hxc : 0 <= x < alloc_ceiling) by (unfold FS_IMG_END in Hx2; lia).
  assert (Nw : ~ (w <= x < w + 56))
    by (pose proof (fsw_pobj_off_img B ly4 S4 W4 _ _ mem4 w HAR4 HPw4); unfold FS_IMG_END in *; lia).
  assert (No : ~ (o + 24 <= x < o + 56))
    by (pose proof (fsw_pobj_off_img B ly4 S4 W4 _ _ mem4 o HAR4 HPo4); unfold FS_IMG_END in *; lia).
  assert (Ns : ~ (y' + 8 * n <= x < y' + 8 * n + 8)).
  { destruct (fsw_ablock_off_img B ly4 S4 W4 _ _ _ _ HAR4 HinY4) as [L | L]; try (rewrite Hrq in L by lia);
      unfold FS_IMG_END, HEAD in *; lia. }
  assert (Nd : ~ (k' + 56 * n <= x < k' + 56 * n + 56)).
  { destruct (fsw_ablock_off_img B ly4 S4 W4 _ _ _ _ HAR4 HinK4) as [L | L]; try (rewrite Hrq in L by lia);
      unfold FS_IMG_END, HEAD in *; lia. }
  transitivity (mbyte tfibsegs (mrestrict (w_H W4) m6) x).
  { apply (YCbq.mbyte_of_aview tfibsegs (w_H W4) (w_H W4) m6 m7 x). exact (M7' x Hxc Nw). }
  transitivity (mbyte tfibsegs (mrestrict (w_H W4) m5) x).
  { apply (YCbq.mbyte_of_aview tfibsegs (w_H W4) (w_H W4) m5 m6 x). exact (M6 x Hxc Nd). }
  unfold mbyte, mrestrict. rewrite (M5 x Hxc Ns No). reflexivity. }
destruct (fsw_pobj_low B ly4 S4 W4 _ _ mem4 o HAR4 HPo4) as (Lo5 & Lo6).
destruct (fsw_pobj_low B ly4 S4 W4 _ _ mem4 w HAR4 HPw4) as (Lw5 & Lw6).
(* ---- pj_set_spec's post ---- *)
exists k', y', cap', Dold, Dnew, Dr, Do, Ug, a.
split; [exact HGR|]. split; [exact PD|]. split; [exact PDo|].
exists ly4, S4, regsF, memF, mdF. split; [exact Ec|].
split; [rewrite (pSn_ev_split n cap _ Hcap0); unfold EV_fuzz_malloc; exact HJf|].
split; [exact OKf|]. split; [exact POf|]. split; [exact HPf|].
split; [exact RF|]. split; [exact Ha4096|].
split.
{ assert (Erh : rd_hblocks (Dnew ++ [(a, Z.of_nat (length kname) + 1)]) =
    rd_hblocks Dnew ++ [(a - HEAD, Z.of_nat (length kname) + 1 + HEAD)]) by (unfold rd_hblocks; rewrite map_app; reflexivity).
  rewrite Erh, HAB4, <- Hbl1, <- !app_assoc.
  apply (Permutation_trans (l' := ablocks B ly3 S3 ++ (rd_hblocks Dold ++ [(a - HEAD, Z.of_nat (length kname) + 1 + HEAD)]))).
  { apply Permutation_app_head. apply Permutation_app_comm. }
  rewrite !app_assoc. apply Permutation_app_tail. exact HPERM. }
split; [exact (rnode_below B ly4 S4 W4 _ _ m7 memF Do o _ Do HAR4 SBF ltac:(lia) Lo6 HTF)|].
split; [exact (pS_zero_below W4 m7 memF w SBF ltac:(lia) Lw6 HZF)|].
split; [exact (pobj_below B ly4 S4 W4 _ _ m7 memF o HAR4 SBF HPoF)|].
split; [exact (pobj_below B ly4 S4 W4 _ _ m7 memF w HAR4 SBF HPwF)|].
split; [exact (cstr_ok_below W4 m7 memF k kname SBF HKF)|].
exists (Z.max peak3 (live + PjGrammar.held (grow_tr 6 n cap) + (Z.of_nat (length kname) + 1))).
split; [lia|].
rewrite (pSn_held_split n cap _ Hklen0), (pSn_len_split n cap _).
replace (live + (PjGrammar.held (grow_tr 6 n cap) + (Z.of_nat (length kname) + 1)))
  with (live + PjGrammar.held (grow_tr 6 n cap) + (Z.of_nat (length kname) + 1)) by lia.
replace (cnt + (Z.of_nat (length (grow_tr 6 n cap)) + 1)) with (cnt + Z.of_nat (length (grow_tr 6 n cap)) + 1) by lia.
exact (HGF _ _ _ _ HG4).
Qed.

End MAIN.

(* ---- grow discharged by S0's FSW_grow_holds.grow_holds (a Theorem Labs lane's proof, in S0 since 30057674945) ---- *)
Section CL. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Theorem pj_set_holds_s0 : forall B, FsShadowSyms B -> fs_img_facts tfibsegs B -> pj_get_spec tfibsegs B ->
  fuzz_realloc_spec tfibsegs B -> fuzz_strdup_spec tfibsegs B ->
  FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy -> FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset ->
  pj_set_spec tfibsegs B.
Proof.
intros B HSS IMG GET REALLOC SD RT_memcpy RT_memset.
exact (@pj_set_holds fx rc SK B HSS IMG GET (@FSW_grow_holds.grow_holds fx rc SK B HSS REALLOC) SD RT_memcpy RT_memset).
Qed.
End CL.
