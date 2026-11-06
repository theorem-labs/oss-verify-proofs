(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): CA_Top, the
   composition of the re-walk of check_no_overread (cno, entry A_prog_slot AS_check_no_overread = slot 201) into the
   kit text tcheck_no_overread_specX (lib/A/PRH_FnCheck.v), at the walks' instance (ARx := ARcfx = ARcf /\
   xs_placed_cf, RL := prh_room_live_a8, PL := PL_cno_A, cp := CfParams_preset), with the memory invariant P
   instantiated ONCE at the memnorm instance cn_mn D (Cno102A_Base.v cn_mn_laws / cn_mn_call / cn_mn_mn).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma; the composition of the segments).
   THE RE-HIDING MOVE (the free and realloc rows in their re-hiding form): every stretch from the first parse_noting on
   runs across a free, so it concludes SRr' SEGS RZ_cf (the walk's world relation wle' SEGS RZ_cf: the hidden set may
   grow only inside the re-hide zone RZ_cf), and so does the text: tcheck_no_overread_specX concludes SRr' segs RZ_cf
   with its post fpostFbm stated in place at wle' segs RZ_cf. CA0_4 makes no free: it stays at SRr and is lifted by
   YA0nH.SRr_SRr'. The chain is joined with YSRrG.SRr'_bind.
   INPUTS (by path; each blob in this tree): lib/A/PRH_FnCheck.v (the text), lib/A/Prog/Cno102A_Base.v (cn_pre / cn_Q /
   cn_post = the text's premises and post, verbatim; no DW; the wild budget wbudget [] (prh_wk F_check_no_overread);
   the hull budget as cn_pre's last conjunct), Cno102A_E.v / Cno102A_EC.v, Cno102A_R.v, Cno102A_F.v, Cno102A_FA.v,
   Cno102A_FT.v, lib/A/PRH_Img.v.
   THE STRETCHES, every one a LEMMA:
     CA0_4   Cno102A_EC.cn_E: entry -> CN_INIT \/ CN_INIT3, under cn_pre and cn_fp (SRr);
     CA5_9   Cno102A_R.cn_R: CN_INIT \/ CN_INIT3 -> CN_FREE, its exit cn_ex_freeR at wle' SEGS RZ_cf (SRr');
     CA10    Cno102A_FT.cn_seg_free: CN_FREE -> CN_END, from cn_at_freeR at wle' SEGS RZ_cf (SRr'; NO state premise:
             the free order ties come from the readings through the base's cn_fo);
     CA11    Cno102A_FT.cn_seg_end: CN_END -> the function exit cn_ex_ret (SRr').
   THE CITED LEMMAS' NAMED ARGUMENTS, deduplicated (Section hypotheses here, each spelled as in its file):
     image facts: IMG (cn_img B; cn_E, cn_R, FT), PAL (PALib B; cn_E, FT), ENV (api_env SEGS B; FT), SYMS (asyms_ok B;
       cn_E), SM3 (pc_stack_malloc (as_code B) CN_CID = SIGMA AS___asan_stack_malloc_3; cn_E), IMGSH (the image shadow
       mapped in every ARcf state; cn_E);
     runtime rows: MEMSET (__asan_memset; cn_R's MEMSET and cn_E's ASET, one statement), ACPY (__asan_memcpy; cn_E),
       AMALLOC (YGcfMallocComposeKeep.amalloc_realizes_cf_keep, the malloc row with the memnorm keep at its end
       configuration, the form cn_E's copy segments cite), ASM3 (astack_malloc_realizes_xm at class CN_CID; cn_E),
       AFREE (YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, the free row's re-hiding form with the memnorm keep at
       its end configuration; FT), SS5M (__asan_set_shadow_f5; FT);
     the kit's callee texts: HRO, HSAME, HPN (cn_R), HPJFREE (FT).
   DISCHARGED HERE: HW (prh_head_wide; cn_E, cn_R, FT) by CfParamsPreset.preset_head_wide and HH (CFHEAD-16,
     PRH_Base.prh_head16; FT) by Cno102A_FA.cn_head16_preset, now that cp is the preset's; cn_R's LAWS by
     AR_laws_x_xs (AR_laws_ok_cf); cn_E's cn_fp by YGcallScf.stack_malloc_progress_any under the capacity rule.
     At the A' instance (Cno102A_TopA.v): IMG, PAL, ENV, SYMS, SM3, IMGSH, MEMSET, ACPY, ASM3, SS5M.
   THE HULL: the text's hull premise (PresetHullBudget.hull_budget S (ck_cno_evs ..)) is cn_pre's last conjunct
     (Cno102A_Base.cn_pre_hull); the stretches thread it through their cuts and pay the callee texts
     (tparse_noting_specX in CA5_9, tpj_free_specX and the frees in CA10) from it. This file makes no call and pays
     nothing; it passes the premise into cn_pre.
   THE PROOF: ci_fpos := the position the frame-area model's __asan_stack_malloc_3 returns (stack_malloc_progress_any
     at count_cid 3 (frames S) < fs_frames 3, from the text's `Z.of_nat (length (frames S)) <= ck_FRAMES_CAP -
     FR_check_no_overread`, read BY NAME: Cno102A_Base.cn_pre_frames); the cuts chained backward by SRr'_bind
     (CN_END <- CN_FREE <- CN_INIT / CN_INIT3 <- entry); P := cn_mn D once; cn_post from cn_ex_ret and P (the same
     body cn_Q at the same budget WS, fpostFbm = fpostFb + the memnorm keep).
   Numerals: 245 (WORD: the shadow byte 0xf5, SS5M's spelling); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
(* the re-hiding move: SRr' / wle' / SRr_SRr' (YA0nH), SRr'_bind / SRr'_mono (YSRrG), the zone RZ_cf (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
(* the malloc and free rows' memnorm-keeping twins (YGcfMallocComposeKeep; the free one in its re-hiding form) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Cno102A_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Cno102A_E Cno102A_EC Cno102A_R Cno102A_F
  Cno102A_FA Cno102A_FT.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the capacity rule: the text's frame budget leaves a class-3 frame free ---- *)
Lemma cn_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.
Lemma cn_cap : forall S, Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_no_overread ->
  count_cid CN_CID (frames S) < fs_frames CN_CID.
Proof.
intros S H. pose proof (cn_count_le CN_CID (frames S)) as Hc.
assert (E : ck_FRAMES_CAP - FR_check_no_overread < fs_frames CN_CID) by (vm_compute; reflexivity).
lia.
Qed.

(* open a cut's exit: hnf to its existentials, each one, then the configuration equation and the cut *)
Ltac ck_open HEX := hnf in HEX;
  repeat match type of HEX with @ex _ _ => let x := fresh "x" in destruct HEX as [x HEX] end;
  destruct HEX as [-> HAT].

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
(* the allocator parameters: the preset harness's, as the cited stretches bind them *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
(* the walks' instance, bound ONCE here (Cno102A_F.v's, Caw102A_Base.v's) *)
#[local] Existing Instance PL_cno_A.
#[local] Existing Instance prh_room_live_a8.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation CP := CfParamsPreset.CfParams_preset.
(* the walk's world relation from the first parse_noting on: the hidden set grows only inside the re-hide zone *)
#[local] Notation RCF := (wle' SEGS RZ_cf).
Variable B : asyms.
(* THE CONTEXT OF THE CALL, bound ONCE for the whole file: every premise below that mentions a context is at THIS
   CTX0, never at every CTX0, so a caller cites the theorem with the texts it has at its own context. After `End top`
   the theorem reads `forall .. B CTX0, <premises at CTX0> -> tcheck_no_overread_specX .. CTX0`. *)
Variable CTX0 : list (list Z).
(* the walk's allocator relation (S1KitAlloc's ARxs, YGcallcf.v) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

(* ---- the entry configuration (the text's) ---- *)
Definition cn_cfg0 (D : cn_in) : config :=
  cfg_at SEGS (SIGMA AS_check_no_overread) (ci_regs D) (ci_mem D) (ci_md D).
(* ================================ THE SECTION HYPOTHESES ================================ *)
(* the cited lemmas' named arguments, deduplicated; the A' instance file discharges the image facts and rows *)
Hypothesis IMG : cn_img B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis SYMS : asyms_ok B.
Hypothesis SM3 : pc_stack_malloc (as_code B) CN_CID = SIGMA AS___asan_stack_malloc_3.
Hypothesis IMGSH : forall ly S Hp W mem md a, ARcf SEGS B ly S Hp W mem md -> pa_lo <= a < pa_hi ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the malloc row with the memnorm keep at its end configuration (YGcfMallocComposeKeep.v) *)
Hypothesis AMALLOC : forall fz : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS B.
Hypothesis ASM3 : astack_malloc_realizes_xm (fx := fx) SEGS B ARcfx CN_CID.
Hypothesis ACPY : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OCpy (SIGMA AS___asan_memcpy).
Hypothesis MEMSET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OSet (SIGMA AS___asan_memset).
(* the free row in its re-hiding form (its realization over the zone RZ_cf) with the memnorm keep at its end
   configuration (YGcfMallocComposeKeep.v) *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis SS5M : forall fz : YK11.FPState,
  @YGcallMxmn.aset_shadow_realizes_xm fz SEGS B ARcfx (SIGMA AS___asan_set_shadow_f5) 245.
Hypothesis ENV : api_env SEGS B.
(* the kit's callee texts *)
Hypothesis HRO : forall fz : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fz rc CP prh_img_A prh_room_live_a8 A_prog_listing PA B ARcfx SK.
Hypothesis HSAME : forall fz : YK11.FPState,
  @tsame_specX fz rc CP prh_img_A prh_room_live_a8 A_prog_listing PA B ARcfx SK DOC_D.
(* ONE CTX0, the walk's own: the callee texts are premises AT THE CTX0 this walk uses, never at every CTX0, so a caller
   that has parse_noting / pj_free at its own context can cite the theorem *)
Hypothesis HPN : forall fz : YK11.FPState,
  @tparse_noting_specX fz rc ci CP prh_img_A prh_room_live_a8 A_prog_listing PA B ARcfx SK CTX0.
Hypothesis HPJFREE : forall fz : YK11.FPState,
  tpj_free_specX (fx := fz) (PI := prh_img_A) (RL := prh_room_live_a8) B ARcfx SK CTX0 DOC_D.

(* ================================ THE STRETCHES, every one a LEMMA ================================ *)
(* CA0_4: Cno102A_EC.cn_E; its cn_fp and entry configuration are Cno102A_E.v's own *)
Lemma CA0_4 :
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D, cn_pre (fx := fx) B ARcfx CTX0 D -> Cno102A_E.cn_fp D -> P (ci_mem D) ->
  SRr SEGS (ci_W D) (cn_cfg0 D)
    (fun W' c' => (cn_ex_init (fx := fx) B ARcfx D W' c' \/ cn_ex_init3 (fx := fx) B ARcfx D W' c') /\
                  P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D HPRE HFP HP0.
assert (HE : Cno102A_E.cn_seg_E (fx := fx) (cp := CP) (RL := prh_room_live_a8) (SK := SK) B ARcfx CTX0).
{ eapply Cno102A_EC.cn_E;
    first [exact IMG | exact PAL | exact SYMS | exact SM3 | exact CfParamsPreset.preset_head_wide | exact IMGSH
          | exact AMALLOC | exact ASM3 | exact ACPY | exact MEMSET]. }
unfold Cno102A_E.cn_seg_E in HE.
change (cn_cfg0 D) with (Cno102A_E.cn_entry_cfg (fx := fx) D).
exact (HE P PLAW PCALL D HPRE HFP HP0).
Qed.
(* CA5_9: Cno102A_R.cn_R, its AR_laws_x from AR_laws_ok_cf; its exit is CN_FREE at the walk's relation *)
Lemma CA5_9 :
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D W c, cn_pre (fx := fx) B ARcfx CTX0 D ->
  (cn_ex_init (fx := fx) B ARcfx D W c \/ cn_ex_init3 (fx := fx) B ARcfx D W c) -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ_cf W c (fun W' c' => cn_ex_freeR (fx := fx) B ARcfx RCF D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL PMN D W c HPRE HX HPc.
exact (Cno102A_R.cn_R (fx := fx) (SK := SK) B ARcfx CTX0 (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B))
  IMG CfParamsPreset.preset_head_wide MEMSET HRO HSAME HPN P PLAW PCALL PMN D W c HPRE HX HPc).
Qed.
(* CA10 / CA11: Cno102A_FT.cn_seg_free / cn_seg_end at the preset parameters; HH = CFHEAD-16 there *)
Lemma CA10 : Cno102A_F.cn_seg_freeP (fx := fx) (SK := SK) B CTX0.
Proof.
eapply Cno102A_FT.cn_seg_free;
  first [exact IMG | exact HPJFREE | exact AFREE | exact PAL | exact CfParamsPreset.preset_head_wide
        | exact SS5M | exact ENV | exact Cno102A_FA.cn_head16_preset].
Qed.
Lemma CA11 : Cno102A_F.cn_seg_endP (fx := fx) (SK := SK) B CTX0.
Proof.
eapply Cno102A_FT.cn_seg_end;
  first [exact IMG | exact HPJFREE | exact AFREE | exact PAL | exact CfParamsPreset.preset_head_wide
        | exact SS5M | exact ENV | exact Cno102A_FA.cn_head16_preset].
Qed.

(* ================================ THE CHAIN, generic in P ================================ *)
Section chain.
(* CTX0 is Section top's, bound once above, so every callee-text premise is at THIS CTX0 *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Hypothesis PCALL : srr_inv_call SEGS P.
Hypothesis PMN : srr_inv_mn SEGS P.
#[local] Notation CNPRE D := (cn_pre (fx := fx) B ARcfx CTX0 D).
#[local] Notation FIN D := (fun W' c' => cn_ex_ret (fx := fx) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c'))).

(* CA11 *)
Lemma ck_end : forall D W c, CNPRE D -> Cno102A_F.cn_ex_end (fx := fx) B D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ_cf W c (FIN D).
Proof.
intros D W c HPRE HEX HPc. ck_open HEX.
eapply (CA11 P PLAW PCALL); [exact HPRE | exact HAT | exact HPc].
Qed.
(* CA10, then CA11: joined at CN_END *)
Lemma ck_free : forall D W c, CNPRE D -> cn_ex_freeR (fx := fx) B ARcfx RCF D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ_cf W c (FIN D).
Proof.
intros D W c HPRE HEX HPc. ck_open HEX.
eapply (SRr'_bind SEGS RZ_cf); [eapply (CA10 P PLAW PCALL); [exact HPRE | exact HAT | exact HPc]|].
intros W1 c1 _ [HX HP1]. exact (ck_end D W1 c1 HPRE HX HP1).
Qed.
(* CA5-CA9, then CA10-CA11: joined at CN_FREE *)
Lemma ck_R : forall D W c, CNPRE D ->
  (cn_ex_init (fx := fx) B ARcfx D W c \/ cn_ex_init3 (fx := fx) B ARcfx D W c) -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ_cf W c (FIN D).
Proof.
intros D W c HPRE HX HPc.
eapply (SRr'_bind SEGS RZ_cf); [exact (CA5_9 P PLAW PCALL PMN D W c HPRE HX HPc)|].
intros W1 c1 _ [HF HP1]. exact (ck_free D W1 c1 HPRE HF HP1).
Qed.
(* CA0-CA4 (lifted from SRr), then CA5-CA11: joined at CN_INIT / CN_INIT3 *)
Lemma ck_entry : forall D, CNPRE D -> Cno102A_E.cn_fp D -> P (ci_mem D) ->
  SRr' SEGS RZ_cf (ci_W D) (cn_cfg0 D) (FIN D).
Proof.
intros D HPRE HFP HP0.
eapply (SRr'_bind SEGS RZ_cf); [exact (SRr_SRr' SEGS RZ_cf _ _ _ (CA0_4 P PLAW PCALL D HPRE HFP HP0))|].
intros W1 c1 _ [HX HP1]. exact (ck_R D W1 c1 HPRE HX HP1).
Qed.
End chain.

(* ---- THE WALK of one record: P := cn_mn D, ONCE ---- *)
Lemma cn_walk_A : forall D : cn_in,
  cn_pre (fx := fx) B ARcfx CTX0 D -> Cno102A_E.cn_fp D ->
  SRr' SEGS RZ_cf (ci_W D) (cn_cfg0 D)
    (fun W' c' => cn_ex_ret (fx := fx) B ARcfx D W' c' /\ cn_mn D (ms_mem (cfg_ms c'))).
Proof.
intros D HPRE HFP.
exact (ck_entry (cn_mn D) (cn_mn_laws D) (cn_mn_call D) (cn_mn_mn (fx := fx) B ARcfx CTX0 D HPRE)
  D HPRE HFP (cn_mn_entry D)).
Qed.

(* ---- THE TEXT AT ONE RECORD: the text's premises (cn_pre, verbatim) give the text's post (cn_post, verbatim) at
   the text's entry configuration, at the walk's relation; ci_fpos is not read (the fake frame's position is the
   frame-area model's, chosen here) ---- *)
Theorem check_no_overread_walk_A : forall D : cn_in,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  SRr' SEGS RZ_cf (ci_W D) (cn_cfg0 D) (cn_post (fx := fx) B ARcfx D).
Proof.
intros [ly S Hp W regs mem md ch data x Lam peak cnt ran most fpos0] HPRE.
pose proof (cn_pre_frames (fx := fx) B ARcfx CTX0 _ HPRE) as HFR. cbn [ci_S] in HFR.
(* the fake frame's position: the capacity rule at the entry state *)
destruct (YGcallScf.stack_malloc_progress_any S CN_CID ltac:(unfold CN_CID; lia) (cn_cap S HFR))
  as (pos & S1 & HPATH).
pose (D := mkCnIn ly S Hp W regs mem md ch data x Lam peak cnt ran most pos).
assert (HPRE' : cn_pre (fx := fx) B ARcfx CTX0 D) by exact HPRE.
assert (HFP : Cno102A_E.cn_fp D) by exact (ex_intro _ S1 HPATH).
eapply (SRr'_mono SEGS RZ_cf); [exact (cn_walk_A D HPRE' HFP)|].
intros W' c' _ [HRET HMN].
unfold cn_ex_ret, fpostFb, YCbqGwild.apost_base_xbFR in HRET.
destruct HRET as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hfz & Hfk & HB & HJ & Har & HQ).
rewrite Hc in HMN.
unfold cn_post, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR, fQmn.
exists fx', ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HB|]. split; [exact HJ|].
split; [exact Har|]. split; [exact HQ | exact HMN].
Qed.

(* ================================ THE KIT TEXT ================================ *)
(* its 23 premises are cn_pre's 23 conjuncts in the text's order; the last is the hull budget *)
Theorem check_no_overread_holds_A :
  @tcheck_no_overread_specX fx rc ci CP prh_img_A prh_room_live_a8 A_prog_listing PA B ARcfx SK CTX0.
Proof using IMG PAL SYMS SM3 IMGSH AMALLOC ASM3 ACPY MEMSET AFREE SS5M ENV HRO HSAME HPN HPJFREE.
unfold tcheck_no_overread_specX.
intros ly S Hp W regs mem md ch data x Lam peak cnt ran most.
cbv zeta.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
pose (D := mkCnIn ly S Hp W regs mem md ch data x Lam peak cnt ran most 0).
assert (HPRE : cn_pre (fx := fx) B ARcfx CTX0 D).
{ exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21
    (conj H22 H23)))))))))))))))))))))). }
exact (check_no_overread_walk_A D HPRE).
Qed.

End top.
