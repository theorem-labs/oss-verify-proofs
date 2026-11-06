(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan pin 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4),
   ex_value PIECE 5 (ev_number):
   WalkS8a's ev_number_spec (S8aIface.v:331) PROVED, at image A's instance (L := A_prog_listing, PA := PI_prog_A), from
   the seven lane lemmas (S8aNumA/B/C/D/E/FT.v, the walk sub-pieces) and S8aNumM.v (ev_mid preservation), composed by
   S8aNumWalk.v's ev_number_of_pieces. This is the lemma WalkS8a's S8aCompose.v plugs in for piece 5.
   The instance is fixed (not a Context PAImg) because the strtod ROW is image A's: lib/A/Prog/strtod_row.v
   strtod_row_A (h-verbs-1's A' row; its image constants are strtod_c.v blob 4e725dbd9c0c's) is stated over rsegs and
   strtod's entry STRTOD, so it is cited here verbatim at PI_prog_A (pa_segs = rsegs, pa_sigma AS_strtod = STRTOD).
   Derived here, no longer hypotheses: the strtod call text (STR, by strtod_row_A), ex_value's entry (A_entry_ex_value,
   by computation) and errno-in-image (strtod_row.v strtod_cells_A at as_errno B = STRTOD_ERRNO).
   Section hypotheses (each discharged at the concrete instance, or a named row / kit law):
     LAWS   the allocator laws AR_laws_x at the instance's head length cf_head (the instance)
     HIMG   ev_img_ok = 272 <= pi_frame F_ex_value (prh_img_A, by reflexivity)
     HHEAD  8 <= cf_head (preset's CfParams: 16)
     HPST   the program-written statics prh_pst (#102: alloc.c's six with g_most, and g_own_ran_out) lie in the
            image, away from errno
     Htp Herrno Hown  the three facts about B that strtod_row_A asks (strtod's tp and errno are B's, errno is not
            runtime-owned), as lib/A/VrdNum.v and lib/B/Prog/ExvB_Stmt.v carry them
     (no memnorm hypothesis: memnorm is a STATE fact, ev_pre's and ev_mid's last conjunct (S8aIface.v), carried by
            the lanes through YSRrMemnorm.v's twins and the call texts' keeps; the refuted law HMEMNORM is deleted)
     HOFFB HOFFF  strtod_site_x's image clauses (YStrtodRowX.v:348-349): a live block lies off [IMG_LO, IMG_TOP), a
            live fake frame lies above IMG_TOP; AR_laws_x (YCbqG.v:149-166) has no such law
     HGOTC  strtod's GOT guard word is one of B's const cells (the image-A binding, A/AE22.v canary_cell_in:
            A_GOT_CANARY = STRTOD_GOT_GUARD, V_GOT_CANARY = STRTOD_GUARD); its rom bytes are derived (strtod_got_A)
     CPY CMP BCMP the __asan_memcpy / __wrap_strcmp / __wrap_bcmp call texts in their memnorm-keeping forms
            (YGcallMxmn.v: aintrin_realizes_xm, astrcmp_realizes_xrom over the relro band, abcmp_realizes_xm)
     HBLK32 HAMEM8  lane E's two remaining instance facts (see their comment below). The old HROM (rom bytes not owned /
            errno / statics: the pal_rom_ok form, FALSE at the real image per h-verbs-1 16:18Z) is deleted: lane E
            derives the strcmp text's arodata_okP from fpre through the journal and the ledger
   Numerals: 7364 (DERIVED: ex_value's slot 1841 * 4, PAImg_prog.v A_entry_ex_value); 8, 4 (LENGTH: a GOT cell, errno's
   width); 2 ^ 32 (LENGTH: strcmp's int bound). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP FCiface YGcallMx YGcallMxmn YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut S8aNumWalk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aNumA S8aNumB S8aNumC S8aNumD S8aNumE S8aNumFT S8aNumM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Local Open Scope Z_scope.

(* the scan's byte set is inside musl's: PjGrammar.numch -> FmtFp_facts3.is_numch (both pure byte tests; the form of
   lib/A/VrdNum.v vrd_numch_is, restated, not Required) *)
Lemma evn_numch_is : forall c, PjGrammar.numch c = true -> FmtFp_facts3.is_numch c = true.
Proof.
  intros c H. unfold PjGrammar.numch, PjGrammar.digit in H. unfold FmtFp_facts3.is_numch.
  destruct (48 <=? c), (c <=? 57), (c =? 46), (c =? 101), (c =? 69), (c =? 43), (c =? 45); cbn in *; congruence.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Local Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HIMG : ev_img_ok.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis HPST : forall z, Exists (in_zr z) prh_pst -> in_img SEGS z /\ ~ (as_errno B <= z < as_errno B + 4).
(* the facts about B that strtod_row_A (lib/A/Prog/strtod_row.v:48-56) asks *)
Hypothesis Htp : as_tp B = STRTOD_TP.
Hypothesis Herrno : as_errno B = STRTOD_ERRNO.
Hypothesis Hown : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
(* strtod_site_x's image clauses (YStrtodRowX.v:348-349) at image A's constants: AR_laws_x has no law that places a
   live block or fake frame off the image band (at AR: YC1fP.v:334 blk_off_imgPI, from ALedger's pa_img_cover) *)
Hypothesis HOFFB : ev_blk_offimg B ARx strtod_img_A.
Hypothesis HOFFF : ev_frm_offimg ARx strtod_img_A.
(* strtod_site_x's GOT clause (ev_got_ok, the SEG_N form): the guard word is one of B's const cells, so AR_laws_x
   field 16 alx_const_cells keeps it in every ARx state; its eight image bytes hold the guard cell's address by
   strtod_row.v strtod_got_A (derived below). MARKED image-A binding of B, discharged at the binding by A/AE22.v
   canary_cell_in. (The old HGOT, "the GOT cells are not runtime-owned statics", is deleted: PValueB's audit found it
   false at image B.) *)
Hypothesis HGOTC : forall ly, In (z8 (ANum STRTOD_GOT_GUARD) STRTOD_GUARD) (as_const B ly).
Hypothesis CPY : forall fx1, aintrin_realizes_xm (fx := fx1) SEGS B ARx OCpy (pa_sigma AS___asan_memcpy).
Hypothesis CMP : forall fx1, astrcmp_realizes_xrom (fx := fx1) SEGS B ARx pa_relro_lo pa_relro_hi (pa_sigma AS___wrap_strcmp).
Hypothesis BCMP : forall fx1, abcmp_realizes_xm (fx := fx1) SEGS B ARx (pa_sigma AS___wrap_bcmp).
(* lane E's open facts (S8aNumE.v's CUTFIX hypotheses), each an instance fact with a named source:
     HBLK32 a block is below 2 ^ 32 bytes -> ARcf's AR_blocks_law_cf (n < cf_malloc_max = 2^29 - 2^20)
     HAMEM8 MARKED (the shared text, lib/B/Prog/ExvB_Stmt.v eh_blk_amem8, owner h-mani-a8 / c-omx-alloc): a live
            block lies in the runtime's 8-byte-margin application range, as YGcallMx's strcmp row asks
            (YGcallMx.v:77-78, :160); alx_blocks gives only in_app (YG0f.v:277) *)
Hypothesis HBLK32 : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 32.
(* HAMEM8: PROVED at the allocator instance: h-mani-a8's YGcfBlockRange.v:46 block_amem_range8_cf
   (origin/cold/h-mani-a8-preset-alloc 6c9f248bed97, from ARcf alone; k := n - 1 or the k-form at :59), discharged where
   ARx := ARcf; it is a hypothesis here only because this file is generic over ARx *)
Hypothesis HAMEM8 : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  YGcallMx.amem_range8 p (req_size n).

Lemma ev_number : ev_number_spec B ARx SK.
Proof.
  (* ex_value's entry at the instance (PAImg_prog.v A_entry_ex_value: slot 1841) *)
  assert (Hent : pa_sigma AS_ex_value = pa_val A_TEXT + 7364) by (vm_compute; reflexivity).
  (* errno is an image byte: strtod_row.v's cells at as_errno B = STRTOD_ERRNO *)
  assert (HERR : forall a0, as_errno B <= a0 < as_errno B + 4 -> in_img SEGS a0).
  { intros a0 Ha. rewrite Herrno in Ha.
    exact (YStrtodRowX.srx_cell_img rsegs a0
      (YStrtodRowX.srx_cells_b_sound rsegs STRTOD_ERRNO 4 a0 (proj2 (proj2 strtod_cells_A)) Ha)). }
  assert (MK : forall a, ev_mid_keep_stmt B ARx SK a) by (eapply S8aNumM.ev_mid_keep; eassumption).
  assert (MC : forall a, ev_mid_cur_stmt B ARx SK a) by (eapply S8aNumM.ev_mid_cur; eassumption).
  assert (PA_ : ev_A_stmt B ARx SK) by (eapply S8aNumA.ev_A; eassumption).
  assert (PB : ev_B_stmt B ARx SK) by (eapply S8aNumB.ev_B; eassumption).
  assert (PC : ev_C_stmt B ARx SK) by (eapply S8aNumC.ev_C_holds; eassumption).
  assert (PD : ev_D_stmt B ARx SK) by (eapply S8aNumD.ev_D; eassumption).
  assert (PF : ev_F_stmt B ARx SK) by (eapply S8aNumFT.ev_F; eassumption).
  assert (PT : ev_T_stmt B ARx SK) by (eapply S8aNumFT.ev_T; eassumption).
  assert (PE : ev_E_stmt B ARx SK) by (eapply S8aNumE.ev_E; eassumption).
  (* the caller facts of the strtod row at image A *)
  assert (SITE : ev_strtod_site B ARx strtod_img_A).
  { split; [exact HOFFB|]. split; [exact HOFFF|].
    split; [exact strtod_got_A | exact HGOTC]. }
  refine (ev_number_of_pieces B ARx SK PA_ PB PC PD PE PF PT HERR strtod_img_A _ SITE CPY CMP BCMP HIMG).
  (* the strtod call text: THE ROW, strtod_row_A, cited verbatim at strtod's entry STRTOD *)
  intros fx1.
  change (pa_sigma AS_strtod) with STRTOD.
  apply (strtod_row_A (fx := fx1) (HL := cf_head) B ARx LAWS Htp Herrno Hown STK_RT_STRTOD).
  - unfold STK_RT_STRTOD, ESTACK, STRTOD_K. lia.
  - intros txt [HF HL]. split; [exact (Forall_impl _ evn_numch_is HF) | exact HL].
  - intros txt bits c _ H. exact H.
Qed.
End c.
