(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 414 of its 496 lines of code are new or changed and 4971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B2.v, with its module names and addresses changed; 438 of its 521 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B3_p2.v, with its addresses and numbers changed; 314 of its 401 lines of code are new or changed and 434 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B3 of reac_segconf_parse_file's
   walk, its last piece: 0x88148 (after check B#2) -> DONE (0x89114, the empty text) or HEAD (0x881f8, the first
   line). The B3 segment lane of the image-B G3 walk owner, 2026-10-30. ADAPTED from the image-A G3 walk owner's image-A segment walk lib/A/Prog/pf_a2.v
   (commit 3f59c8d75ed4: seed, plain runs, region read-back, the exit cuts), re-derived on image B's
   code:
     0x88148 lbu a0,0(s11); sd s3,88(s1); srli a1,s3,3; sd a1,80(s1); 0x88158 bnez a0 -> 0x88160,
             else 0x8815c j DONE 0x89114 (t[0] = 0: the text is empty, s = [] since s has no NUL)
     0x88160 .. 0x881f4 li s8,0; sd zero,192(s1) (cur = NULL); the slots of PF_SL (~c, &seg[0].seen_gen,
             &c->overflow, .str.3 / .str.2, 0x2c80, F + 0x40 .. F + 0x450 and their `not`s); li s2,35; li s10,-1
   The exits: INV_DONE with cf = pf_start rcs lab (H_DONE at every FP state), or INV_HEAD (length s) with o = 0,
   ln = 0, d = [], cf = pf_start rcs lab, cur = None, nm = [] (H_HEAD (length s) at every FP state); the posts are
   PF_POST through pf_seg_B3_f.v's b3f_parse_fst / b3f_parse_done (r_parse_file is r_lines from pf_start). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B3_f pf_seg_B3_t pf_seg_B3_k pf_seg_B3_p1 pf_seg_B3_p2 pf_seg_B3_p3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a YO0c YI08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the value a chunk's symbolic word denotes *)
Lemma pb3_dv_off : forall E n x k y, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> y = x + k ->
  sv_denot E (SOff n k) = Z_to_bv 64 y.
Proof. intros E n x k y Hn Hx ->. exact (pb3_den_off E n x k Hn Hx). Qed.
Lemma pb3_dv_not : forall E n x k y, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
  y = pf_nt (x + k) -> sv_denot E (SAlu ALU_XOR (SOff n k) (SLit (-1))) = Z_to_bv 64 y.
Proof. intros E n x k y Hn Hx Hk ->. exact (pb3_den_not E n x k Hn Hx Hk). Qed.
Lemma pb3_dv_srl : forall E n x y, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> y = x / 8 ->
  sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = Z_to_bv 64 y.
Proof. intros E n x y Hn Hx ->. exact (pb3_den_srl3 E n x Hn Hx). Qed.
Lemma pb3_dv_lit : forall E z y, z mod 2 ^ 64 = y mod 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 y.
Proof.
intros E z y H. cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Lemma pb3_lit_eq : forall z y, z mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 z = w64 y.
Proof.
intros z y H. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
(* the first byte of a C string's encoding *)
Lemma pb3_t0_len : forall s : list Z, nth 0 (s ++ [0]) 0 <> 0 -> (0 < length s)%nat.
Proof. intros [|b s] H; [exfalso; apply H; reflexivity | cbn; lia]. Qed.
Lemma pb3_t0_nil : forall s : list Z, ~ In 0 s -> nth 0 (s ++ [0]) 0 = 0 -> s = [].
Proof. intros [|b s] Hn H; [reflexivity|]. cbn in H. subst b. exfalso. apply Hn. left. reflexivity. Qed.
(* a reader that agrees on the block c keeps the record *)
Lemma pb3_same_rconf_on : forall (rd rd' : reader) c cf,
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) -> sa_rconf rd c cf -> sa_rconf rd' c cf.
Proof.
intros rd rd' c cf HK (bs & Hb & Henc). exists bs. split; [|exact Henc].
pose proof Henc as (HL & _). intros i Hi. rewrite HK; [exact (Hb i Hi)|].
unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.

Ltac pb3_ar := unfold pf_nt, PF_O_CN, PF_O_BUF, PF_O_LOW, PF_O_L146, PF_O_KNOWN, PF_O_NTOK, seg_spec.RC_N,
  seg_spec.RS_SEEN_GEN, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE,
  in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia.
Ltac pb3_den := first
  [ apply pb3_dv_lit; reflexivity
  | eapply pb3_dv_srl; [eassumption | pb3_ar | first [reflexivity | pb3_ar]]
  | eapply pb3_dv_not; [eassumption | pb3_ar | pb3_ar | pb3_ar]
  | eapply pb3_dv_off; [eassumption | pb3_ar | pb3_ar] ].
Ltac pb3_regh HS EE RG :=
  lazymatch goal with |- getr (ms_regs ?ms) (Z_to_bv 5 ?k) = _ =>
    let Rk := fresh "Rk" in prreg HS (Z_to_bv 5 k) Rk; rewrite Rk; clear Rk end;
  first
  [ reflexivity
  | apply pb3_lit_eq; reflexivity
  | lazymatch goal with |- ew _ ?n = _ => let z := eval cbv in (Z.of_nat n) in rewrite (EE n (Z_to_bv 5 z) eq_refl) end;
    apply (pb3_rg _ _ _ _ RG); solve [unfold PB3_FI; pb3_in] ].


Ltac pb3_hr0 HS W HR0 :=
  lazymatch type of HS with
  | st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
  | st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
  end; cbn [ms_mem restrict] in HR0.
Ltac pb3_slot HR0 U9 :=
  eapply (pb3_word_of_region _ _ _ _ 9%nat _ _ _ _ _ _ _ _ _ HR0 U9); [solve [pb3_in] | pb3_den | pb3_ar].

(* ---------- the seed at 0x88148 ---------- *)
Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Section x. Context {fx : YK11.FPState}.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma pb3_post : forall v, PF_POST B v = PF_POSTr B v (fst (r_parse_file (p_rcs v) (p_s v) (p_lab v))).
Proof. intros v. unfold PF_POST, PF_POSTr. rewrite b3f_parse_snd. reflexivity. Qed.

Lemma pb3_seed3b : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 F c shc t t0,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 18) = w64 0x3000 -> getr rX (Z_to_bv 5 27) = w64 t ->
  0 <= s1 -> s1 + 0xd8 <= 2 ^ 64 -> 0 <= F -> F + 0x20 < 2 ^ 64 -> 0 <= c -> c + 0x40e0 < 2 ^ 64 ->
  0 <= shc < 2 ^ 64 -> 0 <= t -> t + 1 <= s1 -> 0 <= t0 < 256 ->
  rdword (rdW Wc memc) (s1 + 0x88) = Some F -> rdword (rdW Wc memc) (s1 + 0x98) = Some F ->
  rdword (rdW Wc memc) (s1 + 0xc8) = Some c -> rdword (rdW Wc memc) (s1 + 0x18) = Some shc ->
  rdword (rdW Wc memc) (s1 + 0x20) = Some (c + 0x40e0) -> rdword (rdW Wc memc) (s1 + 0x40) = Some (F + 0x20) ->
  rdword (rdW Wc memc) (s1 + 0x48) = Some (c + 0x4080) -> rdW Wc memc t = Some t0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 F; w64 c; w64 shc; w64 t0])) pb3_ss3b
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x310))) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 F c shc t t0 R9 R18 R27 Hs0 Hs1 HF0 HF1 Hc0 Hc1 Hsh Ht0 Ht1 Hb W88 W98 WC8 W18 W20 W40 W48 WT.
set (E := Eimg (Ereg rX [w64 F; w64 c; w64 shc; w64 t0])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = t) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 shc) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E35 : ew E 35 = w64 t0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 3)).
assert (U35 : bv_unsigned (ew E 35) = t0) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
assert (HSn : st_ok_pi SEGS VAL E pb3_ss3b0
  (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x310))) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, pb3_r3s1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; [..|apply Forall_nil].
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x88 8 (SOff 32 0) F).
        -- rewrite pb3_den_atom0, E32. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W88.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x98 8 (SOff 32 0) F).
        -- rewrite pb3_den_atom0, E32. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W98.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0xc8 8 (SOff 33 0) c).
        -- rewrite pb3_den_atom0, E33. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact WC8.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x18 8 (SOff 34 0) shc).
        -- rewrite pb3_den_atom0, E34. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W18.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x20 8 (SOff 33 0x40e0) (c + 0x40e0)).
        -- apply pb3_den_off; [exact E33 | lia].
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W20.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x40 8 (SOff 32 0x20) (F + 0x20)).
        -- apply pb3_den_off; [exact E32 | lia].
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W40.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x48 8 (SOff 33 0x4080) (c + 0x4080)).
        -- apply pb3_den_off; [exact E33 | lia].
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W48.
    + unfold region_ok, pb3_r3t. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) t 0 1 (SOff 35 0) t0).
      * rewrite pb3_den_atom0, E35. reflexivity.
      * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      * cbn. lia.
      * change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. apply pb3_val_mem_of_sa_val.
        intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, pb3_le_byte1 by lia. exact WT.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val pb3_r3s1 pb3_r3t]. rewrite U9, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U35, Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 18) 0x3000 HSn R18 eq_refl).
Qed.

(* the frame part and the objects at a later state of the segment *)
Lemma pb3_fi_of : forall v pos lyc Sc Wc memA rX' memc' mdc',
  frm0 fx -> pb3_FA B v pos lyc Sc Wc memA ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  pb3_kept v pos (rdW Wc memA) (rdW Wc memc') ->
  rdword (rdW Wc memc') (pf_s1 v + 0xc8) = Some (p_c v) ->
  pf_rg rX' (PB3_FI B v) ->
  pf_fi B v pos lyc Sc Wc rX' memc' mdc' /\ pf_obj B v lyc Sc (rdW Wc memc').
Proof.
intros v pos lyc Sc Wc memA rX' memc' mdc' HFR HFA HJ K WC8 HR.
destruct HFA as (HCX & G & Hin & EF & Hly & HSc & HPm & HOBJA & HSAV & HFL & HTF & Hfrs).
pose proof HJ as (HAR & _).
assert (HTD : sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE).
{ destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ &
    (fe & ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTD & _) & _)) & _). exact HTD. }
split.
- split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPm|].
  split; [exact (pb3_keep_saved v pos _ _ _ G K HSAV)|].
  split; [exact (pb3_keep_flag v pos _ _ G K HFL)|].
  split; [exact HFR|]. split; [exact HTF|].
  split; [apply Forall_cons; [exact WC8 | apply Forall_nil]|].
  exact HR.
- exact (pb3_keep_obj B v pos lyc Sc Wc memc' mdc' (rdW Wc memA) (rdW Wc memc') G HAR Hin EF HTD K HOBJA).
Qed.

(* ---------- the piece: 0x88148 -> DONE (empty text) or HEAD (the first line) ---------- *)
Lemma pb3_s3b : forall v pos lyc Sc Wc memA rX memc mdc,
  frm0 fx -> pb3_FA B v pos lyc Sc Wc memA -> pb3_MID2 B v pos lyc Sc Wc memA rX memc mdc ->
  (forall n, HA_HEAD B n) -> HA_DONE B ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x310)) rX memc mdc) (PF_POST B v).
Proof.
intros v pos lyc Sc Wc memA rX memc mdc HFR HFA HM HH HD.
pose proof HFA as (HCX & G & Hin & EF & Hly & HSc & HPm & HOBJA & HSAV & HFL & HTF & Hfrs).
pose proof HM as (HJ & K2 & HRC & HSL & HFSH & HCN & HRG).
pose proof HJ as (HAR & _).
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in S1.
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof HCX as (_ & _ & _ & Hc64 & _ & Ht64 & _).
assert (PRE : rc_refused (p_rcs v) + 2 ^ 17 < 2 ^ 32 /\ rc_overflow (p_rcs v) + 2 ^ 17 < 2 ^ 32 /\
  (length (p_s v) <= 65535)%nat /\ sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE).
{ destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ &
    (fe & ((_ & _ & _ & _ & _ & _ & Hrf & Hov & _ & _ & Hl65 & _ & _ & HTD & _) & _)) & _).
  exact (conj Hrf (conj Hov (conj Hl65 HTD))). }
destruct PRE as (Hrf & Hov & Hl65 & HTD).
assert (HOBJ : pf_obj B v lyc Sc (rdW Wc memc))
  by exact (pb3_keep_obj B v pos lyc Sc Wc memc mdc (rdW Wc memA) (rdW Wc memc) G HAR Hin EF HTD K2 HOBJA).
pose proof HOBJ as (O1 & O2 & O3 & O4 & O5 & _).
destruct (pb3_heap_out B v pos lyc Sc Wc memc mdc (p_t v) (pf_len v) (p_t v) G HAR Hin EF O3
  ltac:(unfold pf_len; lia)) as (T1 & T2 & T3).
pose proof O1 as ((Hz & Hn0) & _).
remember (nth 0 (p_s v ++ [0]) 0) as t0 eqn:Et0.
assert (WT : rdW Wc memc (p_t v) = Some t0).
{ pose proof (Hz 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H. rewrite Z.add_0_r, <- Et0 in H. exact H. }
destruct (aview_byte SEGS (w_H Wc) memc _ _ WT) as (_ & _ & _ & Ht0b).
assert (R : forall r x, In (r, x) (PB3_FI B v ++ [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000);
    (27, p_t v)]) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x Hr; exact (pb3_rg rX _ r x HRG Hr)).
assert (Hshc : 0 <= shadow_addr (p_c v + seg_spec.RC_GEN) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *.
  pose proof (Z.div_pos (p_c v + 16608) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (p_c v + 16608) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
pose proof (pb3_seed3b Wc rX memc (pf_s1 v) (pf_F v pos) (p_c v) (shadow_addr (p_c v + seg_spec.RC_GEN)) (p_t v) t0
  (R 9 _ ltac:(unfold PB3_FI; pb3_in)) (R 18 _ ltac:(unfold PB3_FI; pb3_in)) (R 27 _ ltac:(unfold PB3_FI; pb3_in))
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) Hshc
  ltac:(lia) ltac:(unfold pf_len in *; lia) Ht0b
  ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in) ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in)
  ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in) ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in)
  ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in) ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in)
  ltac:(apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in) WT) as HS.
set (E0 := Eimg (Ereg rX [w64 (pf_F v pos); w64 (p_c v); w64 (shadow_addr (p_c v + seg_spec.RC_GEN)); w64 t0])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr rX r)
  by (intros n r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = w64 (pf_F v pos)) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E0 33 = w64 (p_c v)) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E0 34 = w64 (shadow_addr (p_c v + seg_spec.RC_GEN)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E35 : ew E0 35 = w64 t0) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 3)).
assert (E277 : ew E0 277 = w64 (seg_litA_rc [SP; TAB; CR])) by exact (pb3_obj36 OBJ E0 HEI).
assert (E278 : ew E0 278 = w64 (seg_litA_rc F_long)) by exact (pb3_obj37 OBJ E0 HEI).
clearbody E0.
assert (E19 : ew E0 19 = w64 (p_c v + seg_spec.RC_N)) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); apply R; unfold PB3_FI; pb3_in).
assert (U9 : bv_unsigned (ew E0 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (R 9 _ ltac:(unfold PB3_FI; pb3_in)); unfold w64; apply unsigned_lit_small; lia).
assert (L36 : seg_litA_rc [SP; TAB; CR] = 0x21380) by (vm_compute; reflexivity).
assert (L37 : seg_litA_rc F_long = 0x213a0) by (vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
pb3_rewin HS 0%nat 0 0xd8 ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite U9; apply Hpres0; rewrite ESTK; lia).
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x310)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x310))).
(* 0x88148 .. 0x88158 *)
paj_run_sh RUNP HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc0 fr0 lyx own) end.
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (pf_s1 v - pf_sp0 v));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; rewrite ESTK; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG, HF.
pb3_clear_md.
assert (KMa : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v <= a < pf_s1 v + 0xd8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms)
    (fun a => pf_s1 v <= a < pf_s1 v + 0xd8) HFr); [| exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia |]).
  destruct Hin'. }
assert (MGa : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
assert (EFIN : forall rX' memc' mdc',
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v <= a < pf_s1 v + 0xd8) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  rdword (rdW Wc memc') (pf_s1 v + 0xc8) = Some (p_c v) -> pf_rg rX' (PB3_FI B v) ->
  pf_fi B v pos lyc Sc Wc rX' memc' mdc' /\ pf_obj B v lyc Sc (rdW Wc memc') /\
  sa_rconf (rdW Wc memc') (p_c v) (pf_start (p_rcs v) (p_lab v)) /\
  pf_fsh (rdW Wc memc') (pf_SH v pos) PF_SC_HEAD /\
  (forall i, 0 <= i < 16 -> rdW Wc memc' (pf_F v pos + PF_O_CN + i) = Some 0) /\
  rdword (rdW Wc memc') (pf_s1 v + 0xd8) = Some (pf_SH v pos + 8)).
{ intros rX' memc' mdc' HJ' KM' MG' WC8 HR'.
  assert (K' : pb3_kept v pos (rdW Wc memA) (rdW Wc memc')).
  { apply (pb3_kept_trans v pos _ (rdW Wc memc)); [exact K2|]. split.
    - intros a Ha Hn. apply KM'; [exact Ha|]. intros Hq; apply Hn. unfold pb3_Wr. left. rewrite ESTK. lia.
    - intros a Ha Hv. exact (MG' a Hv). }
  destruct (pb3_fi_of v pos lyc Sc Wc memA rX' memc' mdc' HFR HFA HJ' K' WC8 HR') as (HFI' & HOBJ').
  split; [exact HFI'|]. split; [exact HOBJ'|].
  split; [apply (pb3_same_rconf_on (rdW Wc memc)); [intros a Ha; apply KM'; pb3_ar | exact HRC]|].
  split; [intros i Hi; rewrite KM'; [exact (HFSH i Hi) | pb3_ar | pb3_ar]|].
  split; [intros i Hi; rewrite KM'; [exact (HCN i Hi) | pb3_ar | pb3_ar]|].
  rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [apply (pb3_sl_get _ _ _ _ _ HSL); pb3_in|].
  intros k Hk. apply KM'; pb3_ar. }
psrr_branch_pi RUNP BR HS.
- (* t[0] <> 0: the setup, to HEAD 0x881f8 *)
  rewrite branch_ne_U, (U_atom E0 35 t0 E35), U_lit in Hc by lia.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_sh RUNTO HS HJ (AF_reac_segconf_parse_file + 0x3c0).
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc0 fr0 lyx own) end.
    eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (pf_s1 v - pf_sp0 v));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; rewrite ESTK; lia | cbn [YP09.r_whi]; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  pb3_clear_md. rename ms into msP. rename ms0 into ms.
  assert (KMb : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v <= a < pf_s1 v + 0xd8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite <- (KMa a Ha Hn). apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem msP) (ms_mem ms)
      (fun a => pf_s1 v <= a < pf_s1 v + 0xd8) HFr); [| exact Ha | exact Hn].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia |]).
    destruct Hin'. }
  assert (MGb : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem msP) (ms_mem ms) a HG (MGa a Hv))).
  pb3_hr0 HS Wc HR0.
  assert (WC8 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0xc8) = Some (p_c v)) by pb3_slot HR0 U9.
  assert (QF : pf_rg (ms_regs ms) (PB3_FI B v)).
  { unfold pf_rg, PB3_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_regh HS EE HRG. }
  assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ [(27, p_t v + Z.of_nat 0); (24, 0)])).
  { unfold pf_rg, PF_RL. cbn [app Z.of_nat]. rewrite Z.add_0_r.
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_regh HS EE HRG. }
  destruct (EFIN (ms_regs ms) (ms_mem ms) mdv0 HJ KMb MGb WC8 QF) as (HFI' & HOBJ' & HRC' & HFSH' & HCN' & WD8).
  pmkst HS.
  rewrite pb3_post, b3f_parse_fst.
  refine (HH (length (p_s v)) fx v pos lyc Sc Wc _ _ _ (pf_start (p_rcs v) (p_lab v)) None [] 0%nat 0 [] _).
  split; [split; [exact HCX | split; [exact HFI' | split; [exact HOBJ' | split; [| exact HFSH']]]]|].
  { unfold pf_sl, PF_SL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      first [exact WD8 | pb3_slot HR0 U9]. }
  split; [exact (pf_lctx_start _)|].
  split; [exact (pb3_t0_len _ (fun H => Hc (eq_trans Et0 H)))|].
  split; [exact (Nat.le_refl (length (p_s v)))|].
  split.
  { split; [exact HRC'|]. split; [exact I|].
    split; [exact (b3f_nm_nil _ _ HCN')|].
    split; [exact (b3f_cnt_start (p_rcs v) (p_lab v) (p_s v) Hrf Hov Hl65)|].
    cbn [pf_cur_ptr]. pb3_slot HR0 U9. }
  exact QL.
- (* t[0] = 0: the empty text, to DONE 0x89114 *)
  rewrite branch_ne_U, (U_atom E0 35 t0 E35), U_lit in Hc by lia.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (Hsnil : p_s v = []) by exact (pb3_t0_nil _ Hn0 (eq_trans (eq_sym Et0) Hc)).
  paj_run_to_sh RUNTO HS HJ (AF_reac_segconf_parse_file + 0x12dc).
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc0 fr0 lyx own) end.
    eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (pf_s1 v - pf_sp0 v));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; rewrite ESTK; lia | cbn [YP09.r_whi]; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  pb3_clear_md. rename ms into msP. rename ms0 into ms.
  assert (KMb : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v <= a < pf_s1 v + 0xd8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite <- (KMa a Ha Hn). apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem msP) (ms_mem ms)
      (fun a => pf_s1 v <= a < pf_s1 v + 0xd8) HFr); [| exact Ha | exact Hn].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia |]).
    destruct Hin'. }
  assert (MGb : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem msP) (ms_mem ms) a HG (MGa a Hv))).
  pb3_hr0 HS Wc HR0.
  assert (WC8 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0xc8) = Some (p_c v)) by pb3_slot HR0 U9.
  assert (QF : pf_rg (ms_regs ms) (PB3_FI B v)).
  { unfold pf_rg, PB3_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_regh HS EE HRG. }
  assert (QD : pf_rg (ms_regs ms) [(21, pf_SH v pos)]).
  { unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_regh HS EE HRG. }
  destruct (EFIN (ms_regs ms) (ms_mem ms) mdv0 HJ KMb MGb WC8 QF) as (HFI' & HOBJ' & HRC' & HFSH' & HCN' & WD8).
  pmkst HS.
  rewrite pb3_post, (b3f_parse_done _ _ _ Hsnil).
  refine (HD fx v pos lyc Sc Wc _ _ _ (pf_start (p_rcs v) (p_lab v)) _).
  split; [exact HCX|]. split; [exact HFI'|]. split; [exact HOBJ'|]. split; [exact HRC'|].
  split; [unfold pf_sl; repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_slot HR0 U9|].
  split; [exact HFSH' | exact QD].
Qed.

End x.
End d.
