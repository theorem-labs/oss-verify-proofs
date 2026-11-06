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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 285 of its 337 lines of code are new or changed and 5001 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the piece MISS -> KLOOP of segment A11b of
   reac_segconf_parse_file's walk, `pfm_miss_ok : forall n, HA_KLOOP B n 0 -> H_MISS B n` (statements:
   lib/A/Prog/pf_pieces.v:623-636 and lib/A/Prog/pf_a11b_d.v). Part of segment A11b's proof, by the G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment A11b, piece MISS; reuse search and CONFIRM:
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md,
   the rule-24 check 2026-10-30T15:42:08Z; reuse verdict none).

   The code (the excerpt in the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s), 45 instructions, 0x885a8 .. 0x88658:
     0x885a8 sd s9,0x18(s1)                 slot 0x18 = vp
     0x885ac .. 0x88624  31 x sb zero,X(s11)  cells 0x64..0x81 and 0x8a = 0: known[240] and ntok in scope
     0x88628 ld s3,0x70(s1)                 s3 = F + 0x450 (slot 0x70, PF_SL)
     0x8862c sd zero,0(s3)                  ntok = 0 (no inline check: its shadow cell was just set to 0)
     0x88630 mv a0,s3 ; 0x88634 jal reac_box_catalogue
     0x88638 ld a1,0(s3)                    a1 = 11 (the callee's post)
     0x8863c a2 = 240 ; 0x88640 beqz a1,0x886c8 (not taken: 11) ; s7 = a0 ; s9 = 0 ; s4 = s6 + (a0 >> 3) ;
     s3 = 1 ; s8 = a0                       then 0x8865c, the loop head KLOOP at pass 0.
   The proof: a run of the PLAIN symbolic executor (it stores into the shadow band) from the seed pfm_seed1
   (lib/A/Prog/pf_a11b_m1.v) to the call; the cut state at the call rebuilt by pfm_move at known's scope; the
   call by PaNoChain.cl_callS_wide (the callee's footprint [F + 0x450, F + 0x458) lies in the caller's own
   class-5 frame, not in a block, and its post is apost_base, so the FP state is unchanged), its premises by
   the closed call-site lemma reac_box_catalogue_site_ok, the frame chain by pf_a5_k.a5_chain; a second plain
   run from pfm_seed2 to the loop head; INV_KLOOP by pfm_assemble.
   Section hypotheses: CAT (the callee contract at the listing's entry and image A's numbers) and SIGP (the
   call target BASE + AF_reac_box_catalogue). No SSPX, VRO, OBJ or TL: the stack-protector cells and the
   read-only window are carried through the image range (pf_a11b_m1.v's pfm_img_far). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  reac_box_catalogue_c pf_pieces pf_a5_k pf_a11b_d pf_a11b_f pf_a11b_m1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= tactics (lib/A/Prog/pf_a2.v's pa2_rreg / pa2_clear_md / pa2_atom) ======================= *)
Ltac pfm_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pfm_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* a register the run left as its own atom, back to the seed's register file (R: a lemma over a list) *)
Ltac pfm_atom HS EE R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    pfm_rreg HS; rewrite pfm_den_atom0;
    lazymatch goal with |- ew _ ?n = _ => rewrite (EE n (Z_to_bv 5 k) eq_refl) end;
    apply R; unfold a5_FI, PF_RL, PF_RM; pfm_in end.
(* after the call and the second run: a callee-saved register, through the callee (HP2) to the call state *)
Ltac pfm_fin HS2 EE2 HP2 QR1 :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    pfm_rreg HS2; rewrite pfm_den_atom0;
    lazymatch goal with |- ew _ ?n = _ => rewrite (EE2 n (Z_to_bv 5 k) eq_refl) end;
    rewrite (HP2 k ltac:(unfold acallee_saved; lia)); apply QR1; unfold a5_FI, PF_RM; pfm_in end.

(* ======================= reading a region the run wrote (lib/A/Prog/pf_a2.v) ======================= *)
Definition pfm_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
(* s4 = s6 + (a0 >> 3) at 0x88650 *)
Lemma pfm_den_s4 : forall E sb x, ew E 22 = Z_to_bv 64 sb -> ew E 10 = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 ->
  0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3))) = Z_to_bv 64 (sb + x / 8).
Proof.
intros E sb x H22 H10 Hx Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3))))).
f_equal. change (U E (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3))) = sb + x / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3.
rewrite (U_atom E 22 sb H22 ltac:(lia)), (U_atom E 10 x H10 ltac:(lia)).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
apply zcanon_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma pfm_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> pfm_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.
Lemma pfm_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.

Section e.
Variable B : asyms.
(* the program callee, at the listing's entry and image A's numbers (the A11b brief's text) *)
Hypothesis CAT : forall fx0 : YK11.FPState,
  @reac_box_catalogue_contract fx0 rc SK SEGS B (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
(* the listing's facts over the abstract instance (SegObj.v): the call target *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Theorem pfm_miss_ok : forall n : nat, HA_KLOOP B n 0 -> H_MISS B n.
Proof.
intros n HK v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
pose proof HI as (HB & HMID & HST & HSTR & HINB & HBT & HSL & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFR.
pose proof HB as (HCX & HFI & HOBJ & HSLB & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold kLowMemEnd, kHighShadowEnd in G11, G12.
rewrite SPF in G1.
pose proof HINB as HINB'. unfold pf_inb, PF_O_BUF in HINB'.
assert (Hvp : 0 <= vp < 2 ^ 64) by lia.
assert (Hs16 : pf_s1 v mod 16 = 0).
{ rewrite (Z.div_mod (pf_s1 v) 32) by lia. rewrite G5, Z.add_0_r.
  replace (32 * (pf_s1 v / 32)) with ((2 * (pf_s1 v / 32)) * 16) by lia. apply Z_mod_mult. }
assert (RF : forall r x, In (r, x) (a5_FI B v) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x H; exact (a5_rg_get rX _ r x HFR H)).
assert (RM : forall r x, In (r, x) (PF_RL v pos ++ PF_RM v o ln ++ [(25, vp)]) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x H; exact (a5_rg_get rX _ r x HRG H)).

(* ---- 0x885a8 .. the jal at 0x88634: the plain executor from pfm_seed1 ---- *)
pose proof (pfm_seed1 B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_L146 HB
  ltac:(unfold pf_rg; apply Forall_cons; [cbn [fst snd]; apply RM; unfold PF_RL; pfm_in | apply Forall_nil])) as HS.
set (E := pfm_E1 v pos rX) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pfm_E1; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; unfold pfm_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (pf_F v pos + PF_O_NTOK))
  by (subst E; unfold pfm_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply RF; unfold a5_FI; pfm_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos)) by (apply RM; unfold PF_RL; pfm_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos + PF_O_NTOK)
  by (rewrite E32; apply unsigned_lit_small; unfold PF_O_NTOK; lia).
unfold cfg_at. change (w64 (BASE + PF_MISS)) with (Z_to_bv 64 (BASE + PF_MISS)).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ intros a (r & Hr & Ha). unfold pfm_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite U9 in Ha. rewrite SPF. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). change (fs_frame_bytes 5 / 8) with 256.
    rewrite U27 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). change (fs_frame_bytes 5 / 8) with 256.
    rewrite U27 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
    rewrite U32 in Ha. unfold PF_O_NTOK in Ha. lia. }
pfm_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem pfm_ss1) (w_H Wc) memc (ms_mem ms) (pfm_Wr v pos) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin'];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U27, ?U32 in Hrr; unfold pfm_Wr, PF_O_NTOK in *;
     rewrite SPF; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2 end.
cbn [ms_mem restrict] in HR0, HR1, HR2.
assert (W18 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 24) = Some vp).
{ eapply (pfm_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 24 (SOff 25 0) vp HR0 U9);
    [pfm_in | | exact Hvp].
  rewrite pfm_den_atom0, (EE 25%nat (Z_to_bv 5 25) eq_refl). apply RM. unfold PF_RL, PF_RM. pfm_in. }
assert (W1c : forall i, 0x64 <= i < 0x82 \/ i = 0x8a -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0).
{ intros i [Hi | ->].
  - apply (pfm_cell_of_region E (w_H Wc) (ms_mem ms) 27 _ _ _ _ _ _ i _ HR1 U27). revert i Hi.
    apply (pfm_zrange (fun i => pfm_cell_ok _ i 0) 0x64 30). vm_compute. reflexivity.
  - apply (pfm_cell_of_region E (w_H Wc) (ms_mem ms) 27 _ _ _ _ _ _ 0x8a _ HR2 U27). vm_compute. reflexivity. }
(* the registers at the call *)
assert (QR1 : forall r x, In (r, x) (a5_FI B v ++ [(18, 0x23); (27, pf_SH v pos)] ++ PF_RM v o ln ++ [(25, vp)]) ->
  getr (ms_regs ms) (Z_to_bv 5 r) = w64 x).
{ intros r x Hr. unfold a5_FI, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-; first [pfm_atom HS EE RF | pfm_atom HS EE RM] |]).
  destruct Hr. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_KRET)) by (pfm_rreg HS; exact (codeptr_val _ 14596 HEI)).
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v))
  by (eapply (pfm_bvr _ _ 2); [reflexivity | apply QR1; unfold a5_FI; pfm_in]).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (eapply (pfm_bvr _ _ 3); [reflexivity | apply QR1; unfold a5_FI; pfm_in]).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (eapply (pfm_bvr _ _ 4); [reflexivity | apply QR1; unfold a5_FI; pfm_in]).
assert (Q8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v))
  by (eapply (pfm_bvr _ _ 8); [reflexivity | apply QR1; unfold a5_FI; pfm_in]).
assert (Q10 : getr (ms_regs ms) 10 = w64 (pf_F v pos + PF_O_NTOK))
  by (pfm_rreg HS; rewrite pfm_den_atom0; exact E32).
assert (Q19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (pf_F v pos + PF_O_NTOK))
  by (pfm_rreg HS; rewrite pfm_den_atom0; exact E32).
pmkst HS.
rewrite (SIGP SS_reac_box_catalogue ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_box_catalogue) with AF_reac_box_catalogue by (vm_compute; reflexivity).
(* the cut state at the call: known and ntok in scope *)
assert (HB1 : pf_base B v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_KN).
{ apply (pfm_move B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_L146 Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_KN HB HJ).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - exact K1.
  - intros a _ Hv. exact (M1 a Hv).
  - unfold pf_rg. rewrite Forall_forall. intros [r x] Hx. apply QR1. apply in_or_app. left. exact Hx.
  - exact HFRM.
  - exact (pfm_fsh_kn v pos _ _ G K1 W1c HFSH). }
destruct (reac_box_catalogue_site_ok B v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv HB1 Q10)
  as (H10 & Hc64 & Harm & HEV).
destruct (a5_chain B _ _ _ _ _ _ _ _ _ HB1) as (ch1 & Hch).
set (c := pf_F v pos + PF_O_NTOK) in *.
assert (Ec : (c =? 0) = false) by (apply Z.eqb_neq; subst c; unfold PF_O_NTOK; lia).
assert (Hsp1 : spZ (ms_regs ms) = pf_s1 v) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* ---- 0x88634: jal reac_box_catalogue (a0 = &ntok), returning at 0x88638 ---- *)
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx) B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc mdv 0
    STK_reac_box_catalogue [(c, c + 8)] EV_reac_box_catalogue (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + PF_KRET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 catA /\ (c <> 0 -> sa_val (rdW W2 mem2) c 8%nat 11) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) STK_reac_box_catalogue (fun a => c <> 0 /\ c <= a < c + 8) /\
       sa_noalloc B (p_ly v) Sc ly2 S2) HJ).
  - rewrite Hsp1. lia.
  - rewrite Zminus_mod, Hs16, G3. reflexivity.
  - lia.
  - unfold STK_reac_box_catalogue. lia.
  - rewrite SPF. unfold STK_reac_box_catalogue. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [change PF_KRET with 14596; lia | reflexivity].
  - rewrite unsigned_lit_small by (change PF_KRET with 14596; lia). change PF_KRET with 14596. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    replace (s0Z (ms_regs ms)) with (pf_sp0 v) by (unfold s0Z; rewrite Q8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    exact Hch.
  - intros HPRE1. eapply SRr_mono.
    { exact (CAT fx (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 c HPRE1 H10 Hc64 Harm HEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    rewrite Ec in HJ'. split; [exact HJ' | split; [exact HP' | exact HK']].
  - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
    subst c. unfold PF_O_NTOK in *. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    exfalso. subst c. unfold PF_O_NTOK in *. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Ha02 & Hval2 & Hkept2 & HNA2)).
destruct HNA2 as (HPm2 & Hly2 & (f2 & HS2e)). subst ly2.
assert (Hc0 : c <> 0) by (subst c; unfold PF_O_NTOK; lia).
(* what the call kept: everything outside its window [s1 - 16, s1) and ntok *)
assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ pfm_Wr v pos a -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hn. apply (Hkept2 a Ha).
  - rewrite Hsp1. intros Hw. apply Hn. left. rewrite SPF. unfold STK_reac_box_catalogue in Hw. lia.
  - intros (_ & Hw). apply Hn. right; right; right. subst c. exact Hw. }
assert (M12 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a <> None -> rdW W2 mem2 a <> None).
{ intros a Ha Hv.
  destruct (Z_le_gt_dec (pf_s1 v - 16) a) as [L1 | L1]; [destruct (Z_lt_le_dec a (pf_s1 v)) as [L2 | L2]|].
  - pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
    apply (aview_some_of_apresent SEGS). apply Hpr. unfold STK_reac_box_catalogue. lia.
  - rewrite (Hkept2 a Ha); [exact Hv | rewrite Hsp1; unfold STK_reac_box_catalogue; lia |].
    intros (_ & Hw). subst c. unfold PF_O_NTOK in *. lia.
  - destruct (Z_le_gt_dec c a) as [L3 | L3]; [destruct (Z_lt_le_dec a (c + 8)) as [L4 | L4]|].
    + pose proof (proj1 HJ2) as HAR2. pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr2 & _).
      assert (Hin2 : In (5, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
      destruct (al_frames _ _ LAWS (p_ly v) S2 W2 mem2 md2 5 pos HAR2 Hin2) as (_ & _ & Hfb & _).
      apply (aview_some_of_apresent SEGS). apply (proj1 (Hfb a ltac:(change (frame_addr (p_ly v) 5 pos) with (pf_F v pos);
        change (fs_frame_bytes 5) with 2048; subst c; unfold PF_O_NTOK in *; lia))).
    + rewrite (Hkept2 a Ha); [exact Hv | rewrite Hsp1; unfold STK_reac_box_catalogue; lia | intros (_ & Hw); lia].
    + rewrite (Hkept2 a Ha); [exact Hv | rewrite Hsp1; unfold STK_reac_box_catalogue; lia | intros (_ & Hw); lia]. }
assert (Ha02z : getr regs2 (Z_to_bv 5 10) = w64 catA) by (rewrite <- Ha02; f_equal; apply bv_eq; reflexivity).
assert (R19 : getr regs2 (Z_to_bv 5 19) = w64 c) by (rewrite (HP2 19 ltac:(unfold acallee_saved; lia)); exact Q19).
(* ---- 0x88638 .. 0x8865c: the plain executor from pfm_seed2 to the loop head ---- *)
pose proof (pfm_seed2 W2 regs2 mem2 c R19 ltac:(subst c; unfold PF_O_NTOK; lia) ltac:(subst c; unfold PF_O_NTOK; lia)
  (Hval2 Hc0)) as HS2.
set (E2 := Eimg (Ereg regs2 [])) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E2 n0 = getr regs2 r)
  by (intros n0 r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
paj_run_to_shc (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS2 HJ2 PF_KLOOP.
{ unfold pfm_ss2. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pfm_clear_md.
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E2 (ss_mem pfm_ss2) (w_H W2) mem2 (ms_mem ms0) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin' as [Hq | []]. injection Hq as <- <- <-.
  cbn [base_val] in Hrr. lia. }
assert (M23 : forall a, rdW W2 mem2 a <> None -> rdW W2 (ms_mem ms0) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H W2) mem2 (ms_mem ms0) a HG Hv)).
(* the registers at the loop head *)
assert (QR3 : pf_rg (ms_regs ms0) (pfm_R3 B v pos o ln)).
{ unfold pf_rg, pfm_R3, a5_FI, PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: try solve [pfm_fin HS2 EE2 HP2 QR1].
  all: try solve [pfm_rreg HS2; reflexivity].
  - pfm_rreg HS2. rewrite (pfm_den_s4 E2 SHADOW_OFF catA); [reflexivity | | | unfold catA; lia | unfold SHADOW_OFF; lia].
    + rewrite (EE2 22%nat (Z_to_bv 5 22) eq_refl), (HP2 22 ltac:(unfold acallee_saved; lia)).
      apply QR1. unfold a5_FI. pfm_in.
    + rewrite (EE2 10%nat (Z_to_bv 5 10) eq_refl). exact Ha02z.
  - pfm_rreg HS2. rewrite pfm_den_atom0, (EE2 10%nat (Z_to_bv 5 10) eq_refl). exact Ha02z. }
pmkst HS2.
change (Z_to_bv 64 (BASE + 14632)) with (w64 (BASE + PF_KLOOP)).
apply (HK fx v pos (p_ly v) S2 W2 (ms_regs ms0) (ms_mem ms0) _ cf nm o ln d gi vp val).
apply (pfm_assemble B n v pos (p_ly v) Sc Wc rX memc mdc cf nm o ln d gi vp val S2 W2 (ms_regs ms0) (ms_mem ms0) _ HI).
- eapply ajournal_mono_k; [exact HJ2 | unfold EV_reac_box_catalogue; lia].
- exists f2. exact HS2e.
- exact HPm2.
- intros a Ha Hn. rewrite (K23 a Ha), (K12 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha Hv. apply M23. apply (M12 a Ha). exact (M1 a Hv).
- exact HFRM.
- exact QR3.
- intros i Hi. assert (Hr : 0 <= pf_SH v pos + i < 2 ^ 64) by lia.
  rewrite (K23 _ Hr). rewrite (Hkept2 _ Hr); [exact (W1c i Hi) | rewrite Hsp1; unfold STK_reac_box_catalogue; lia |].
  intros (_ & Hw). subst c. unfold PF_O_NTOK in *. lia.
- rewrite (rdword_ext (rdW Wc (ms_mem ms)) (rdW W2 (ms_mem ms0)) (pf_s1 v + 24)); [exact W18|].
  intros k Hk. assert (Hr : 0 <= pf_s1 v + 24 + k < 2 ^ 64) by lia.
  rewrite (K23 _ Hr). rewrite (Hkept2 _ Hr); [reflexivity | rewrite Hsp1; unfold STK_reac_box_catalogue; lia |].
  intros (_ & Hw). subst c. unfold PF_O_NTOK in *. lia.
- intros k Hk. fold c. assert (Hr : 0 <= c + Z.of_nat k < 2 ^ 64) by (subst c; unfold PF_O_NTOK; lia).
  rewrite (K23 _ Hr). exact (Hval2 Hc0 k Hk).
Qed.

End e.
End f.
End d.
