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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 583 of its 656 lines of code are new or changed and 4980 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B11b's head, MISS 0x88a50 ->
   KLOOP 0x88b14 (pass 0): the 31 scope-in stores, ntok = 0, reac_box_catalogue, the two trap flags. The B11b segment lane of
   the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk, the
   head of segment B11b: pb11a_head : HA_KLOOP n 0 -> H_MISS n).
    ADAPTED from the image-A G3 walk owner's image-A lanes (a working branch's pf_a11b_d.v KRET; the A2 segment lane's pf_a2.v seed / run
   / region reading) and the image-B G3 walk owner's B10b join piece (pf_seg_B10b_j.v, the B seed on s5's atom), re-derived on
   image B's code; the program call by reac_segconf_parse.v's cl_callSF form (here cl_callS_wideF: the callee's
   footprint is a slot of the walk's own class-5 frame).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     0x88a50 .. 0x88ac8  31 `sb zero,X(s5)`, X = 0x64 .. 0x81 and 0x8a (known and ntok in scope)
     0x88acc ld s3,128(s1)   slot 0x80 = F + 0x450 = &ntok (PF_SL)
     0x88ad0 sd zero,0(s3)   ntok = 0
     0x88ad4 mv a0,s3
     0x88ad8 jal reac_box_catalogue   KCAT (a0 = &ntok, sp = s1; returns 0x88adc)
     0x88adc ld a1,0(s3)     KRET: a1 = ntok = 11 (the callee's post)
     0x88ae0 li a2,240; 0x88ae4 beqz a1,KREFM (not taken: 11)
     0x88ae8 mv a4,a0 (tab = catA); li s3,0; li s11,0; snez a1,a0; andi a0,a0,7; seqz a0,a0
     0x88b00 sd a1,104(s1) (slot 0x68 = 1); and a0,a0,a1; 0x88b08 sd a0,96(s1) (slot 0x60 = 1); mv s8,a4; mv s7,a4
     0x88b14 KLOOP (pass 0)
   Checks: none in this part (B#28 is the loop's). Traps: none in this part (T23 - T27 are the loop's; their two
   flags are set here). Calls: reac_box_catalogue (C42).
   The proof: run 1 of the PLAIN executor from a seed at MISS (pb11a_ss1: the shadow cells as writable regions on s5's
   atom, slot 0x80 as a read-only chunk on s1's atom naming the extra atom 32 = &ntok, ntok writable on atom 32) to
   the call; the cut INV_KC at the callee's entry; the call by cl_callS_wideF and the contract CAT; the cut INV_KRET at
   the return (at the FP state the call returns); run 2 from a seed at KRET (pb11a_ss2: ntok = 11 as a chunk on s3's
   atom, slots 0x60 .. 0x70 writable on s1's atom, a0 pinned to catA) to KLOOP.
   SECTION HYPOTHESES: CAT (pf_pieces.v's for B11b: reac_box_catalogue_contract at BASE + AF_reac_box_catalogue,
   STK_reac_box_catalogue, catA, at every FP state); SIGP (the listing's seg_sig_prog over the walk's abstract PAImg
   instance, B's SegObj.v, as reac_segconf_parse.v takes it: the call target pa_sigma SS_reac_box_catalogue is
   BASE + AF_reac_box_catalogue). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
  reac_box_catalogue_c SegInstB pf_pieces pf_seg_B11b_d pf_seg_B11b_f pf_seg_B11b_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_a2.v / pf_seg_B10b_j.v) ---------- *)
Lemma pb11a_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pb11a_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma pb11a_set_fs_id : forall s, s = set_fs (st_fs s) s.
Proof. intros s. destruct s. reflexivity. Qed.
Ltac pb11a_in := solve [unfold PF_RL, PF_RM, pb11_FI; cbn [In app]; repeat first [left; reflexivity | right]].
Ltac pb11a_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pb11a_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis CAT : forall fx0 : YK11.FPState, reac_box_catalogue_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
Hypothesis SIGP : seg_sig_prog (PI := PI).

(* ---------- reading a region the run wrote (pf_a2.v) ---------- *)
Definition pb11a_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma pb11a_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> pb11a_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
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
Lemma pb11a_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
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
(* the 8 bytes sa_val names, as the run's chunk reads them *)
Lemma pb11a_val_mem_of_sa_val : forall H m a v, 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H m) a 8%nat v -> val_mem SEGS (mrestrict H m) a 8 v.
Proof.
intros H m a v Hv HS k Hk. specialize (HS k Hk). unfold aview in HS.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in HS. injection HS as Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small; [exact Hb|].
cbv [OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YO0f.le_byte]. apply Z.mod_pos_bound. lia.
Qed.
Lemma pb11a_sa_val_of_val_mem : forall H m a v,
  val_mem SEGS (mrestrict H m) a 8 v -> sa_val (aview SEGS H m) a 8%nat v.
Proof.
intros H m a v HV k Hk. unfold aview. rewrite (HV k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* the reader wraps addresses modulo 2^64 (mbyte reads Z_to_bv 64 a) *)
Lemma pb11a_aview_mod : forall H m a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let pb11a_RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let pb11a_RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let pb11a_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

(** ** The cut at the return from reac_box_catalogue (KRET, 0x88adc): known / ntok in scope, ntok = 11, s3 = &ntok
    (callee-saved across the call), a0 = catA (the callee's post) *)
Definition INV_KRET (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  sa_val (rdW Wc memc) (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(19, pf_F v pos + PF_O_NTOK); (10, catA)]).

(* ---------- run 2: KRET (0x88adc) -> KLOOP (0x88b14), pass 0 ---------- *)
Definition pb11a_regions2 : smem :=
  [YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 11))];
   YP09.mkRegion (Some 9%nat) 0x60 0x70 0x60 0x70 []].
Definition pb11a_ss2 : sstate :=
  mkSS PF_KRET (sr_set sr_atoms (Z_to_bv 5 10) (SLit catA)) pb11a_regions2 None (mkFacts [] [] []).
Lemma pb11a_seed2 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KRET n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) pb11a_ss2
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KRET)) memc (seg_rom SEGS))).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HB & _ & _ & _ & _ & HNT & _ & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof (proj1 HB) as HCX.
pose proof HB as (_ & (HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in Hpres.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (pf_F v pos + PF_O_NTOK)) by (apply (pb11_rg_get rX _ 19 _ HRG); pb11a_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 catA) by (apply (pb11_rg_get rX _ 10 _ HRG); pb11a_in).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb11_rg_get rX _ 9 _ HFI); pb11a_in).
assert (U19 : bv_unsigned (ew E 19) = pf_F v pos + PF_O_NTOK)
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; unfold w64, PF_O_NTOK; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL E (mkSS PF_KRET sr_atoms pb11a_regions2 None (mkFacts [] [] []))
  (mkst rX (Z_to_bv 64 (BASE + PF_KRET)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pb11a_regions2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [unfold PF_O_NTOK; lia|]. split; [unfold PF_O_NTOK; lia|]. split; [intros o0 Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SLit 11) 11); [reflexivity | cbn; lia | cbn; lia|].
      rewrite Z.add_0_r. apply pb11a_val_mem_of_sa_val; [lia | exact HNT].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o0 Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, pb11a_regions2.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PF_O_NTOK.
    repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 10) catA HS0 R10 eq_refl).
Qed.

Lemma pb11a_r2 : forall n, HA_KLOOP B n 0 ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KRET n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KRET) rX memc mdc) (PB11_POST B v cf gi nm val o ln).
Proof.
intros n KLOOP v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
pose proof (pb11a_seed2 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI) as HS.
pose proof HI as (HB & HMID & HST & HVP & HINB & HNT & H70 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSL & HFSH).
pose proof HFIb as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb11_rg_get rX _ 9 _ HFI); pb11a_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_KRET)) with (Z_to_bv 64 (BASE + PF_KRET)).
(* 0x88adc .. 0x88b10: ntok, the beqz (not taken), the flags to slots 0x68 / 0x60, s3 / s11 / s7 / s8 / a4 / a2 *)
paj_run_to_sh pb11a_RUNTO HS HJ PF_KLOOP.
{ intros a (r & Hr & Ha). unfold pb11a_ss2, pb11a_regions2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
  left. rewrite U9 in Ha. rewrite SPF. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
pb11a_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x60 <= a < pf_s1 v + 0x70) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem pb11a_ss2) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_s1 v + 0x60 <= a < pf_s1 v + 0x70) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
cbn [ms_mem restrict] in HR1.
assert (W60 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0x60) = Some 1).
{ eapply (pb11a_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x60 (SLit 1) 1 HR1 U9);
    [pb11a_in | reflexivity | lia]. }
assert (W68 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0x68) = Some 1).
{ eapply (pb11a_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x68 (SLit 1) 1 HR1 U9);
    [pb11a_in | reflexivity | lia]. }
(* the registers at KLOOP *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pb11a_rreg HS; rewrite pb11a_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Q19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 0) by (pb11a_rreg HS; reflexivity).
assert (Q27 : getr (ms_regs ms) (Z_to_bv 5 27) = w64 0) by (pb11a_rreg HS; reflexivity).
assert (Q23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 catA) by (pb11a_rreg HS; reflexivity).
assert (Q24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 catA) by (pb11a_rreg HS; reflexivity).
assert (Q14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 catA) by (pb11a_rreg HS; reflexivity).
assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 240) by (pb11a_rreg HS; reflexivity).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_KLOOP) rg mm mdx) end.
(* the keep relation over B11b's write set *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true false false a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply K1; [exact Ha|]. intros Hq. apply Hn. right; left. split; [reflexivity | exact Hq]. }
assert (KWt : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply KW; [exact Ha|]. intros Hq. apply Hn. exact (pb11_Wrx_mono v pos _ _ _ a Hq). }
assert (KWf : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true false a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply KW; [exact Ha|]. intros Hq. apply Hn.
  destruct Hq as [Hq | [Hq | [(Hq & _) | (Hq & _)]]]; [left; exact Hq | right; left; exact Hq | discriminate Hq | discriminate Hq]. }
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
apply (KLOOP fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val).
split.
{ apply (pb11_move B fx v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_KNOWN HB HJ
    (ex_intro _ (st_fs Sc) (pb11a_set_fs_id Sc)) (Permutation_refl _) KWt M1).
  - unfold pf_rg, pb11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (pb11_rg_get rX _ _ _ HFI); pb11a_in | pb11a_in]).
  - exact (pb11_keep_fsh v pos _ _ true true PF_SC_KNOWN G KWf HFSH).
  - exact HFRM. }
split; [exact HMID|].
split; [exact (pb11_keep_st B v pos lyc Sc Wc memc mdc Wc (ms_mem ms) G HAR Hin Hly KWt cf (Some gi) nm _ HC5 HST)|].
split; [exact (pb11_keep_buf_str v pos Wc memc Wc (ms_mem ms) G KWt vp val HINB HVP)|].
split; [exact HINB|].
split; [lia|].
split; [exact I|].
split.
{ intros k Hk. rewrite KW; [exact (HNT k Hk) | unfold PF_O_NTOK; lia |].
  unfold pb11_Wrx, PF_O_KNOWN, PF_O_NTOK. rewrite SPF in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  intros [Hq | [Hq | [(Hq & _) | (Hq & _)]]]; [lia | destruct Hq as [_ Hq]; lia | discriminate Hq | discriminate Hq]. }
split.
{ unfold pf_sl. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; [exact W60 | exact W68|].
  apply Forall_inv in H70. cbn [fst snd] in H70.
  rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [exact H70|].
  intros k Hk. apply K1; lia. }
unfold pf_rg, PF_RL, PF_RM in HRG |- *. cbn [app] in HRG |- *.
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [ rewrite QK; [apply (pb11_rg_get rX _ _ _ HRG); pb11a_in | pb11a_in]
        | exact Q19 | exact Q27 | exact Q23 | exact Q24 | exact Q14 | exact Q12 ].
Qed.
End x.

Lemma pb11a_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Section y. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The cut at reac_box_catalogue's entry (0x8a8a0, from KCAT 0x88ad8): known / ntok in scope, ntok = 0,
    a0 = s3 = &ntok, ra = KRET *)
Definition INV_KC (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(19, pf_F v pos + PF_O_NTOK); (10, pf_F v pos + PF_O_NTOK)]) /\
  getr rX 1 = w64 (BASE + PF_KRET).

(* the state reac_box_catalogue returns (at its FP state f1) is the cut KRET *)
Lemma pb11a_after : forall (f1 : YK11.FPState) n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val S2 W2 regs2 mem2 md2,
  INV_KC n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  fxrel fx f1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc S2 W2 mem2 md2 0 ->
  aregs_preserved rX regs2 ->
  getr regs2 10 = w64 catA ->
  sa_val (rdW W2 mem2) (pf_F v pos + PF_O_NTOK) 8%nat 11 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 16 <= a < pf_s1 v) ->
     ~ (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8) -> rdW W2 mem2 a = rdW Wc memc a) ->
  Permutation (ablocks B lyc S2) (ablocks B lyc Sc) -> (exists f, S2 = set_fs f Sc) ->
  INV_KRET (fx := f1) n v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d gi vp val.
Proof.
intros f1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val S2 W2 regs2 mem2 md2 HI Hfx HJ2 HP2 H10 HNT HK
  HPERM2 [f2 HS2].
destruct HI as (HB & HMID & HST & HVP & HINB & H70 & HRG & _).
pose proof (pb11_geo (fx := fx) B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _ & _).
pose proof (pb11_fi_regs (fx := fx) B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & HFIb & HOBJ & _ & HFSH).
pose proof HFIb as (_ & _ & _ & _ & _ & _ & HFRM & _).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (GW : forall a, pb11_Wrx v pos true true false a \/ ~ (pf_s1 v - 16 <= a < pf_s1 v) /\
  ~ (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8)).
{ intros a. clear - G.
  pose proof STK_values as (_ & _ & _ & SPF & _).
  destruct G as (G1 & G2 & G3 & G4 & _).
  destruct (Z_lt_le_dec a (pf_s1 v - 16)) as [L1 | L1]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L2 | L2]].
  - destruct (Z_lt_le_dec a (pf_F v pos + PF_O_NTOK)) as [L3 | L3];
      [right; split; lia | destruct (Z_lt_le_dec a (pf_F v pos + PF_O_NTOK + 8)) as [L4 | L4]; [|right; split; lia]].
    left. right; right; left. split; [reflexivity|]. right. unfold PF_O_NTOK in *. lia.
  - left. left. rewrite SPF. lia.
  - destruct (Z_lt_le_dec a (pf_F v pos + PF_O_NTOK)) as [L3 | L3];
      [right; split; lia | destruct (Z_lt_le_dec a (pf_F v pos + PF_O_NTOK + 8)) as [L4 | L4]; [|right; split; lia]].
    left. right; right; left. split; [reflexivity|]. right. unfold PF_O_NTOK in *. lia. }
assert (KEEPf : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true false a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hn. destruct (GW a) as [Hq | (H1 & H2)]; [exfalso; exact (Hn Hq) | exact (HK a Ha H1 H2)]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hn. apply KEEPf; [exact Ha|]. intros Hq. apply Hn. exact (pb11_Wrx_mono v pos _ _ _ a Hq). }
assert (VIS : forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None).
{ intros a0 Hv0. rewrite pb11a_aview_mod in Hv0 |- *.
  set (a := a0 mod 2 ^ 64) in *.
  assert (Ha : 0 <= a < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  clearbody a.
  destruct (Z_lt_le_dec a (pf_s1 v - 16)) as [L1 | L1]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L2 | L2]].
  - destruct (Z_lt_le_dec a (pf_F v pos + PF_O_NTOK)) as [L3 | L3];
      [rewrite (HK a Ha); [exact Hv0 | lia | lia] |].
    destruct (Z_lt_le_dec a (pf_F v pos + PF_O_NTOK + 8)) as [L4 | L4]; [|rewrite (HK a Ha); [exact Hv0 | lia | lia]].
    replace a with (pf_F v pos + PF_O_NTOK + Z.of_nat (Z.to_nat (a - (pf_F v pos + PF_O_NTOK)))) by lia.
    rewrite (HNT (Z.to_nat (a - (pf_F v pos + PF_O_NTOK))) ltac:(lia)). discriminate.
  - apply (aview_some_of_apresent SEGS). apply Hpres2. clear - G L1 L2.
    pose proof STK_values as (_ & _ & _ & SPF & _). destruct G as (G1 & G2 & G3 & G4 & _). rewrite SPF. lia.
  - assert (HF : pf_F v pos + PF_O_NTOK + 8 <= pf_s1 v).
    { clear - G. pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
      destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). rewrite SPF in G1. unfold PF_O_NTOK. lia. }
    rewrite (HK a Ha); [exact Hv0 | lia | lia]. }
split.
{ apply (pb11_move (fx := fx) B f1 v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN S2 W2 regs2 mem2 md2 PF_SC_KNOWN HB HJ2
    (ex_intro _ f2 HS2) HPERM2 KEEP VIS).
  - exact (pb11_rg_pres rX regs2 (pb11_FI B v) HP2 (pb11_FI_cs B v) HFI).
  - exact (pb11_keep_fsh v pos (rdW Wc memc) (rdW W2 mem2) true true PF_SC_KNOWN G KEEPf HFSH).
  - exact (fxrel_frm0 fx f1 HFRM Hfx). }
split; [exact HMID|].
split; [exact (pb11_keep_st B v pos lyc Sc Wc memc mdc W2 mem2 G HAR Hin Hly KEEP cf (Some gi) nm _ HC5 HST)|].
split; [exact (pb11_keep_buf_str v pos Wc memc W2 mem2 G KEEP vp val HINB HVP)|].
split; [exact HINB|].
split; [exact HNT|].
split.
{ apply (pb11_keep_slots v pos _ _ true true true _ G KEEP); [|exact H70].
  repeat constructor; cbn [fst]; lia. }
apply pb11_rg_app in HRG as [HRL HRG']. apply pb11_rg_app in HRG' as [HRM HRX].
pose proof (Forall_inv HRX) as HR19. cbn [fst snd] in HR19.
apply pb11_rg_app; split; [exact (pb11_rg_pres rX regs2 _ HP2 (pb11_RL_cs v pos) HRL)|].
apply pb11_rg_app; split; [exact (pb11_rg_pres rX regs2 _ HP2 (pb11_RM_cs v o ln) HRM)|].
constructor; [cbn [fst snd]; rewrite (HP2 19 ltac:(unfold acallee_saved; lia)); exact HR19|].
constructor; [exact H10 | constructor].
Qed.

Lemma pb11a_call : forall n, HA_KLOOP B n 0 ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KC n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + AF_reac_box_catalogue) rX memc mdc) (PB11_POST B v cf gi nm val o ln).
Proof.
intros n KLOOP v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HB & HMID & HST & HVP & HINB & H70 & HRG & HRA).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSL & HFSH).
pose proof HFIb as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & HNEV & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
destruct (pb11_chain B _ _ _ _ _ _ _ _ _ HB) as (ch1 & HCH).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (SCAT : STK_reac_box_catalogue = 16) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
set (c := pf_F v pos + PF_O_NTOK) in *.
assert (Hc0 : c <> 0) by (unfold c, PF_O_NTOK; lia).
assert (EFP : (if c =? 0 then [] else [(c, c + 8)]) = [(c, c + 8)]) by (rewrite (proj2 (Z.eqb_neq _ _) Hc0); reflexivity).
assert (R2 : getr rX 2 = w64 (pf_s1 v)) by (apply (pb11a_bvr rX _ 2); [reflexivity | apply (pb11_rg_get rX _ 2 _ HFI); pb11a_in]).
assert (R3 : getr rX 3 = w64 (as_gp B)) by (apply (pb11a_bvr rX _ 3); [reflexivity | apply (pb11_rg_get rX _ 3 _ HFI); pb11a_in]).
assert (R4 : getr rX 4 = w64 (as_tp B)) by (apply (pb11a_bvr rX _ 4); [reflexivity | apply (pb11_rg_get rX _ 4 _ HFI); pb11a_in]).
assert (R8 : getr rX 8 = w64 (pf_sp0 v)) by (apply (pb11a_bvr rX _ 8); [reflexivity | apply (pb11_rg_get rX _ 8 _ HFI); pb11a_in]).
assert (R10 : getr rX 10 = w64 c) by (apply (pb11a_bvr rX _ 10); [reflexivity | apply (pb11_rg_get rX _ 10 _ HRG); pb11a_in]).
assert (Hsp : spZ rX = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hs0 : s0Z rX = pf_sp0 v) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (HF8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk. replace (k * 32) with ((4 * k) * 8) by lia.
  apply Z_mod_mult. }
(* the count pointer's facts: ntok's shadow cell 0x8a is 0 (PF_SC_KNOWN), the frame and its shadow present *)
assert (Hcm8 : c mod 8 = 0) by (unfold c, PF_O_NTOK; rewrite Zplus_mod, HF8; reflexivity).
assert (HcSH : forall x, c <= x < c + 8 -> SHADOW_OFF + x / 8 = pf_SH v pos + 138).
{ intros x Hx. rewrite G10. unfold c, PF_O_NTOK in Hx.
  pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite HF8 in DF.
  assert (E : x / 8 = pf_F v pos / 8 + 138).
  { rewrite (Z.div_unique x 8 (pf_F v pos / 8 + 138) (x - pf_F v pos - 1104)); [reflexivity | lia | lia]. }
  lia. }
assert (HRA8 : range_addressable (rdW Wc memc) SHADOW_OFF c 8).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite (HcSH x Hx).
  rewrite (HFSH 138 ltac:(lia)). reflexivity. }
assert (HADDR : sa_addr (rdW Wc memc) c 8).
{ split; [unfold c, PF_O_NTOK; lia|]. split; [unfold c, PF_O_NTOK; lia|].
  split; [unfold amem_range, c, PF_O_NTOK; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9;
          unfold kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia|].
  split; [exact HRA8|].
  intros _ s Hs. unfold shadow_addr in Hs. rewrite (HcSH c ltac:(lia)), (HcSH (c + 8 - 1) ltac:(lia)) in Hs.
  apply (aview_some_of_apresent SEGS).
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia. apply Hshp.
  pose proof (Z.mod_pos_bound (pf_SH v pos + 138) 8 ltac:(lia)).
  pose proof (Z.div_mod (pf_SH v pos + 138) 8 ltac:(lia)).
  lia. }
assert (HDST : sa_dst SEGS B lyc Sc Wc memc rX c 8).
{ left. split; [|exact HRA8]. exists 5, pos. split; [exact Hin|]. split; [lia|].
  subst lyc. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
  unfold c, PF_O_NTOK. lia. }
unfold PB11_POST, pf_postm, PF_POSTr.
eapply srr_after_callF.
{ apply (cl_callS_wideF B LAWS Wc rX memc (Z_to_bv 64 (BASE + AF_reac_box_catalogue)) STK_reac_segconf_parse_file
    (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
    STK_reac_box_catalogue [(c, c + 8)] EV_reac_box_catalogue (pf_s1 v - pf_sp0 v) (w64 (BASE + PF_KRET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 catA /\
       (c <> 0 -> sa_val (rdW W2 mem2) c 8%nat 11) /\
       sa_kept SEGS Wc memc W2 mem2 rX STK_reac_box_catalogue (fun a => c <> 0 /\ c <= a < c + 8) /\
       sa_noalloc B lyc Sc ly2 S2) HJ).
  - exact Hsp.
  - rewrite Zminus_mod, G3. replace (pf_s1 v mod 16) with 0; [reflexivity|].
    pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D. rewrite G5, Z.add_0_r in D. rewrite D.
    replace (32 * (pf_s1 v / 32)) with ((2 * (pf_s1 v / 32)) * 16) by lia. symmetry. apply Z_mod_mult.
  - lia.
  - rewrite SCAT. lia.
  - rewrite SCAT, SPF. lia.
  - exact R3.
  - exact R4.
  - exact HRA.
  - apply ret_ok_codeptr_v; unfold PF_KRET, AF_reac_segconf_parse_file; [lia | reflexivity].
  - unfold w64. rewrite unsigned_lit_small; [|unfold PF_KRET, AF_reac_segconf_parse_file; lia].
    unfold PF_KRET, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia. rewrite Hs0. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { apply (CAT fx lyc Sc Wc rX memc mdc ch1 c HPRE1 R10 ltac:(unfold c, PF_O_NTOK; lia)
        (or_intror (conj Hcm8 (conj HADDR HDST)))).
      unfold EV_reac_box_catalogue, EV_reac_segconf_parse_file in *. lia. }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    rewrite EFP in HJ'.
    exists fx, ly', S', regs', mem', md'. split; [rewrite HRA; reflexivity|].
    split; [intros k _; reflexivity|]. split; [left; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    unfold awr_byte. right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. subst lyc. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos).
    change (fs_frame_bytes 5) with 2048. unfold c, PF_O_NTOK in Ha. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. exfalso. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    rewrite SPF in Hw. unfold c, PF_O_NTOK in Ha. lia. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 Hle Hfx (HJ2 & HJc & HP2 & (H10 & HNT & HKEEP & HNA)).
destruct HNA as (HPERM2 & -> & HS2).
replace (0 + EV_reac_box_catalogue) with 0 in HJ2 by reflexivity.
assert (HKP : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 16 <= a < pf_s1 v) ->
  ~ (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8) -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha H1 H2. apply (HKEEP a Ha).
  - rewrite Hsp, SCAT. replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by ring. exact H1.
  - intros (_ & Hq). exact (H2 Hq). }
pose proof (pb11a_after fx1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val S2 W2 regs2 mem2 md2
  (conj HB (conj HMID (conj HST (conj HVP (conj HINB (conj H70 (conj HRG HRA))))))) Hfx HJ2 HP2 H10 (HNT Hc0)
  HKP HPERM2 HS2) as HK2.
change (mkCfg (@mkst fx1 regs2 (w64 (BASE + PF_KRET)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at (fx := fx1) SEGS (BASE + PF_KRET) regs2 mem2 md2).
exact (pb11a_r2 (fx := fx1) n KLOOP v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d gi vp val HK2).
Qed.
End y.

Section z. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let pb11a_RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let pb11a_RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.

(* ---------- run 1: MISS (0x88a50) -> the call of reac_box_catalogue (0x88ad8) ---------- *)
(* every register its own atom, atom 32 = &ntok = F + 0x450; slot 0x80 read-only on s1's atom (its word names atom
   32), known's 30 cells and ntok's cell writable on s5's atom, ntok writable on atom 32 *)
Definition pb11a_regions1 : smem :=
  [YP09.mkRegion (Some 9%nat) 0x80 0x88 0 0 [YP09.mkChunk 0x80 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 21%nat) 100 130 100 130 [];
   YP09.mkRegion (Some 21%nat) 138 139 138 139 [];
   YP09.mkRegion (Some 32%nat) 0 8 0 8 []].
Definition pb11a_ss1 : sstate := mkSS PF_MISS sr_atoms pb11a_regions1 None (mkFacts [] [] []).
Lemma pb11a_seed1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_MISS B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)])) pb11a_ss1
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_MISS)) memc (seg_rom SEGS))).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HB & _ & _ & _ & _ & _ & _ & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (_ & _ & _ & HSL & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (pf_F v pos + PF_O_NTOK))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
pose proof STK_values as (_ & _ & _ & SPF0 & _).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb11_rg_get rX _ 9 _ HFI); pb11a_in).
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (pb11_rg_get rX _ 21 _ HRG); pb11a_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos + PF_O_NTOK)
  by (rewrite E32; unfold w64, PF_O_NTOK; apply unsigned_lit_small; lia).
assert (H80 : rdword (rdW Wc memc) (pf_s1 v + 0x80) = Some (pf_F v pos + PF_O_NTOK)).
{ exact (proj1 (Forall_forall _ _) HSL (0x80, pf_F v pos + PF_O_NTOK)
    ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
rewrite restrict_mkst_fx. unfold pb11a_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pb11a_regions1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0x80 8 (SOff 32 0) (pf_F v pos + PF_O_NTOK));
      [rewrite pb11a_den_atom0; exact E32 | unfold PF_O_NTOK; cbn; lia | cbn; lia|].
    exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ H80).
  + rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o0 Ho. apply (apresent_writable SEGS). apply Hshp. lia.
  + rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o0 Ho. apply (apresent_writable SEGS). apply Hshp. lia.
  + rewrite U32. split; [unfold PF_O_NTOK; lia|]. split; [unfold PF_O_NTOK; lia|]. split; [|constructor].
    intros o0 Ho. apply (apresent_writable SEGS). apply Hfp. unfold PF_O_NTOK in *. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region, pb11a_regions1.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PF_O_NTOK.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold kLowMemEnd, kHighShadowEnd in *.
  pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
  repeat split; lia.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* the head of B11b: MISS -> KLOOP pass 0 *)
Lemma pb11a_miss : forall n, HA_KLOOP B n 0 -> H_MISS B n.
Proof.
intros n KLOOP v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
pose proof (pb11a_seed1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI) as HS.
pose proof HI as (HB & HMID & HST & HVP & HINB & _ & H70 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSL & HFSH).
pose proof HFIb as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
set (E := Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (pf_F v pos + PF_O_NTOK))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (pb11_rg_get rX _ 21 _ HRG); pb11a_in).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos + PF_O_NTOK)
  by (rewrite E32; unfold w64, PF_O_NTOK; apply unsigned_lit_small; lia).
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
unfold cfg_at. change (w64 (BASE + PF_MISS)) with (Z_to_bv 64 (BASE + PF_MISS)).
(* 0x88a50 .. 0x88ad8: the 31 scope-in stores, s3 = &ntok, ntok = 0, a0 = s3, the call *)
paj_run_shc pb11a_RUNP pb11a_RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold pb11a_ss1, pb11a_regions1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | | |].
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    rewrite U21 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    rewrite U21 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5) with 2048. rewrite U32 in Ha. unfold PF_O_NTOK in Ha. lia. }
pb11a_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((pf_SH v pos + 100 <= a < pf_SH v pos + 130) \/ (pf_SH v pos + 138 <= a < pf_SH v pos + 139) \/
       (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8)) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem pb11a_ss1) (w_H Wc) memc (ms_mem ms)
    (fun a => (pf_SH v pos + 100 <= a < pf_SH v pos + 130) \/ (pf_SH v pos + 138 <= a < pf_SH v pos + 139) \/
       (pf_F v pos + PF_O_NTOK <= a < pf_F v pos + PF_O_NTOK + 8)) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21, ?U32 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2 end.
cbn [ms_mem restrict] in HR1, HR2.
assert (CK : forall i, pb11_kcell i -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0).
{ intros i [Hi | ->].
  - apply (pb11a_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR1 U21). revert i Hi.
    apply (pb11_zrange (fun i => pb11a_cell_ok _ i 0) 100 30). vm_compute. reflexivity.
  - apply (pb11a_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ 138 _ HR2 U21). vm_compute. reflexivity. }
(* the registers at the call *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pb11a_rreg HS; rewrite pb11a_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = w64 (BASE + PF_KRET)) by (pb11a_rreg HS; exact (codeptr_val _ _ HEI)).
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_NTOK))
  by (pb11a_rreg HS; rewrite pb11a_den_atom0; exact E32).
assert (Q19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (pf_F v pos + PF_O_NTOK))
  by (pb11a_rreg HS; rewrite pb11a_den_atom0; exact E32).
pmkst HS.
rewrite (SIGP SS_reac_box_catalogue ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_box_catalogue) with AF_reac_box_catalogue by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_reac_box_catalogue)) (ms_mem ms) (seg_rom SEGS)) mdv)
  with (cfg_at SEGS (BASE + AF_reac_box_catalogue) (ms_regs ms) (ms_mem ms) mdv).
(* the keep relation over B11b's write set *)
assert (KWs : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos false true true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply K1; [exact Ha|]. intros [Hq | [Hq | Hq]]; apply Hn.
  - right; right; right. split; [reflexivity|]. exists (a - pf_SH v pos). split; [left; lia | lia].
  - right; right; right. split; [reflexivity|]. exists (a - pf_SH v pos). split; [right; lia | lia].
  - right; right; left. split; [reflexivity|]. right. exact Hq. }
assert (KWt : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply KWs; [exact Ha|]. intros Hq. apply Hn. exact (pb11_Wrx_mono v pos _ _ _ a Hq). }
apply (pb11a_call n KLOOP v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val).
split.
{ apply (pb11_move (fx := fx) B fx v pos lyc Sc Wc rX memc mdc PF_SC_L146 Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_KNOWN HB HJ
    (ex_intro _ (st_fs Sc) (pb11a_set_fs_id Sc)) (Permutation_refl _) KWt M1).
  - unfold pf_rg, pb11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (pb11_rg_get rX _ _ _ HFI); pb11a_in | pb11a_in]).
  - exact (pb11_fill_fsh v pos _ _ false true G KWs CK HFSH).
  - exact HFRM. }
split; [exact HMID|].
split; [exact (pb11_keep_st B v pos lyc Sc Wc memc mdc Wc (ms_mem ms) G HAR Hin Hly KWt cf (Some gi) nm _ HC5 HST)|].
split; [exact (pb11_keep_buf_str v pos Wc memc Wc (ms_mem ms) G KWt vp val HINB HVP)|].
split; [exact HINB|].
split.
{ apply (pb11_keep_slots v pos _ _ true true true _ G KWt); [|exact H70].
  repeat constructor; cbn [fst]; lia. }
split.
{ unfold pf_rg, PF_RL, PF_RM in HRG |- *. cbn [app] in HRG |- *.
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [ rewrite QK; [apply (pb11_rg_get rX _ _ _ HRG); pb11a_in | pb11a_in] | exact Q19 | exact Q10 ]. }
apply (pb11a_bvr _ _ 1); [reflexivity | exact Q1].
Qed.
End z.

(* the head of B11b at every FP state *)
Theorem pb11a_head : forall (f0 : YK11.FPState) n, HA_KLOOP B n 0 -> H_MISS (fx := f0) B n.
Proof. intros f0 n K. exact (pb11a_miss (fx := f0) n K). Qed.

End d.
