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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 748 of its 817 lines of code are new or changed and 4984 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): one pass of segment B11b's join loop,
   KLOOP 0x88b14 (pass ti) -> the snprintf call 0x88b9c -> KLOOP (pass ti + 1) or KREFM 0x88bd0 (after pass 10).
   The B11b segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of reac_segconf_parse_file's
   image-B walk, the join loop of segment B11b: pb11p_pass).
   ADAPTED from the image-A G3 walk owner's image-A lane, on a working branch (pf_a11b_d.v's KLOOP) and the unit owner's UBSan
   walk on a working branch lib/U/Prog/pf_p7_miss.v (the trap tests of the same loop), re-derived on image B;
   the seed / run / region shape from this lane's own pf_seg_B11b_a.v (pb11a_r2, pb11a_call).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), pass ti (s3 = ti, s11 = kn = pb11_kn ti,
   s7 = s8 = catA + 296 ti, a4 = catA, a2 = 240; slots 0x60 = 0x68 = 1):
     0x88b14 bltu a2,s11 -> unimp (T23: 240 < kn; kn <= 77)
     0x88b18 beqz s3 -> a3 = "" (0x21860) at 0x88b28, else a3 = "|" (0x21840) at 0x88b1c
     0x88b30 a0 = 296 ti; a1 = tab + 296 ti; a2 = (a1 = 0); a5 = slot 0x68
     0x88b44 beq a5,a2 -> unimp (T24); 0x88b48 bltu a1,a4 -> unimp (T25: tab + 296 ti < tab)
     0x88b4c .. 0x88b60 mulh / srai / xor / snez; bnez -> unimp (T26: 296 ti overflows)
     0x88b64 a0 = slot 0x60; 0x88b68 beqz -> unimp (T27)
     0x88b6c .. 0x88b78 lbu of sh(tab + 296 ti); bnez -> 0x89234 errpath_load8 (B#28: the row's shadow byte is 0,
                        sa_cat's sa_pinned at the state's AR)
     0x88b7c s2 = tab; 0x88b80 a4 = ld 0(s8) = tab[ti].token (sa_cat's row word); a0 = slot 0x78 + kn;
             a1 = 240 - kn; a2 = "%s%s" (0x21820)
     0x88b9c jal wrapper_snprintf   (pf_seg_B11b_s.v pb11_snp, from this pc)
     0x88ba0 a2 = 240; a1 = ld 128(s1) (&ntok); a1 = ld 0(a1) (= 11); s3 = ti + 1; a4 = s2; s2 = '#'
     0x88bb8 bgeu s3,a1 -> KREFM 0x88bd0 (taken iff ti = 10)
     0x88bbc s11 = kn + a0 (a0 = |T|); a0 = s11 + 2; s7 += 296; s8 += 296
     0x88bcc bltu a0,a2 -> KLOOP 0x88b14 (taken: kn (S ti) + 2 <= 79 < 240)
   THE PROOF: every trap test and every branch is decided by computation, so ti is concrete in each run: the pass is
   proved by eleven instances of two runs. Run 1 (pb11p_ss1, KLOOP -> KSNP) carries the two trap flags and known's
   base as read-only chunks on s1's atom, the catalogue row's word as an absolute region whose chunk names the token
   pointer, and the row's shadow byte as an absolute 1-byte region (0, from sa_cat's sa_pinned at the state's AR:
   pb11p_shadow0). It writes nothing. pb11_snp takes the call; pb11p_after rebuilds INV_KSRET at the FP state the
   wrapper returns and hands it to pb11p_r2, whose run 2 (pb11p_ss2, KSRET -> KLOOP or KREFM) re-reads ntok through
   slot 0x80 and writes nothing either.
   SECTION HYPOTHESES: ASNPRINTF (pf_pieces.v's for B11b, as pf_seg_B11b_s.v); OBJ (the listing's seg_val_objs over
   the walk's abstract PAImg instance, B's SegObj.v, as reac_segconf_parse.v takes it: the auipc/addi literal
   atoms are the image's .rodata addresses). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B11b_d pf_seg_B11b_f pf_seg_B11b_k pf_seg_B11b_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B11b_a.v) ---------- *)
Lemma pb11p_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pb11p_set_fs_id : forall s, s = set_fs (st_fs s) s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma pb11p_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v ->
  getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac pb11p_in := solve [unfold PF_RL, PF_RM, pb11_FI; cbn [In app]; repeat first [left; reflexivity | right]].
Ltac pb11p_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pb11p_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* a literal register value the run leaves: the numbers agree by computation *)
Ltac pb11p_lit := cbn [sv_denot]; unfold w64; f_equal; vm_compute; reflexivity.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the reader wraps addresses modulo 2^64 (mbyte reads Z_to_bv 64 a) *)
Lemma pb11p_aview_mod : forall H m a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma pb11p_val_mem_of_sa_val : forall H m a v (n : nat),
  sa_val (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a v n HS k Hk. specialize (HS k Hk). unfold aview in HS.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in HS. injection HS as Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small; [exact Hb|].
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* an auipc / addi literal: the listing's object atom is the image's address (OBJ) *)
Lemma pb11p_obj : forall (E : env) (k : nat) (off : Z), img_env VAL A_LIM E ->
  (k < length seg_objs)%nat -> (A_OBJ k < A_LIM)%nat ->
  sv_denot E (SOff (A_OBJ k) off) = w64 (nth k seg_objs 0 + off).
Proof.
intros E k off HE Hk Hl. cbn [sv_denot].
rewrite (HE (A_OBJ k) ltac:(unfold A_OBJ, A_TEXT in *; lia)). rewrite (OBJ k Hk). reflexivity.
Qed.
Ltac pb11p_objd HEI :=
  lazymatch goal with
  | |- context [sv_denot ?E (SOff ?a ?off)] =>
      let i := eval vm_compute in (a - 241)%nat in
      change a with (A_OBJ i);
      rewrite (pb11p_obj E i off HEI ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)
                 ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))
  end.

(* the catalogue row of pass ti: 8-aligned, so its shadow byte is 0 (saddr_ok at the granule's last byte) *)
Lemma pb11p_shadow0 : forall ly S (W : world SEGS) mem md ti, (ti < 11)%nat ->
  AR SEGS B ly S W mem md -> sa_cat SEGS B (rdW W mem) catA ->
  rdW W mem (SHADOW_OFF + pin_spec.row_addr catA ti / 8) = Some 0.
Proof.
intros ly S W mem md ti Hti HAR HCAT.
destruct HCAT as (Hpin & _ & _).
destruct (Hpin ly S W mem md HAR) as (_ & _ & _ & HRA & _).
pose proof (Nat2Z.is_nonneg ti) as Hn0. assert (HN : Z.of_nat ti <= 10) by lia.
assert (ER : pin_spec.row_addr catA ti = 8 * (82964 + 37 * Z.of_nat ti))
  by (unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA; lia).
assert (ED2 : pin_spec.row_addr catA ti / 8 = 82964 + 37 * Z.of_nat ti).
{ rewrite ER. replace (8 * (82964 + 37 * Z.of_nat ti)) with ((82964 + 37 * Z.of_nat ti) * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (ED : (pin_spec.row_addr catA ti + 7) / 8 = 82964 + 37 * Z.of_nat ti).
{ rewrite ER. replace (8 * (82964 + 37 * Z.of_nat ti) + 7) with ((82964 + 37 * Z.of_nat ti) * 8 + 7) by lia.
  rewrite Z.div_add_l by lia. lia. }
assert (EM : (pin_spec.row_addr catA ti + 7) mod 8 = 7).
{ rewrite ER. replace (8 * (82964 + 37 * Z.of_nat ti) + 7) with (7 + (82964 + 37 * Z.of_nat ti) * 8) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
destruct (HRA (pin_spec.row_addr catA ti + 7)
  ltac:(unfold pin_spec.CAT_BYTES; rewrite ER; unfold catA; lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs. rewrite ED in Hs. rewrite ED2.
unfold saddr_ok in Hok. rewrite EM in Hok.
destruct Hok as [-> | Hc]; [exact Hs | lia].
Qed.

(** ** The cut at the return of the snprintf call (KSRET, 0x88ba0), after pass ti: known holds the join of the
    first ti + 1 tokens and its NUL, ntok still 11, s2 = catA (borrowed at 0x88b7c), a0 = |T| (the call's answer) *)
Section inv. Context {fx : YK11.FPState}.
Definition INV_KSRET (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (dd : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (ti : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln dd n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  (ti < 11)%nat /\
  sa_zs (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) (pb11_J (S ti) ++ [0]) /\
  sa_val (rdW Wc memc) (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x60, 1); (0x68, 1); (0x70, vp)] /\
  pf_rg rX ([(21, pf_SH v pos); (26, -1)] ++ PF_RM v o ln ++
            [(18, catA); (19, Z.of_nat ti); (27, pb11_kn ti); (23, pin_spec.row_addr catA ti);
             (24, pin_spec.row_addr catA ti); (10, Z.of_nat (length (pb11_text ti)))]).
End inv.

(* ---------- the two seeds ---------- *)
(* run 1, KLOOP: the two trap flags and known's base on s1's atom (read-only), the row's word and its shadow byte
   as absolute regions; atom 32 = the token pointer, atom 33 = known *)
Definition pb11p_regions1 (ti : nat) : smem :=
  [YP09.mkRegion (Some 9%nat) 0x60 0x80 0 0
     [YP09.mkChunk 0x60 (CVal 8 (SLit 1)); YP09.mkChunk 0x68 (CVal 8 (SLit 1));
      YP09.mkChunk 0x78 (CVal 8 (SOff 33 0))];
   YP09.mkRegion None (pin_spec.row_addr catA ti) (pin_spec.row_addr catA ti + 8) 0 0
     [YP09.mkChunk (pin_spec.row_addr catA ti) (CVal 8 (SOff 32 0))];
   YP09.mkRegion None (SHADOW_OFF + pin_spec.row_addr catA ti / 8)
     (SHADOW_OFF + pin_spec.row_addr catA ti / 8 + 1) 0 0
     [YP09.mkChunk (SHADOW_OFF + pin_spec.row_addr catA ti / 8) (CVal 1 (SLit 0))]].
Definition pb11p_ss1 (ti : nat) : sstate :=
  mkSS PF_KLOOP
    (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
      (Z_to_bv 5 19) (SLit (Z.of_nat ti)))
      (Z_to_bv 5 27) (SLit (pb11_kn ti)))
      (Z_to_bv 5 23) (SLit (pin_spec.row_addr catA ti)))
      (Z_to_bv 5 24) (SLit (pin_spec.row_addr catA ti)))
      (Z_to_bv 5 14) (SLit catA))
      (Z_to_bv 5 12) (SLit 240))
      (Z_to_bv 5 20) (SLit SHADOW_OFF))
    (pb11p_regions1 ti) None (mkFacts [] [] []).
(* run 2, KSRET: slot 0x80 (&ntok) on s1's atom and ntok on atom 32 *)
Definition pb11p_regions2 : smem :=
  [YP09.mkRegion (Some 9%nat) 0x80 0x88 0 0 [YP09.mkChunk 0x80 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 11))]].
Definition pb11p_ss2 (ti : nat) : sstate :=
  mkSS PF_KSRET
    (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
      (Z_to_bv 5 19) (SLit (Z.of_nat ti)))
      (Z_to_bv 5 27) (SLit (pb11_kn ti)))
      (Z_to_bv 5 23) (SLit (pin_spec.row_addr catA ti)))
      (Z_to_bv 5 24) (SLit (pin_spec.row_addr catA ti)))
      (Z_to_bv 5 18) (SLit catA))
      (Z_to_bv 5 10) (SLit (Z.of_nat (length (pb11_text ti)))))
    pb11p_regions2 None (mkFacts [] [] []).

Section w. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let pb11p_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

Lemma pb11p_seed2 : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val,
  INV_KSRET n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val ti ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)])) (pb11p_ss2 ti)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KSRET)) memc (seg_rom SEGS))).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val HI.
destruct HI as (HB & _ & _ & _ & _ & Hti & _ & HNT & _ & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (_ & _ & _ & HSL & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Nat2Z.is_nonneg ti) as Hn0.
assert (Hkn : 0 <= pb11_kn ti <= 77) by (apply pb11_kn_bound; lia).
set (E := Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (pf_F v pos + PF_O_NTOK))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos + PF_O_NTOK)
  by (rewrite E32; unfold w64, PF_O_NTOK; apply unsigned_lit_small; lia).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb11_rg_get rX _ 9 _ HFI); pb11p_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (S80 : rdword (rdW Wc memc) (pf_s1 v + 0x80) = Some (pf_F v pos + PF_O_NTOK)).
{ exact (proj1 (Forall_forall _ _) HSL (0x80, pf_F v pos + PF_O_NTOK)
    ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL E (mkSS PF_KSRET sr_atoms pb11p_regions2 None (mkFacts [] [] []))
  (mkst rX (Z_to_bv 64 (BASE + PF_KSRET)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pb11p_regions2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0x80 8 (SOff 32 0) (pf_F v pos + PF_O_NTOK));
        [rewrite pb11p_den_atom0; exact E32 | unfold PF_O_NTOK; cbn; lia | cbn; lia|].
      exact (val_mem_of_rdword SEGS _ _ _ _ S80).
    + rewrite U32. split; [unfold PF_O_NTOK; lia|]. split; [unfold PF_O_NTOK; lia|].
      split; [intros oo Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SLit 11) 11); [reflexivity | cbn; lia | cbn; lia|].
      rewrite Z.add_0_r. apply pb11p_val_mem_of_sa_val. exact HNT.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, pb11p_regions2.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PF_O_NTOK.
    repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (Z.of_nat ti)) by (apply (pb11_rg_get rX _ 19 _ HRG); pb11p_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pb11_kn ti)) by (apply (pb11_rg_get rX _ 27 _ HRG); pb11p_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (pin_spec.row_addr catA ti))
  by (apply (pb11_rg_get rX _ 23 _ HRG); pb11p_in).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 (pin_spec.row_addr catA ti))
  by (apply (pb11_rg_get rX _ 24 _ HRG); pb11p_in).
assert (R18 : getr rX (Z_to_bv 5 18) = w64 catA) by (apply (pb11_rg_get rX _ 18 _ HRG); pb11p_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat (length (pb11_text ti))))
  by (apply (pb11_rg_get rX _ 10 _ HRG); pb11p_in).
exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 10) (Z.of_nat (length (pb11_text ti)))
        (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 18) catA
          (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 24) (pin_spec.row_addr catA ti)
            (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 23) (pin_spec.row_addr catA ti)
              (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 27) (pb11_kn ti)
                (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 19) (Z.of_nat ti) HS0 R19 eq_refl)
                R27 eq_refl) R23 eq_refl) R24 eq_refl) R18 eq_refl) R10 eq_refl).
Qed.

(* ---------- the cut run 2 reaches ---------- *)
Lemma pb11p_mk_kloop : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val rY memY mdY,
  INV_KSRET n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val ti ->
  (ti < 10)%nat ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memY mdY 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memY a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memY a <> None) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 26; 25; 22] -> getr rY (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rY (Z_to_bv 5 18) = w64 0x23 ->
  getr rY (Z_to_bv 5 19) = w64 (Z.of_nat (S ti)) ->
  getr rY (Z_to_bv 5 27) = w64 (pb11_kn (S ti)) ->
  getr rY (Z_to_bv 5 23) = w64 (pin_spec.row_addr catA (S ti)) ->
  getr rY (Z_to_bv 5 24) = w64 (pin_spec.row_addr catA (S ti)) ->
  getr rY (Z_to_bv 5 14) = w64 catA ->
  getr rY (Z_to_bv 5 12) = w64 240 ->
  INV_KLOOP B n v pos lyc Sc Wc rY memY mdY cf nm o ln dd gi vp val (S ti).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val rY memY mdY HI Hlt HJ K M QK Q18 Q19 Q27 Q23 Q24
  Q14 Q12.
destruct HI as (HB & HMID & HST & HVP & HINB & Hti & HKM & HNT & HSL3 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSLp & HFSH).
pose proof HFIb as (_ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (KWt : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rdW Wc memY a = rdW Wc memc a)
  by (intros a Ha _; exact (K a Ha)).
assert (KWs : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos false true false a -> rdW Wc memY a = rdW Wc memc a)
  by (intros a Ha _; exact (K a Ha)).
assert (Hknb : 0 <= pb11_kn (S ti) <= 77) by (apply pb11_kn_bound; lia).
split.
{ apply (pb11_move B fx v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN Sc Wc rY memY mdY PF_SC_KNOWN HB HJ
    (ex_intro _ (st_fs Sc) (pb11p_set_fs_id Sc)) (Permutation_refl _) KWt M).
  - unfold pf_rg, pb11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (pb11_rg_get rX _ _ _ HFI); pb11p_in | pb11p_in]).
  - exact (pb11_keep_fsh v pos _ _ false true PF_SC_KNOWN G KWs HFSH).
  - exact HFRM. }
split; [exact HMID|].
split; [exact (pb11_keep_st B v pos lyc Sc Wc memc mdc Wc memY G HAR Hin Hly KWt cf (Some gi) nm _ HC5 HST)|].
split; [exact (pb11_keep_buf_str v pos Wc memc Wc memY G KWt vp val HINB HVP)|].
split; [exact HINB|].
split; [lia|].
split.
{ cbn [pb11_kmem]. intros i Hi.
  assert (HiB : Z.of_nat i <= 78).
  { rewrite length_app in Hi. cbn [length] in Hi.
    pose proof Hknb as Hb. unfold pb11_kn in Hb. lia. }
  rewrite (K (pf_F v pos + PF_O_KNOWN + Z.of_nat i) ltac:(unfold PF_O_KNOWN; lia)).
  exact (HKM i Hi). }
split.
{ intros k Hk. rewrite (K (pf_F v pos + PF_O_NTOK + Z.of_nat k) ltac:(unfold PF_O_NTOK; lia)).
  exact (HNT k Hk). }
split.
{ apply (pb11_keep_slots v pos _ _ false true false _ G KWs); [|exact HSL3].
  repeat constructor; cbn [fst]; lia. }
unfold pf_rg, PF_RL, PF_RM. cbn [app].
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [ exact Q18 | exact Q19 | exact Q27 | exact Q23 | exact Q24 | exact Q14 | exact Q12
        | rewrite QK; [apply (pb11_rg_get rX _ _ _ HRG); pb11p_in | pb11p_in] ].
Qed.

Lemma pb11p_mk_krefm : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val rY memY mdY,
  INV_KSRET n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val 10 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memY mdY 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memY a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memY a <> None) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 26; 25; 22] -> getr rY (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rY (Z_to_bv 5 18) = w64 0x23 ->
  INV_KREFM B n v pos lyc Sc Wc rY memY mdY cf nm o ln dd gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val rY memY mdY HI HJ K M QK Q18.
destruct HI as (HB & HMID & HST & HVP & HINB & Hti & HKM & HNT & HSL3 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSLp & HFSH).
pose proof HFIb as (_ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (KWt : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a -> rdW Wc memY a = rdW Wc memc a)
  by (intros a Ha _; exact (K a Ha)).
assert (KWs : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos false true false a -> rdW Wc memY a = rdW Wc memc a)
  by (intros a Ha _; exact (K a Ha)).
assert (HF8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk.
  replace (k * 32) with ((4 * k) * 8) by lia. apply Z_mod_mult. }
split.
{ apply (pb11_move B fx v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN Sc Wc rY memY mdY PF_SC_KNOWN HB HJ
    (ex_intro _ (st_fs Sc) (pb11p_set_fs_id Sc)) (Permutation_refl _) KWt M).
  - unfold pf_rg, pb11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (pb11_rg_get rX _ _ _ HFI); pb11p_in | pb11p_in]).
  - exact (pb11_keep_fsh v pos _ _ false true PF_SC_KNOWN G KWs HFSH).
  - exact HFRM. }
split; [exact HMID|].
split; [exact (pb11_keep_st B v pos lyc Sc Wc memc mdc Wc memY G HAR Hin Hly KWt cf (Some gi) nm _ HC5 HST)|].
split; [exact (pb11_keep_buf_str v pos Wc memc Wc memY G KWt vp val HINB HVP)|].
split; [exact HINB|].
split.
{ split.
  - split; [|exact pb11_known_nulfree].
    intros i Hi. rewrite pb11_J_11 in HKM.
    assert (HiB : Z.of_nat i <= 78).
    { rewrite length_app in Hi. cbn [length] in Hi. rewrite pb11_known_len in Hi. lia. }
    rewrite (K (pf_F v pos + PF_O_KNOWN + Z.of_nat i) ltac:(unfold PF_O_KNOWN; lia)). exact (HKM i Hi).
  - intros x Hx. rewrite pb11_known_len in Hx. replace (Z.of_nat 77%nat) with 77 in Hx by reflexivity.
    assert (EM : (pf_F v pos + PF_O_KNOWN + 77) mod 8 = 5) by (unfold PF_O_KNOWN; lia).
    rewrite EM in Hx.
    rewrite (K x ltac:(unfold PF_O_KNOWN in *; lia)).
    apply (aview_some_of_apresent SEGS). apply Hfp. unfold PF_O_KNOWN in *. lia. }
split.
{ apply (pb11_keep_slots v pos _ _ false true false _ G KWs); [|].
  - repeat constructor; cbn [fst]; lia.
  - unfold pf_sl in HSL3 |- *. apply Forall_inv_tail in HSL3. apply Forall_inv_tail in HSL3. exact HSL3. }
unfold pf_rg, PF_RL, PF_RM. cbn [app].
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [ exact Q18 | rewrite QK; [apply (pb11_rg_get rX _ _ _ HRG); pb11p_in | pb11p_in] ].
Qed.

(* ---------- run 2: KSRET (0x88ba0) -> KLOOP (pass ti + 1) or KREFM ---------- *)
Ltac pb11p_run2_pre HS :=
  intros a (r & Hr & Ha); unfold pb11p_ss2, pb11p_regions2 in Hr; cbn [ss_mem In] in Hr;
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.

Lemma pb11p_r2 : forall n ti, (ti < 11)%nat ->
  ((ti < 10)%nat -> HA_KLOOP B n (S ti)) -> HA_KREFM B n ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val,
  INV_KSRET n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val ti ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KSRET) rX memc mdc) (PB11_POST B v cf gi nm val o ln).
Proof.
intros n ti Hti KL KR v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val HI.
pose proof HI as HI0.
destruct HI as (HB & HMID & HST & HVP & HINB & _ & HKM & HNT & HSL3 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSLp & HFSH).
pose proof HFIb as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg rX [w64 (pf_F v pos + PF_O_NTOK)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at. change (w64 (BASE + PF_KSRET)) with (Z_to_bv 64 (BASE + PF_KSRET)).
do 10 (destruct ti as [|ti];
  [ pose proof (pb11p_seed2 n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val HI0) as HS;
    fold E in HS;
    paj_run_to_sh pb11p_RUNTO HS HJ PF_KLOOP;
    [ pb11p_run2_pre HS
    | cbn [ms_mem mkst] in HFr, HG, HF; pb11p_clear_md;
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a);
      [ intros a Ha;
        apply (kept_of_frame (segs:=SEGS) E (ss_mem (pb11p_ss2 _)) (w_H Wc) memc (ms_mem ms)
                 (fun _ => False) HFr); [| exact Ha | intros HFx; exact HFx];
        intros b wlo whi a' Hin' Hrr; vm_compute in Hin'; cbv beta;
        repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin'
      | assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
          by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv));
        assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 21; 26; 25; 22] ->
            getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r));
        [ intros r Hr; cbn [In] in Hr;
          repeat (destruct Hr as [<- | Hr];
            [pb11p_rreg HS; rewrite pb11p_den_atom0; apply EE; reflexivity |]); destruct Hr
        | pmkst HS;
          lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
            change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
              with (cfg_at SEGS (BASE + PF_KLOOP) rg mm mdx) end;
          apply (KL ltac:(lia) fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln dd gi vp val);
          apply (pb11p_mk_kloop n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val
                   (ms_regs ms) (ms_mem ms) mdv HI0 ltac:(lia) HJ K1 M1 QK);
          solve [ pb11p_rreg HS; pb11p_lit ] ] ] ]
  | ]).
destruct ti as [|ti]; [| exfalso; lia].
pose proof (pb11p_seed2 n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val HI0) as HS.
fold E in HS.
paj_run_to_sh pb11p_RUNTO HS HJ PF_KREFM.
{ pb11p_run2_pre HS. }
cbn [ms_mem mkst] in HFr, HG, HF. pb11p_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha.
  apply (kept_of_frame (segs:=SEGS) E (ss_mem (pb11p_ss2 10)) (w_H Wc) memc (ms_mem ms)
           (fun _ => False) HFr); [| exact Ha | intros HFx; exact HFx].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pb11p_rreg HS; rewrite pb11p_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
    with (cfg_at SEGS (BASE + PF_KREFM) rg mm mdx) end.
apply (KR fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln dd gi vp val).
apply (pb11p_mk_krefm n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val
         (ms_regs ms) (ms_mem ms) mdv HI0 HJ K1 M1 QK).
pb11p_rreg HS. pb11p_lit.
Qed.
End w.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let pb11p_RUNTO1 := SRr_run_to_pi_AJ (fx := fx) B LAWS.

Lemma pb11p_seed1 : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val tp,
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val ti ->
  regions_wf (pb11p_regions1 ti) = true ->
  0 <= tp < 2 ^ 64 ->
  rdword (rdW Wc memc) (pin_spec.row_addr catA ti) = Some tp ->
  rdW Wc memc (SHADOW_OFF + pin_spec.row_addr catA ti / 8) = Some 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 tp; w64 (pf_F v pos + PF_O_KNOWN)])) (pb11p_ss1 ti)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KLOOP)) memc (seg_rom SEGS))).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val tp HI HWF Htpb HROW HSH.
destruct HI as (HB & _ & _ & _ & _ & Hti & _ & _ & HSL3 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (_ & _ & _ & HSL & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Nat2Z.is_nonneg ti) as Hn0. assert (HN : Z.of_nat ti <= 10) by lia.
assert (Hkn : 0 <= pb11_kn ti <= 77) by (apply pb11_kn_bound; lia).
assert (ER : pin_spec.row_addr catA ti = 8 * (82964 + 37 * Z.of_nat ti))
  by (unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA; lia).
assert (ED2 : pin_spec.row_addr catA ti / 8 = 82964 + 37 * Z.of_nat ti).
{ rewrite ER. replace (8 * (82964 + 37 * Z.of_nat ti)) with ((82964 + 37 * Z.of_nat ti) * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
set (E := Eimg (Ereg rX [w64 tp; w64 (pf_F v pos + PF_O_KNOWN)])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 tp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 (pf_F v pos + PF_O_KNOWN))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb11_rg_get rX _ 9 _ HFI); pb11p_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (S60 : rdword (rdW Wc memc) (pf_s1 v + 0x60) = Some 1)
  by (exact (proj1 (Forall_forall _ _) HSL3 (0x60, 1) ltac:(cbn [In]; tauto))).
assert (S68 : rdword (rdW Wc memc) (pf_s1 v + 0x68) = Some 1)
  by (exact (proj1 (Forall_forall _ _) HSL3 (0x68, 1) ltac:(cbn [In]; tauto))).
assert (S78 : rdword (rdW Wc memc) (pf_s1 v + 0x78) = Some (pf_F v pos + PF_O_KNOWN)).
{ exact (proj1 (Forall_forall _ _) HSL (0x78, pf_F v pos + PF_O_KNOWN)
    ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
assert (SV1 : sa_val (rdW Wc memc) (SHADOW_OFF + pin_spec.row_addr catA ti / 8) 1%nat 0).
{ intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
  replace (Z.of_nat 0%nat) with 0 by reflexivity. rewrite Z.add_0_r.
  replace (le_byte 0 1 0%nat) with 0 by (vm_compute; reflexivity). exact HSH. }
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL E (mkSS PF_KLOOP sr_atoms (pb11p_regions1 ti) None (mkFacts [] [] []))
  (mkst rX (Z_to_bv 64 (BASE + PF_KLOOP)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - exact HWF.
  - unfold pb11p_regions1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0x60 8 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia|].
        exact (val_mem_of_rdword SEGS _ _ _ _ S60).
      * apply (chunk_ok_val SEGS E _ _ 0x68 8 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia|].
        exact (val_mem_of_rdword SEGS _ _ _ _ S68).
      * apply (chunk_ok_val SEGS E _ _ 0x78 8 (SOff 33 0) (pf_F v pos + PF_O_KNOWN));
          [rewrite pb11p_den_atom0; exact E33 | unfold PF_O_KNOWN; cbn; lia | cbn; lia|].
        exact (val_mem_of_rdword SEGS _ _ _ _ S78).
    + split; [lia|]. split; [rewrite ER; lia|]. split; [intros oo Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ (pin_spec.row_addr catA ti) 8 (SOff 32 0) tp);
        [rewrite pb11p_den_atom0; exact E32 | cbn; lia | cbn; lia|].
      exact (val_mem_of_rdword SEGS _ _ _ _ HROW).
    + split; [rewrite ED2; unfold SHADOW_OFF; lia|]. split; [rewrite ED2; unfold SHADOW_OFF; lia|].
      split; [intros oo Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ (SHADOW_OFF + pin_spec.row_addr catA ti / 8) 1 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia|].
      apply pb11p_val_mem_of_sa_val. exact SV1.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, pb11p_regions1.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite ED2, ER. unfold SHADOW_OFF. repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (Z.of_nat ti)) by (apply (pb11_rg_get rX _ 19 _ HRG); pb11p_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pb11_kn ti)) by (apply (pb11_rg_get rX _ 27 _ HRG); pb11p_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (pin_spec.row_addr catA ti))
  by (apply (pb11_rg_get rX _ 23 _ HRG); pb11p_in).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 (pin_spec.row_addr catA ti))
  by (apply (pb11_rg_get rX _ 24 _ HRG); pb11p_in).
assert (R14 : getr rX (Z_to_bv 5 14) = w64 catA) by (apply (pb11_rg_get rX _ 14 _ HRG); pb11p_in).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 240) by (apply (pb11_rg_get rX _ 12 _ HRG); pb11p_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (pb11_rg_get rX _ 20 _ HFI); pb11p_in).
exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 20) SHADOW_OFF
        (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 12) 240
          (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 14) catA
            (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 24) (pin_spec.row_addr catA ti)
              (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 23) (pin_spec.row_addr catA ti)
                (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 27) (pb11_kn ti)
                  (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 19) (Z.of_nat ti) HS0 R19 eq_refl)
                  R27 eq_refl) R23 eq_refl) R24 eq_refl) R14 eq_refl) R12 eq_refl) R20 eq_refl).
Qed.

(* the state the wrapper returns to (0x88ba0): INV_KSRET, and from it the rest of the pass *)
Lemma pb11p_after : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val rS,
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val ti ->
  (ti < 11)%nat ->
  ((ti < 10)%nat -> HA_KLOOP B n (S ti)) -> HA_KREFM B n ->
  pf_rg rS (pb11_FI B v) ->
  pf_rg rS ([(21, pf_SH v pos); (26, -1)] ++ PF_RM v o ln ++
            [(18, catA); (19, Z.of_nat ti); (27, pb11_kn ti); (23, pin_spec.row_addr catA ti);
             (24, pin_spec.row_addr catA ti)]) ->
  forall (f1 : YK11.FPState) regs2 mem2 md2, fxrel fx f1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem2 md2 0 ->
  aregs_preserved rS regs2 ->
  getr regs2 10 = w64 (Z.of_nat (length (pb11_text ti))) ->
  sa_zs (rdW Wc mem2) (pf_F v pos + PF_O_KNOWN + pb11_kn ti) (pb11_text ti ++ [0]) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) ->
     ~ (pf_F v pos + PF_O_KNOWN + pb11_kn ti <= a <
        pf_F v pos + PF_O_KNOWN + pb11_kn ti + Z.of_nat (length (pb11_text ti)) + 1) ->
     rdW Wc mem2 a = rdW Wc memc a) ->
  SRr SEGS Wc (mkCfg (@mkst f1 regs2 (w64 (BASE + PF_KSRET)) mem2 (seg_rom SEGS)) md2)
    (PB11_POST (fx := f1) B v cf gi nm val o ln).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val rS HI Hti KL KR HFIr HRLr
  f1 regs2 mem2 md2 Hfx HJ2 HP2 HA0 HBY HK2.
destruct HI as (HB & HMID & HST & HVP & HINB & _ & HKM & HNT & HSL3 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSLp & HFSH).
pose proof HFIb as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (Hti10 : (ti <= 10)%nat) by lia.
assert (Hkn : 0 <= pb11_kn ti <= 77) by (apply pb11_kn_bound; lia).
assert (HTl : 5 <= Z.of_nat (length (pb11_text ti)) <= 12).
{ unfold pb11_text. rewrite length_app. pose proof (pb11_sep_len ti). pose proof (pb11_tok_len ti Hti10). lia. }
assert (HKsnp : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
rewrite HKsnp in HK2.
(* what the call kept: everything off its window and off the bytes it wrote *)
assert (KWs : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos false true false a ->
    rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. apply (HK2 a Ha).
  - intros Hq. apply Hn. left. rewrite SPF. unfold PF_O_KNOWN in *. lia.
  - intros Hq. apply Hn. right; right; left. split; [reflexivity|]. left. unfold PF_O_KNOWN in *. lia. }
assert (KWt : forall a, 0 <= a < 2 ^ 64 -> ~ pb11_Wrx v pos true true true a ->
    rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. apply KWs; [exact Ha|]. intros Hq. apply Hn. exact (pb11_Wrx_mono v pos _ _ _ a Hq). }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite SPF in Hpres2.
assert (VIS : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ intros a0 Hv0. rewrite pb11p_aview_mod in Hv0 |- *.
  set (a := a0 mod 2 ^ 64) in *.
  assert (Ha : 0 <= a < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  clearbody a.
  destruct (Z_lt_le_dec a (pf_sp0 v - 12832)) as [L1 | L1];
  [|destruct (Z_lt_le_dec a (pf_sp0 v)) as [L2 | L2]].
  - destruct (Z_lt_le_dec a (pf_F v pos + PF_O_KNOWN + pb11_kn ti)) as [L3 | L3];
    [|destruct (Z_lt_le_dec a (pf_F v pos + PF_O_KNOWN + pb11_kn ti +
                               Z.of_nat (length (pb11_text ti)) + 1)) as [L4 | L4]].
    + rewrite (HK2 a Ha ltac:(lia) ltac:(lia)). exact Hv0.
    + replace a with (pf_F v pos + PF_O_KNOWN + pb11_kn ti +
        Z.of_nat (Z.to_nat (a - (pf_F v pos + PF_O_KNOWN + pb11_kn ti)))) by lia.
      rewrite (HBY (Z.to_nat (a - (pf_F v pos + PF_O_KNOWN + pb11_kn ti)))
        ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + rewrite (HK2 a Ha ltac:(lia) ltac:(lia)). exact Hv0.
  - apply (aview_some_of_apresent SEGS). apply Hpres2. lia.
  - rewrite (HK2 a Ha ltac:(lia) ltac:(unfold PF_O_KNOWN in *; lia)). exact Hv0. }
(* the join so far: the old bytes kept, the new ones from the call *)
assert (HJS : pb11_J (S ti) = pb11_J ti ++ pb11_text ti).
{ rewrite (pb11_J_step ti Hti10). unfold pb11_text. rewrite (pb11_fmt_ss ti Hti10). reflexivity. }
assert (HLJ : Z.of_nat (length (pb11_J ti)) = pb11_kn ti) by reflexivity.
assert (HOLD : forall i, (i < length (pb11_J ti))%nat ->
    rdW Wc memc (pf_F v pos + PF_O_KNOWN + Z.of_nat i) = Some (nth i (pb11_J ti) 0)).
{ clear HJS. destruct ti as [|t]; cbn [pb11_kmem] in HKM.
  - intros i Hi. vm_compute in Hi. lia.
  - intros i Hi. specialize (HKM i ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth1 in HKM by lia. exact HKM. }
assert (HKNEW : sa_zs (rdW Wc mem2) (pf_F v pos + PF_O_KNOWN) (pb11_J (S ti) ++ [0])).
{ intros i Hi. rewrite HJS, <- app_assoc in Hi |- *.
  destruct (Nat.lt_ge_cases i (length (pb11_J ti))) as [Hlt | Hge].
  - rewrite app_nth1 by lia.
    rewrite (HK2 (pf_F v pos + PF_O_KNOWN + Z.of_nat i) ltac:(unfold PF_O_KNOWN; lia)
      ltac:(unfold PF_O_KNOWN; lia) ltac:(unfold PF_O_KNOWN; lia)).
    exact (HOLD i Hlt).
  - rewrite app_nth2 by lia. rewrite length_app in Hi.
    specialize (HBY (i - length (pb11_J ti))%nat ltac:(lia)).
    replace (pf_F v pos + PF_O_KNOWN + Z.of_nat i)
      with (pf_F v pos + PF_O_KNOWN + pb11_kn ti + Z.of_nat (i - length (pb11_J ti))) by lia.
    exact HBY. }
assert (HKS : INV_KSRET (fx := f1) n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln dd gi vp val ti).
{ split.
  { apply (pb11_move B f1 v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN Sc Wc regs2 mem2 md2 PF_SC_KNOWN HB HJ2
      (ex_intro _ (st_fs Sc) (pb11p_set_fs_id Sc)) (Permutation_refl _) KWt VIS).
    - exact (pb11_rg_pres rS regs2 (pb11_FI B v) HP2 (pb11_FI_cs B v) HFIr).
    - exact (pb11_keep_fsh v pos _ _ false true PF_SC_KNOWN G KWs HFSH).
    - exact (fxrel_frm0 fx f1 HFRM Hfx). }
  split; [exact HMID|].
  split; [exact (pb11_keep_st B v pos lyc Sc Wc memc mdc Wc mem2 G HAR Hin Hly KWt cf (Some gi) nm _ HC5 HST)|].
  split; [exact (pb11_keep_buf_str v pos Wc memc Wc mem2 G KWt vp val HINB HVP)|].
  split; [exact HINB|].
  split; [lia|].
  split; [exact HKNEW|].
  split.
  { intros k Hk.
    rewrite (HK2 (pf_F v pos + PF_O_NTOK + Z.of_nat k) ltac:(unfold PF_O_NTOK; lia)
      ltac:(unfold PF_O_NTOK; lia) ltac:(unfold PF_O_KNOWN, PF_O_NTOK; lia)).
    exact (HNT k Hk). }
  split.
  { apply (pb11_keep_slots v pos _ _ false true false _ G KWs); [|exact HSL3].
    repeat constructor; cbn [fst]; lia. }
  unfold pf_rg, PF_RM. cbn [app].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [ rewrite HP2 by (unfold acallee_saved; lia); apply (pb11_rg_get rS _ _ _ HRLr); pb11p_in
          | replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact HA0 ]. }
exact (pb11p_r2 (fx := f1) n ti Hti KL KR v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln dd gi vp val HKS).
Qed.

Ltac pb11p_run1_pre :=
  intros a (r & Hr & Ha); unfold pb11p_ss1, pb11p_regions1 in Hr; cbn [ss_mem In] in Hr;
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.

(* one pass: the loop head before pass ti reaches MISS's post, given the head before pass ti + 1 (ti < 10) and the
   refusal cut KREFM (taken after pass 10), each at every FP state *)
Lemma pb11p_pass : forall n ti, (ti < 11)%nat ->
  ((ti < 10)%nat -> HA_KLOOP B n (S ti)) -> HA_KREFM B n -> H_KLOOP (fx := fx) B n ti.
Proof.
intros n ti Hti KL KR v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val HI.
pose proof HI as HI0.
destruct HI as (HB & HMID & HST & HVP & HINB & _ & HKM & HNT & HSL3 & HRG).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
pose proof (pb11_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HB as (HCX & HFIb & HOBJ & HSLp & HFSH).
pose proof HFIb as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCAT : sa_cat SEGS B (rdW Wc memc) catA) by (destruct HOBJ as (_ & _ & _ & _ & _ & HC & _); exact HC).
pose proof HCAT as (HCATp & HCATi & HCATr).
destruct (HCATr ti ltac:(unfold pin_spec.CAT_N; lia)) as (tp & HROW & HTOK).
assert (HSH0 : rdW Wc memc (SHADOW_OFF + pin_spec.row_addr catA ti / 8) = Some 0)
  by (apply (pb11p_shadow0 lyc Sc Wc memc mdc ti ltac:(lia) HAR HCAT)).
assert (Htpb : 0 <= tp < 2 ^ 64).
{ destruct HTOK as (Htp0 & _ & _ & _ & Himg).
  pose proof (pa_img_range _ (proj1 (Himg tp ltac:(lia)))) as Rtp. unfold kImgEnd in Rtp. lia. }
set (E := Eimg (Ereg rX [w64 tp; w64 (pf_F v pos + PF_O_KNOWN)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 tp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 (pf_F v pos + PF_O_KNOWN))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U33 : bv_unsigned (ew E 33) = pf_F v pos + PF_O_KNOWN)
  by (rewrite E33; unfold w64, PF_O_KNOWN; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_KLOOP)) with (Z_to_bv 64 (BASE + PF_KLOOP)).
(* pass 0: the separator is "" (0x21860); passes 1 .. 10: "|" (0x21840). The script is the same. *)
destruct ti as [|ti].
{ pose proof (pb11p_seed1 n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val tp HI0
    ltac:(vm_compute; reflexivity) Htpb HROW HSH0) as HS;
  fold E in HS;
  paj_run_to_sh pb11p_RUNTO1 HS HJ PF_KSNP;
  [ pb11p_run1_pre
  | cbn [ms_mem mkst] in HFr, HG, HF; pb11p_clear_md;
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a);
    [ intros a Ha;
      apply (kept_of_frame (segs:=SEGS) E (ss_mem (pb11p_ss1 _)) (w_H Wc) memc (ms_mem ms)
               (fun _ => False) HFr); [| exact Ha | intros HFx; exact HFx];
      intros b wlo whi a' Hin' Hrr; vm_compute in Hin'; cbv beta;
      repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
      destruct Hin'
    | assert (K2 : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a);
      [ intros a; rewrite (pb11p_aview_mod (w_H Wc) (ms_mem ms) a), (pb11p_aview_mod (w_H Wc) memc a);
        apply K1; apply Z.mod_pos_bound; lia
      | assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 21; 26; 25; 22] ->
            getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r));
        [ intros r Hr; cbn [In] in Hr;
          repeat (destruct Hr as [<- | Hr];
            [first [ pb11p_rreg HS; rewrite pb11p_den_atom0; apply EE; reflexivity
                   | pb11p_rreg HS; cbn [sv_denot];
                     rewrite (pb11_rg_get rX (pb11_FI B v) 20 SHADOW_OFF HFI ltac:(pb11p_in));
                     unfold w64; reflexivity ] |]); destruct Hr
        | pmkst HS;
          lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
            change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
              with (cfg_at SEGS (BASE + PF_KSNP) rg mm mdx) end;
          apply (pb11_snp B ASNPRINTF (fx := fx) n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val
                   (ms_regs ms) (ms_mem ms) mdv tp HI0 HJ K2);
          [ apply (pb11p_bvr _ _ 2);
            [reflexivity | rewrite QK; [apply (pb11_rg_get rX _ 2 _ HFI); pb11p_in | pb11p_in]]
          | apply (pb11p_bvr _ _ 3);
            [reflexivity | rewrite QK; [apply (pb11_rg_get rX _ 3 _ HFI); pb11p_in | pb11p_in]]
          | apply (pb11p_bvr _ _ 4);
            [reflexivity | rewrite QK; [apply (pb11_rg_get rX _ 4 _ HFI); pb11p_in | pb11p_in]]
          | apply (pb11p_bvr _ _ 10);
            [reflexivity | pb11p_rreg HS; cbn [sv_denot]; rewrite U33; unfold w64;
             f_equal; f_equal; vm_compute; reflexivity]
          | apply (pb11p_bvr _ _ 11); [reflexivity | pb11p_rreg HS; pb11p_lit]
          | apply (pb11p_bvr _ _ 12);
            [reflexivity | pb11p_rreg HS; pb11p_objd HEI; unfold w64; f_equal; vm_compute; reflexivity]
          | apply (pb11p_bvr _ _ 13);
            [reflexivity | pb11p_rreg HS; pb11p_objd HEI; unfold w64; f_equal; vm_compute; reflexivity]
          | apply (pb11p_bvr _ _ 14);
            [reflexivity | pb11p_rreg HS; rewrite pb11p_den_atom0; exact E32]
          | exact HROW
          | exact HTOK
          | exact (pb11p_after n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val
                     (ms_regs ms) HI0 ltac:(lia) KL KR
                     ltac:(unfold pf_rg, pb11_FI; repeat apply Forall_cons; [..|apply Forall_nil];
                           cbn [fst snd];
                           (rewrite QK; [apply (pb11_rg_get rX _ _ _ HFI); pb11p_in | pb11p_in]))
                     ltac:(unfold pf_rg, PF_RM; cbn [app];
                           repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
                           first [ rewrite QK; [apply (pb11_rg_get rX _ _ _ HRG); pb11p_in | pb11p_in]
                                 | pb11p_rreg HS; pb11p_lit ])) ] ] ] ] ].
  }
do 10 (destruct ti as [|ti];
  [ pose proof (pb11p_seed1 n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val tp HI0
      ltac:(vm_compute; reflexivity) Htpb HROW HSH0) as HS;
    fold E in HS;
    paj_run_to_sh pb11p_RUNTO1 HS HJ PF_KSNP;
    [ pb11p_run1_pre
    | cbn [ms_mem mkst] in HFr, HG, HF; pb11p_clear_md;
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a);
      [ intros a Ha;
        apply (kept_of_frame (segs:=SEGS) E (ss_mem (pb11p_ss1 _)) (w_H Wc) memc (ms_mem ms)
                 (fun _ => False) HFr); [| exact Ha | intros HFx; exact HFx];
        intros b wlo whi a' Hin' Hrr; vm_compute in Hin'; cbv beta;
        repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin'
      | assert (K2 : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a);
        [ intros a; rewrite (pb11p_aview_mod (w_H Wc) (ms_mem ms) a), (pb11p_aview_mod (w_H Wc) memc a);
          apply K1; apply Z.mod_pos_bound; lia
        | assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 21; 26; 25; 22] ->
              getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r));
          [ intros r Hr; cbn [In] in Hr;
            repeat (destruct Hr as [<- | Hr];
              [first [ pb11p_rreg HS; rewrite pb11p_den_atom0; apply EE; reflexivity
                     | pb11p_rreg HS; cbn [sv_denot];
                       rewrite (pb11_rg_get rX (pb11_FI B v) 20 SHADOW_OFF HFI ltac:(pb11p_in));
                       unfold w64; reflexivity ] |]); destruct Hr
          | pmkst HS;
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
              change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
                with (cfg_at SEGS (BASE + PF_KSNP) rg mm mdx) end;
            apply (pb11_snp B ASNPRINTF (fx := fx) n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val
                     (ms_regs ms) (ms_mem ms) mdv tp HI0 HJ K2);
            [ apply (pb11p_bvr _ _ 2);
              [reflexivity | rewrite QK; [apply (pb11_rg_get rX _ 2 _ HFI); pb11p_in | pb11p_in]]
            | apply (pb11p_bvr _ _ 3);
              [reflexivity | rewrite QK; [apply (pb11_rg_get rX _ 3 _ HFI); pb11p_in | pb11p_in]]
            | apply (pb11p_bvr _ _ 4);
              [reflexivity | rewrite QK; [apply (pb11_rg_get rX _ 4 _ HFI); pb11p_in | pb11p_in]]
            | apply (pb11p_bvr _ _ 10);
              [reflexivity | pb11p_rreg HS; cbn [sv_denot]; rewrite U33; unfold w64;
               f_equal; f_equal; vm_compute; reflexivity]
            | apply (pb11p_bvr _ _ 11); [reflexivity | pb11p_rreg HS; pb11p_lit]
            | apply (pb11p_bvr _ _ 12);
              [reflexivity | pb11p_rreg HS; pb11p_objd HEI; unfold w64; f_equal; vm_compute; reflexivity]
            | apply (pb11p_bvr _ _ 13);
              [reflexivity | pb11p_rreg HS; pb11p_objd HEI; unfold w64; f_equal; vm_compute; reflexivity]
            | apply (pb11p_bvr _ _ 14);
              [reflexivity | pb11p_rreg HS; rewrite pb11p_den_atom0; exact E32]
            | exact HROW
            | exact HTOK
            | exact (pb11p_after n _ v pos lyc Sc Wc rX memc mdc cf nm o ln dd gi vp val
                       (ms_regs ms) HI0 ltac:(lia) KL KR
                       ltac:(unfold pf_rg, pb11_FI; repeat apply Forall_cons; [..|apply Forall_nil];
                             cbn [fst snd];
                             (rewrite QK; [apply (pb11_rg_get rX _ _ _ HFI); pb11p_in | pb11p_in]))
                       ltac:(unfold pf_rg, PF_RM; cbn [app];
                             repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
                             first [ rewrite QK; [apply (pb11_rg_get rX _ _ _ HRG); pb11p_in | pb11p_in]
                                   | pb11p_rreg HS; pb11p_lit ])) ] ] ] ] ]
  | ]).
exfalso. lia.
Qed.
End x.
End d.
