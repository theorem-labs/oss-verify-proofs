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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 370 of its 431 lines of code are new or changed and 4992 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: segment A5 of reac_segconf_parse_file, the pieces TAIL and R6 of
   lib/A/Prog/pf_a5_d.v (segment A5's proof, 2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk; the function's rule-24 record
   is the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md).
   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s):
     TAIL 0x88068 addi a1,zero,0x40; mv a0,s3 (s3 = SH + 8); 0x88070 jal meta_fill_f8 (__asan_set_shadow_f8 on buf's
        64 shadow cells: buf out of scope; return 0x88074 = R6).
     R6 0x88074 srli a0,s5,3; add a0,a0,s6; lb a0,0(a0); bnez a0,0x889f8 (check 12, load1 at s5 = t + o; slow path
        0x889f8 andi a1,s5,7; blt a1,a0,0x88084); 0x88084 lbu a0,0(s5); mv s9,s5; bnez a0,0x87ddc (HEAD);
        0x88090 j 0x88bb8 (DONE).
   TAIL: a fresh seed, a run of the plain executor to the call, the call by pf_a2_k.v aj_set_shadow_atS (v = 0xf8,
   q = SH + 8, n = 64), and INV_R6 rebuilt with pf_a5_k.v a5_move0 and a5_fill_fsh. R6: a fresh seed whose one
   region is the text's byte at s5 (extra atom 32, trim_tr.v tt_entry's form), a run of the token executor (the
   inline check's obligation is the text's addressability, pf_obj's sa_addr), the branch on the byte, and the
   exits H_HEAD (pred n) (a byte left: o < |s|) and H_DONE (the text's NUL: o = |s|, no line left; the plain proof
   is the plain-build walk owner's lib/Prog/pf_p2.v tail_holds at 04f2be60e018).
   Several helpers (tl_aview_mod, tl_vis_mod, tl_rg_keep, tl_rg_keep_pi, the tl_rreg / tl_atom / tl_atoms
   tactics) are copied from the sibling piece lib/A/Prog/pf_a5_r3.v, tl_after / tl_awr from
   lib/A/Prog/trim_tr.v (tt_after / tt_awr). The one Section hypothesis is pf_pieces.v's for this call:
   aset_shadow_realizes at pa_sigma SS___asan_set_shadow_f8 with value 0xf8, at every FP state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a2_k pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small facts ---------- *)
Lemma tl_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db. replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma tl_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma tl_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma tl_br_ne0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> negb (v =? 0) = b.
Proof. intros E n v b H Hv Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc. Qed.
Lemma tl_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma tl_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* the slots INV_DONE names are four of PF_SL's *)
Lemma tl_sl_sub : forall rd b L L', (forall x, In x L' -> In x L) -> pf_sl rd b L -> pf_sl rd b L'.
Proof. intros rd b L L' Hs H. unfold pf_sl in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hs x Hx)). Qed.

Ltac tl_in := unfold PF_RL, a5_FI; cbn [In app]; repeat first [left; reflexivity | right].
Ltac tl_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* a register the run left as an atom of the seed: its value is the seed register's, from the cut's list R *)
Ltac tl_atom HS EE R :=
  lazymatch type of R with pf_rg ?rx _ =>
    tl_rreg HS; rewrite tl_den_atom0;
    lazymatch goal with |- ew _ ?nn = _ =>
      let k := eval vm_compute in (Z.of_nat nn) in
      transitivity (getr rx (Z_to_bv 5 k)); [apply EE; reflexivity | apply (a5_rg_get _ _ k _ R); tl_in] end end.
Ltac tl_atoms := repeat (apply Forall_cons; [split; [cbn [fst]; lia | cbn [fst]; vm_compute; reflexivity] |]); apply Forall_nil.
Ltac tl_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* the seed at TAIL: every register its own atom, no region (the run reads and writes no memory) *)
Definition tl_ss : sstate := mkSS (AF_reac_segconf_parse_file + 0x5f0) sr_atoms [] None (mkFacts [] [] []).
(* the seed at R6: every register its own atom; atom 32 is the text's byte at s5 = t + o, the one region (read only,
   trim_tr.v tt_ss's form); s5 an application address, s6 the shadow base (the token executor's Bx) *)
Definition r6_regions : smem := [ YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition r6_facts : facts :=
  mkFacts [ (21%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition r6_ss : sstate := mkSS (AF_reac_segconf_parse_file + 0x5fc) sr_atoms r6_regions None r6_facts.
Definition tl_Bx : sv := SOff 22 0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma tl_aview_mod : forall H m a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma tl_vis_mod : forall H m m', (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a <> None -> aview SEGS H m' a <> None) ->
  forall a, aview SEGS H m a <> None -> aview SEGS H m' a <> None.
Proof.
intros H m m' K a Hv. rewrite tl_aview_mod in *. apply K; [apply Z.mod_pos_bound; lia | exact Hv].
Qed.
(* the registers a run left as their own atoms keep the values they had *)
Lemma tl_rg_keep : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok SEGS E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_restrict_reg SEGS H E ss ms _ HS), Hs, tl_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma tl_rg_keep_pi : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hs, tl_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

(* the R6 seed (trim_tr.v tt_entry's form) *)
Definition r6_E (regs : bvmap 5 word) (C : Z) : env := Eimg (Ereg regs [Z_to_bv 64 C]).
Lemma r6_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc p C,
  getr regs 21 = w64 p -> getr regs 22 = w64 SB ->
  4096 <= p <= 2 ^ 47 - 1 -> 0 <= C <= 255 ->
  rdW W memc p = Some C ->
  st_ok_pi SEGS VAL (r6_E regs C) r6_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x5fc))) memc (seg_rom SEGS))).
Proof.
intros W regs memc p C H21 H22 Hp HC Hrd.
set (E := r6_E regs C).
assert (E21 : ew E 21 = Z_to_bv 64 p) by (subst E; unfold r6_E; rewrite (ew_Eimg_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; unfold r6_E; rewrite (ew_Eimg_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 C) by (subst E; unfold r6_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold r6_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r6_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E21, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H W) memc p C Hrd) as (b & Hb & Hv & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst C. apply Z_to_bv_bv_unsigned.
  + rewrite ?Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [r6_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E21, E22, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callee of the TAIL piece (pf_pieces.v's list for A5): meta_fill_f8 = __asan_set_shadow_f8 (segment A2's
   hypothesis form) *)
Hypothesis ASHF8 : forall fx0 : YK11.FPState,
  @aset_shadow_realizes fx0 rc SEGS B (pa_sigma SS___asan_set_shadow_f8) 0xf8.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a token run that writes nothing: the environment agrees with E0 below 33 (HAE), the memory is memc (KM),
   every byte present in memc is present (KP) (trim_tr.v tt_after) *)
Ltac tl_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree 33 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, apresent (w_H _) _ a -> apresent (w_H _) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac tl_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* pf_base and pf_st at a state the run reached without writing a byte: the same layout and frame state, the
   journal at the new state, every byte kept, the frame registers kept *)
Lemma tl_still : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (a5_FI B v) ->
  pf_st v pos (rdW Wc memc) cf cur nm k ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc /\ pf_st v pos (rdW Wc memc') cf cur nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc cf cur nm k HB HJ KM HRF HST.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _ & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & HHC).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc memc' a = rdW Wc memc a)
  by (intros a Ha _; exact (KM a Ha)).
assert (KVIS : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
{ apply tl_vis_mod. intros a Ha Hv. rewrite (KM a Ha). exact Hv. }
split.
- apply (a5_move0 B v pos lyc Sc Wc rX memc mdc sc Sc Wc rX' memc' mdc' sc HB HJ).
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact KALL.
  + exact KVIS.
  + exact HRF.
  + intros i Hi. pose proof HB as (_ & _ & _ & _ & HFSH). rewrite KM; [exact (HFSH i Hi) | unfold kHighShadowEnd in G12; lia].
- eapply (a5_keep_st B v pos lyc Sc Wc memc mdc Wc memc');
    first [exact G | exact HAR | exact Hin | exact Hly | exact KALL | exact KVIS | exact HHC | exact HST].
Qed.

(* ======================= TAIL (0x88068): buf out of scope (meta_fill_f8) ======================= *)
Lemma a5_tail_ok : forall n, H_R6 B n -> H_TAIL B n.
Proof.
intros n HR6 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLC & HLT & HST & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & HLS & _ & _ & _ & HC).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _ & _ & HFSH).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ES : ESTACK = 4096) by reflexivity.
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HS : st_ok_pi SEGS VAL E tl_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x5f0))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold tl_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + PF_TAIL)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x5f0))).
paj_run_shc RUNP RUNC HS HJ.
{ unfold tl_ss. apply awr_ok_nil. }
tl_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem tl_ss) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
(* the registers at the call *)
assert (QFI : pf_rg (ms_regs ms) (a5_FI B v)).
{ apply (tl_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold a5_FI; tl_atoms | exact HFI]. }
assert (Q2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (a5_rg_get _ _ 2 _ QFI); tl_in).
assert (Q3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (a5_rg_get _ _ 3 _ QFI); tl_in).
assert (Q4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (a5_rg_get _ _ 4 _ QFI); tl_in).
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + A5_R6)).
{ tl_rreg HS. rewrite (codeptr_val _ _ HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_SH v pos + 8)) by tl_atom HS EE HRG.
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 64) by (tl_rreg HS; reflexivity).
assert (QL : pf_rg (ms_regs ms)
    (PF_RL v pos ++ [(21, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur)])).
{ unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    tl_atom HS EE HRG. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite (tl_bvr (ms_regs ms) 2%bv 2 _ eq_refl Q2). unfold w64. rewrite unsigned_lit_small by lia. lia. }
pmkst HS.
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (pa_sigma SS___asan_set_shadow_f8) 0xf8 (ASHF8 fx) Wc
    (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc _ 0 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A5_R6)) 5 pos
    (pf_SH v pos + 8) 64 HJ).
  - left. reflexivity.
  - exact Hsp.
  - exact (tl_m16 _ _ G5 G3).
  - lia.
  - rewrite ESTK, ES. lia.
  - apply (tl_bvr _ _ 3); [reflexivity | exact Q3].
  - apply (tl_bvr _ _ 4); [reflexivity | exact Q4].
  - apply (tl_bvr _ _ 1); [reflexivity | exact Q1].
  - apply ret_ok_codeptr_v; [unfold A5_R6, AF_reac_segconf_parse_file; lia | reflexivity].
  - apply (tl_bvr _ _ 10); [reflexivity | exact Q10].
  - apply (tl_bvr _ _ 11); [reflexivity | exact Q11].
  - lia.
  - change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). lia.
  - change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). change (fs_frame_bytes 5 / 8) with 256. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hval & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A5_R6)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + A5_R6) regs2 mem2 md2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HK2 by lia.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite ESTK in Hpres2.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. rewrite (HK2 a Ha); [exact (K1 a Ha) | |]; intros Hq; apply Hn; unfold a5_Wrx.
  - right; right; right. split; [reflexivity | lia].
  - left. rewrite ES in Hq. rewrite ESTK. lia. }
assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ apply tl_vis_mod. intros a Ha Hv.
  destruct (Z_lt_le_dec a (pf_s1 v - ESTACK)) as [Hs1 | Hs1]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hs2 | Hs2]].
  2: { apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ES in Hs1. lia. }
  all: destruct (Z_lt_le_dec a (pf_SH v pos + 8)) as [Hlo | Hlo];
       [|destruct (Z_lt_le_dec a (pf_SH v pos + 72)) as [Hhi | Hhi]].
  all: try (replace a with (pf_SH v pos + 8 + (a - (pf_SH v pos + 8))) by lia; rewrite Hval by lia; discriminate).
  all: rewrite (HK2 a Ha) by (rewrite ?ES in *; lia); rewrite (K1 a Ha); exact Hv. }
assert (HF8 : forall i, 8 <= i < 72 -> rdW Wc mem2 (pf_SH v pos + i) = Some (pf_io false)).
{ intros i Hi. replace (pf_SH v pos + i) with (pf_SH v pos + 8 + (i - 8)) by lia. rewrite Hval by lia. reflexivity. }
assert (HFS : pf_fsh (rdW Wc mem2) (pf_SH v pos)
    (PFSc (sc_cn PF_SC_LINE) false (sc_low PF_SC_LINE) (sc_l146 PF_SC_LINE) (sc_known PF_SC_LINE))).
{ eapply a5_fill_fsh; [exact G | exact KW | exact HF8 | exact HFSH]. }
refine (HR6 v pos (p_ly v) Sc Wc regs2 mem2 md2 cf cur nm o ln d _).
split; [|split; [exact HLC|split; [exact HLT|split]]].
- apply (a5_move0 B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_HEAD HB HJ2).
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact KW.
  + exact HV.
  + exact (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_FI_cs B v) QFI).
  + exact HFS.
- eapply (a5_keep_st B v pos (p_ly v) Sc Wc memc mdc Wc mem2);
    first [exact G | exact HAR | exact Hin | reflexivity | exact KW | exact HV | exact HC | exact HST].
- apply (a5_rg_pres (ms_regs ms) regs2 _ HP2); [|exact QL].
  unfold PF_RL. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.

(* ======================= R6 (0x88074): check 12, the byte at p', HEAD or DONE ======================= *)
Lemma a5_r6_ok : forall n, H_HEAD B (pred n) -> H_DONE B -> H_R6 B n.
Proof.
intros n HH HD v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLC & HLT & HST & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _ & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & _ & HSTR & HADDR & HHT & HHC).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _ & HSL & _).
pose proof HLC as (Hole & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
(* the text lies in a live block: 4096 <= t, t + |s| + 1 <= alloc_ceiling *)
destruct HHT as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
pose proof (req_size_pos mt (proj1 Hm)) as [_ Hreq].
unfold pf_len in Hbt2.
(* the byte at p' = t + o: s's byte o, or its NUL when o = |s| *)
destruct HSTR as ((HZS & _) & _).
set (C := nth o (p_s v ++ [0]) 0).
assert (VC : rdW Wc memc (p_t v + Z.of_nat o) = Some C).
{ exact (HZS o ltac:(rewrite length_app; cbn [length]; lia)). }
destruct (aview_byte SEGS (w_H Wc) memc _ _ VC) as (_ & _ & _ & HCr).
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (p_t v) (pf_len v))
  by (destruct HADDR as (_ & _ & _ & HRA & _); exact HRA).
(* the seed *)
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (p_t v + Z.of_nat o)) by (apply (a5_rg_get _ _ 21 _ HRG); tl_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SB) by (rewrite SB_SHADOW_OFF; apply (a5_rg_get _ _ 22 _ HFI); tl_in).
pose proof (r6_entry Wc rX memc (p_t v + Z.of_nat o) C (tl_bvr rX 21%bv 21 _ eq_refl R21)
  (tl_bvr rX 22%bv 22 _ eq_refl R22) ltac:(lia) ltac:(lia) VC) as HS.
assert (HEI : img_env VAL A_LIM (r6_E rX C)) by (unfold r6_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 C]) (r6_E rX C))
  by (split; [intros k Hk; unfold r6_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (r6_E rX C) k = getr rX r)
  by (intros k r Hk; unfold r6_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E21 : ew (r6_E rX C) 21 = Z_to_bv 64 (p_t v + Z.of_nat o)) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl); exact R21).
assert (E22 : ew (r6_E rX C) 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); exact R22).
assert (E32 : ew (r6_E rX C) 32 = Z_to_bv 64 C)
  by (unfold r6_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI HA0 EE E21 E22 E32. generalize (r6_E rX C) as E0. intros E0 HS HEI HA0 EE E21 E22 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
assert (SHOK : sh_ok SEGS tl_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + A5_R6)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x5fc))).
(* 0x88074 .. 0x8808c: check 12, the byte, s9 = s5, up to `bnez a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold tl_Bx. rewrite (U_atom _ 22 SB E22), (U_atom _ 21 _ E21) by (unfold SB; lia). rewrite SB_SHADOW_OFF.
  exact (range_addressable_sub _ _ (p_t v) (pf_len v) (p_t v + Z.of_nat o) 1 HRA ltac:(lia) ltac:(unfold pf_len; lia)). }
{ tl_awr. }
tl_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a byte left: the next line, HEAD (pred n) *)
  pose proof (tl_br_ne0 _ 32 C _ (tl_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as CNZ.
  apply Bool.negb_true_iff, Z.eqb_neq in CNZ. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_HEAD. { tl_awr. }
  tl_after E0 HAE KM KP.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) => rename msn into msR end.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (EEn : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew En k = getr rX r)
      by (intros k r Hk; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite (proj1 HAE k) by lia; exact (EE k r Hk)) end.
  assert (Hos : (o < length (p_s v))%nat).
  { destruct (Nat.lt_ge_cases o (length (p_s v))) as [Hlt | Hge]; [exact Hlt|]. exfalso. apply CNZ.
    unfold C. rewrite app_nth2 by lia. replace (o - length (p_s v))%nat with 0%nat by lia. reflexivity. }
  assert (QFI : pf_rg (ms_regs msR) (a5_FI B v)).
  { apply (tl_rg_keep_pi _ _ msR (w_H Wc) rX _ HS EEn); [unfold a5_FI; tl_atoms | exact HFI]. }
  assert (QL : pf_rg (ms_regs msR)
      (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur)])).
  { unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      tl_atom HS EEn HRG. }
  destruct (tl_still v pos lyc Sc Wc rX memc mdc (ms_regs msR) (ms_mem msR) _ PF_SC_HEAD cf cur nm _ HB HJ KM QFI HST)
    as (HB2 & HST2).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    refine (HH v pos lyc Sc Wc rg mm mdn cf cur nm o ln d _) end.
  split; [exact HB2|]. split; [exact HLC|]. split; [exact Hos|]. split; [lia|]. split; [exact HST2 | exact QL].
- (* the text's NUL: no line left, DONE *)
  pose proof (tl_br_ne0 _ 32 C _ (tl_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as CZ.
  apply Bool.negb_false_iff, Z.eqb_eq in CZ. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_DONE. { tl_awr. }
  tl_after E0 HAE KM KP.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) => rename msn into msR end.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (EEn : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew En k = getr rX r)
      by (intros k r Hk; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite (proj1 HAE k) by lia; exact (EE k r Hk)) end.
  assert (Hoe : o = length (p_s v)).
  { destruct (Nat.lt_ge_cases o (length (p_s v))) as [Hlt | Hge]; [|lia]. exfalso. apply NZ.
    assert (Hn0 : nth o (p_s v) 0 = 0) by (rewrite <- (app_nth1 (p_s v) [0] 0 Hlt); exact CZ).
    rewrite <- Hn0. apply nth_In. exact Hlt. }
  assert (Hsk : skipn o (p_s v) = []) by (apply skipn_all2; lia).
  assert (QFI : pf_rg (ms_regs msR) (a5_FI B v)).
  { apply (tl_rg_keep_pi _ _ msR (w_H Wc) rX _ HS EEn); [unfold a5_FI; tl_atoms | exact HFI]. }
  assert (Q27 : pf_rg (ms_regs msR) [(27, pf_SH v pos)]).
  { unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. tl_atom HS EEn HRG. }
  destruct (tl_still v pos lyc Sc Wc rX memc mdc (ms_regs msR) (ms_mem msR) _ PF_SC_HEAD cf cur nm _ HB HJ KM QFI HST)
    as (HB2 & HST2).
  pose proof HB2 as (HCX2 & HFI2 & HOBJ2 & HSL2 & HFSH2).
  pose proof HST2 as (HRC2 & _).
  unfold a5_post. rewrite Hsk. change (r_lines (cf, cur, nm) ln (lines [])) with (cf, cur, nm). cbn [fst].
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    refine (HD v pos lyc Sc Wc rg mm mdn cf _) end.
  split; [exact HCX2|]. split; [exact HFI2|]. split; [exact HOBJ2|]. split; [exact HRC2|].
  split; [|split; [exact HFSH2 | exact Q27]].
  apply (tl_sl_sub _ _ (PF_SL v pos)); [|exact HSL2].
  intros x Hx. cbn [In] in Hx. unfold PF_SL. cbn [In].
  repeat (destruct Hx as [<- | Hx]; [repeat first [left; reflexivity | right] |]). destruct Hx.
Qed.
End e.
End f.
End d.
