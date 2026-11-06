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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 455 of its 515 lines of code are new or changed and 4993 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the cut ZST of segment A11a of reac_segconf_parse_file's walk,
   `a11a_zst_ok : forall n, HA_MISS B n -> A11_HIT_stmt B n -> forall li, A11_ZST_stmt B n li`
   (statements: lib/A/Prog/pf_a11a_k.v and lib/A/Prog/pf_pieces.v). Part of segment A11a's proof (the cut ZST), by the G3 walk owner,
   2026-10-30. proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk -- A11a's NUL
   store, by_token call and miss arm); the whole function's rule-24 lookup and CONFIRM (the G3 walk owner's) are in
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md.

   The code (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s:683-691 in records/segp/dis/ at that commit),
   9 instructions, 0x8851c .. 0x8853c (and the
   slow arm 0x88ac0-0x88ac8 of check #26, 3 instructions, decided dead):
     0x8851c add a0,s4,a3        a0 = e = low146 + li (s4 = F + 0x2e0, a3 = li)
     0x88520 srli/add/lb/bnez    check #26 (store1 at e): decided by the shadow entry of e (low146's cells are 0
                                 at scope PF_SC_L146), its slow arm 0x88ac0-0x88ac8 is dead
     0x88530 sb zero,0(a0)       low146[li] = 0
     0x88534 mv a0,s4 ; 0x88538 jal reac_box_catalogue_by_token
     0x8853c beqz a0,0x885a8     NULL -> MISS (pf_pieces.v INV_MISS, applied through HA_MISS); else HIT 0x88540
   The proof: one token run from the seed zm_entry (the store's byte as a written one-byte region on its own atom,
   the alias s4 + a3 = that atom, the shadow entry of the byte) to the call; the cut state at the call by
   pf_a11a_t.v's a11m_cx; the call by PaCall.cl_callS (by_token's post is apost_base: the same FP state), its
   premises from the state at the call, the frame chain by pf_a5_k.a5_chain; a fresh seed at the return 0x8853c,
   the branch split by psrr_branch_tok and decided by by_token's result; the state at MISS / HIT by a11m_cx again
   (by_token keeps every byte outside its own window, sa_kept ... (fun _ => False)).
   Section hypotheses: BT (the callee contract, pf_pieces.v:686) and SIGP (the call target). No SSPX, no VRO. *)
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
PaCallRun PaArt PaFx PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  reac_box_catalogue_by_token_c pf_pieces pf_a5_k pf_a11a_k pf_a11a_f pf_a11a_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= tactics (pf_a11b_m.v's pfm_rreg, the A11b proof) ======================= *)
Ltac zm_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac zm_in := solve [cbn [In app]; repeat (first [left; reflexivity | right])].

(* ======================= pure facts ======================= *)
Lemma zm_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma zm_getz : forall (rg : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> getr rg (Z_to_bv 5 z) = getr rg r.
Proof. intros rg r z <-. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
(* the branch at 0x8853c: beqz on an atom of known value (trim_s.v tr_br_eq0) *)
Lemma zm_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof. intros E n v b H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc. Qed.
(* low146's three shadow cells at scope PF_SC_L146 *)
Lemma zm_shb : forall i, 92 <= i < 95 -> pf_shb PF_SC_L146 i = 0.
Proof. intros i Hi. assert (i = 92 \/ i = 93 \/ i = 94) as [-> | [-> | ->]] by lia; reflexivity. Qed.
(* the folded value's bytes (pf_a11a_f.v a11f_low_map) *)
Lemma zm_nth_low : forall val i, ~ In 0 val -> (i < length (r_low val 0 24))%nat ->
  nth i (r_low val 0 24) 0 = lower (nth i val 0).
Proof.
intros val i Hn Hi. pose proof (a11f_low_len val 24 Hn) as Hl.
assert (Hi23 : (i < 23)%nat) by (rewrite Hl in Hi; cbn [Nat.sub] in Hi; lia).
rewrite (a11f_low_map val 24 Hn).
transitivity (nth i (map lower (firstn (24 - 1) val)) (lower 0)); [reflexivity|].
rewrite map_nth. f_equal. apply a11f_nth_firstn. cbn [Nat.sub]. lia.
Qed.
Lemma zm_low_len : forall val, ~ In 0 val -> (length (r_low val 0 24) <= 23)%nat.
Proof. intros val Hn. rewrite (a11f_low_len val 24 Hn). cbn [Nat.sub]. lia. Qed.

(* ======================= the seed at ZST (0x8851c) ======================= *)
(* every register its own atom; atom 32 = e = low146 + li, the byte the NUL store writes (a one-byte written
   region, trim_t.v's tf_regions shape), the alias s4 + a3 = e (fuzz_command's answer_l.v al_facts), s6 = the
   shadow base exactly; the shadow entry of e decides check #26 *)
Definition zm_regions : smem := [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ].
Definition zm_facts : facts :=
  mkFacts [ (32%nat, PTR 0); (22%nat, mkAF SB SB 0) ] [] [ (SAlu ALU_ADD (SOff 20 0) (SOff 13 0), SOff 32 0) ].
Definition zm_ss : sstate := mkSS A11_ZST sr_atoms zm_regions None zm_facts.
Definition zm_Bx : sv := SOff 22 0.
Definition zm_SH : list shent := [mkSHE 32 0 1].
(* the return 0x8853c: every register its own atom, no region *)
Definition zb_ss : sstate := mkSS A11_RET_BT sr_atoms [] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition zm_E (rX : bvmap 5 word) (e : Z) : env := Eimg (Ereg rX [Z_to_bv 64 e]).
(* a reader reads an address through its 64-bit word (segment A10a's a10_aview_wrap) *)
Lemma zm_aview_wrap : forall H mem a, aview SEGS H mem a = aview SEGS H mem (a mod 2 ^ 64).
Proof.
intros H mem a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod.
reflexivity.
Qed.

Lemma zm_entry : forall (W : world SEGS) (rX : bvmap 5 word) memc F' li' e,
  getr rX (Z_to_bv 5 20) = w64 F' -> getr rX (Z_to_bv 5 13) = w64 li' -> getr rX (Z_to_bv 5 22) = w64 SB ->
  e = F' + li' -> 0 <= li' -> 0 <= F' -> 4096 <= e <= 140737479966720 -> apresent (w_H W) memc e ->
  st_ok_pi SEGS VAL (zm_E rX e) zm_ss
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + A11_ZST)) memc (seg_rom SEGS))).
Proof.
intros W rX memc F' li' e H20 H13 H22 He Hli HF He47 Hpe.
set (E := zm_E rX e).
assert (E20 : ew E 20 = Z_to_bv 64 F')
  by (subst E; unfold zm_E; rewrite (ew_Eimg_Ereg_nat rX _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E13 : ew E 13 = Z_to_bv 64 li')
  by (subst E; unfold zm_E; rewrite (ew_Eimg_Ereg_nat rX _ 13 (Z_to_bv 5 13) eq_refl); exact H13).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (subst E; unfold zm_E; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 e)
  by (subst E; unfold zm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
rewrite restrict_mkst_fx. unfold zm_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold zm_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E32, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hpe.
- unfold zm_regions. cbn. tauto.
- split; [|split; [exact I|]].
  + cbn [zm_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite E32, E22, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [zm_facts f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom _ 20 F' E20), (U_atom _ 13 li' E13), (U_atom _ 32 e E32) by lia.
    subst e. apply zcanon_id. unfold M64. lia.
Qed.

(* a byte a run wrote (the A11b proof's pf_a11b_m.v pfm_cell_of_region) *)
Definition zm_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma zm_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> zm_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
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

(* low146's shadow cells read 0 at scope PF_SC_L146 *)
Lemma zm_l146_sh : forall (rd : reader) v pos x, a5_G v pos -> pf_fsh rd (pf_SH v pos) PF_SC_L146 ->
  pf_F v pos + PF_O_L146 <= x < pf_F v pos + PF_O_L146 + 24 -> rd (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros rd v pos x G HF Hx.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF.
assert (MF : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk. replace (k * 32) with ((4 * k) * 8) by lia.
  apply Z_mod_mult. }
unfold PF_O_L146 in Hx.
assert (Hi : 92 <= x / 8 - pf_F v pos / 8 < 95) by lia.
pose proof (HF (x / 8 - pf_F v pos / 8) ltac:(lia)) as H.
rewrite zm_shb in H by lia. rewrite G10 in H.
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + pf_F v pos / 8 + (x / 8 - pf_F v pos / 8)) by lia.
exact H.
Qed.
(* the folded value with its NUL in low146 is a C string *)
Lemma zm_low_str : forall (rd : reader) v pos val li, a5_G v pos -> ~ In 0 val ->
  li = length (r_low val 0 24) ->
  (forall j, (j < li)%nat -> rd (pf_F v pos + PF_O_L146 + Z.of_nat j) = Some (lower (nth j val 0))) ->
  rd (pf_F v pos + PF_O_L146 + Z.of_nat li) = Some 0 ->
  (forall x, pf_F v pos <= x < pf_F v pos + 2048 -> rd x <> None) ->
  sa_str rd (pf_F v pos + PF_O_L146) (r_low val 0 24).
Proof.
intros rd v pos val li G Hn HL HB H0 HP.
pose proof (zm_low_len val Hn) as Hlen.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
split; [split|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i li) as [Hil | Hil].
  + rewrite app_nth1 by lia. rewrite zm_nth_low by (first [exact Hn | lia]). exact (HB i Hil).
  + assert (i = li) as -> by lia. rewrite app_nth2 by lia.
    replace (li - length (r_low val 0 24))%nat with 0%nat by lia. exact H0.
- exact (a11f_low_nulfree val 24 Hn).
- intros x Hx. rewrite <- HL in Hx. apply HP.
  pose proof (Z.div_mod (pf_F v pos + PF_O_L146 + Z.of_nat li) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (pf_F v pos + PF_O_L146 + Z.of_nat li) 8 ltac:(lia)).
  unfold PF_O_L146 in *. lia.
Qed.

Section e.
Variable B : asyms.
(* reac_box_catalogue_by_token, the one callee of this piece (pf_pieces.v:686), at the listing's entry and image
   A's numbers (SegInstA.v: STK_reac_box_catalogue_by_token, RLO_A, RHI_A, catA), at every FP state *)
Hypothesis BT : forall fx0 : YK11.FPState,
  reac_box_catalogue_by_token_contract (fx := fx0) SEGS B
    (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
(* the listing's call target over the abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* low146 [F + 0x2e0, + k) is addressable, in the frame, with its shadow visible *)
Lemma zm_low_addr : forall v pos lyc Sc (W : world SEGS) mem md k,
  a5_G v pos -> AR SEGS B lyc Sc W mem md -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  pf_fsh (rdW W mem) (pf_SH v pos) PF_SC_L146 -> 0 < k <= 24 ->
  sa_addr (rdW W mem) (pf_F v pos + PF_O_L146) k.
Proof.
intros v pos lyc Sc W mem md k G HAR Hin Hly HF Hk. subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & _).
split; [unfold PF_O_L146; lia|]. split; [unfold PF_O_L146; lia|].
split; [exact (amem_range_sub_app (pf_F v pos) 2048 (pf_F v pos + PF_O_L146) k G9 G7 ltac:(unfold PF_O_L146; lia)
  ltac:(unfold PF_O_L146; lia) ltac:(lia))|].
split.
- intros x Hx. exists 0. split; [apply (zm_l146_sh _ v pos x G HF); lia | left; reflexivity].
- intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS (p_ly v) Sc W mem md 5 pos); [exact HAR | exact Hin | | | lia];
  change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); change (fs_frame_bytes 5) with 2048;
  unfold PF_O_L146; lia.
Qed.

Theorem a11a_zst_ok : forall n : nat, HA_MISS B n -> A11_HIT_stmt B n -> forall li : nat, A11_ZST_stmt B n li.
Proof.
intros n HMISS HHIT li. unfold A11_ZST_stmt.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (HCX & HLI & HCAP & HLOW & HRG).
pose proof HCX as (HB & HMID & HST & HSTR & HINB & HSL).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & Hfp & Hshp).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFR.
pose proof HB as (HCXp & HFI & HOBJ & HSLB & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HSTR as ((_ & Hnf) & _).
pose proof (zm_low_len val Hnf) as Hlen.
pose proof HINB as HINB'. unfold pf_inb, PF_O_BUF in HINB'.
rewrite SPF in G1.
assert (Hs16 : pf_s1 v mod 16 = 0).
{ rewrite (Z.div_mod (pf_s1 v) 32) by lia. rewrite G5, Z.add_0_r.
  replace (32 * (pf_s1 v / 32)) with ((2 * (pf_s1 v / 32)) * 16) by lia. apply Z_mod_mult. }
assert (RF : forall r x, In (r, x) (a5_FI B v) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x H; exact (a5_rg_get rX _ r x HFR H)).
assert (RM : forall r x, In (r, x) (PF_RL v pos ++ PF_RM v o ln ++ [(13, Z.of_nat li); (20, pf_F v pos + PF_O_L146); (25, vp)]) ->
  getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x H; exact (a5_rg_get rX _ r x HRG H)).
set (e := pf_F v pos + PF_O_L146 + Z.of_nat li).
assert (He : pf_F v pos + PF_O_L146 <= e < pf_F v pos + PF_O_L146 + 24) by (subst e; lia).
assert (Hpe : apresent (w_H Wc) memc e) by (apply Hfp; subst e; unfold PF_O_L146; lia).
(* ---- the seed at 0x8851c ---- *)
pose proof (zm_entry Wc rX memc (pf_F v pos + PF_O_L146) (Z.of_nat li) e
  ltac:(apply RM; unfold PF_RL, PF_RM; zm_in) ltac:(apply RM; unfold PF_RL, PF_RM; zm_in)
  ltac:(apply RF; unfold a5_FI; zm_in) eq_refl ltac:(lia) ltac:(unfold PF_O_L146; lia)
  ltac:(subst e; unfold PF_O_L146; lia) Hpe) as HS.
assert (HEI : img_env VAL A_LIM (zm_E rX e)) by (unfold zm_E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (zm_E rX e) n0 = getr rX r)
  by (intros n0 r Hn0; unfold zm_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew (zm_E rX e) 32 = Z_to_bv 64 e)
  by (unfold zm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI EE E32. generalize (zm_E rX e) as E0. intros E0 HS HEI EE E32.
assert (U32 : bv_unsigned (ew E0 32) = e) by (rewrite E32; apply unsigned_lit_small; subst e; unfold PF_O_L146; lia).
assert (UB : U E0 zm_Bx = SHADOW_OFF).
{ unfold zm_Bx. apply (U_atom E0 22 SB); [rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); apply RF; unfold a5_FI; zm_in
  | unfold SB; lia]. }
assert (UE : U E0 (SOff 32 0) = e) by (apply U_atom; [exact E32 | subst e; unfold PF_O_L146; lia]).
assert (HRAe : range_addressable (rdW Wc memc) SHADOW_OFF e 1).
{ intros x Hx. exists 0. split; [apply (zm_l146_sh _ v pos x G HFSH); lia | left; reflexivity]. }
assert (SHOK : sh_ok SEGS zm_Bx zm_SH E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, zm_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 zm_Bx 32%nat e 1 e 0 1 HRAe UB UE); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. subst e. unfold PF_O_L146 in *. lia. }
unfold cfg_at. change (w64 (BASE + A11_ZST)) with (Z_to_bv 64 (BASE + A11_ZST)).
(* ---- 0x8851c .. 0x88538: check #26, the NUL store, a0 = low146, the call ---- *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 32%nat) (b := e); [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 5, pos.
  split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
  subst e. unfold PF_O_L146 in *. lia. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* what the run kept and what it wrote *)
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> a <> e -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun a' => a' = e) HFr);
    [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U32 in Hrr; lia. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  lazymatch goal with H : img_env _ _ Ex |- _ => rename H into HEI1 end end.
cbn [ms_mem restrict] in HR0.
assert (HW0 : rdW Wc (ms_mem ms) e = Some 0).
{ pose proof (zm_cell_of_region _ (w_H Wc) (ms_mem ms) 32 e _ _ _ _ _ 0 0 HR0) as HW.
  rewrite Z.add_0_r in HW. apply HW; [rewrite ?ew_ewset_other by lia; exact U32 | vm_compute; reflexivity]. }
(* the registers at the call *)
assert (QR : forall r x, In (r, x) (a5_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++ [(20, pf_F v pos + PF_O_L146); (25, vp)]) ->
  getr (ms_regs ms) (Z_to_bv 5 r) = w64 x).
{ intros r x Hr. unfold a5_FI, PF_RL, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      zm_rreg HS; rewrite zm_den0, ?ew_ewset_other by lia;
      lazymatch goal with |- ew _ ?nn = _ => rewrite (EE nn (Z_to_bv 5 k) eq_refl) end;
      first [apply RF; unfold a5_FI; zm_in | apply RM; unfold PF_RL, PF_RM; zm_in] end |]).
  destruct Hr. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A11_RET_BT)) by (zm_rreg HS; exact (codeptr_val _ 14344 HEI1)).
assert (Q10 : getr (ms_regs ms) 10 = w64 (pf_F v pos + PF_O_L146)).
{ zm_rreg HS. rewrite zm_den0, ?ew_ewset_other by lia. rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl).
  apply RM. unfold PF_RL, PF_RM. zm_in. }
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v))
  by (rewrite <- (zm_getz (ms_regs ms) 2 2 eq_refl); apply QR; unfold a5_FI; zm_in).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite <- (zm_getz (ms_regs ms) 3 3 eq_refl); apply QR; unfold a5_FI; zm_in).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite <- (zm_getz (ms_regs ms) 4 4 eq_refl); apply QR; unfold a5_FI; zm_in).
assert (Q8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v))
  by (rewrite <- (zm_getz (ms_regs ms) 8 8 eq_refl); apply QR; unfold a5_FI; zm_in).
(* the cut state at the call: the NUL store kept every byte but e *)
assert (Hedef : e = pf_F v pos + PF_O_L146 + Z.of_nat li) by reflexivity.
assert (HK1 : forall a, 0 <= a < 2 ^ 64 -> ~ a11m_X v pos a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply KM1; [exact Ha|]. intros Heq. apply Hn. right; left. rewrite Heq. exact He. }
assert (HFSH1 : pf_fsh (rdW Wc (ms_mem ms)) (pf_SH v pos) PF_SC_L146).
{ intros i Hi. unfold kLowMemEnd, kHighShadowEnd in G11, G12.
  rewrite KM1; [exact (HFSH i Hi) | lia |].
  intros Heq. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold PF_O_L146 in He. lia. }
assert (HRG1 : pf_rg (ms_regs ms) (a5_FI B v)).
{ unfold pf_rg. rewrite Forall_forall. intros [r x] Hx. apply QR. apply in_or_app. left. exact Hx. }
assert (CX1 : a11_cx B n v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val).
{ apply (a11m_cx B n v pos (p_ly v) Sc Wc rX memc mdc cf nm o ln d gi vp val Sc Wc (ms_regs ms) (ms_mem ms) mdv HCX HJ).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - exact HK1.
  - exact M1.
  - exact HRG1.
  - exact HFSH1. }
pose proof CX1 as (HB1 & _ & _ & _ & _ & _).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB1) as (HAR1 & _ & Hin1 & _ & Hfp1 & _).
pose proof HB1 as (_ & _ & HOBJ1 & _ & _).
pose proof HOBJ1 as (_ & _ & _ & _ & _ & HCAT1 & _ & HROD1 & _).
destruct (a5_chain B _ _ _ _ _ _ _ _ _ HB1) as (ch1 & Hch).
(* by_token's premise: the folded value is a C string in low146 *)
assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) (pf_F v pos + PF_O_L146) (r_low val 0 24)).
{ apply (zm_low_str _ v pos val li G Hnf HLI).
  - intros j Hj. unfold PF_O_L146 in *. rewrite KM1; [exact (HLOW j Hj) | lia | lia].
  - exact HW0.
  - intros x Hx. apply (aview_some_of_apresent SEGS). apply Hfp1. exact Hx. }
assert (HBTP : by_token_pre SEGS B (p_ly v) Sc (rdW Wc (ms_mem ms)) catA (pf_F v pos + PF_O_L146) (r_low val 0 24)).
{ split; [unfold PF_O_L146; lia|].
  split; [exact HSTR1|].
  split; [exact (zm_low_addr v pos (p_ly v) Sc Wc (ms_mem ms) mdv (Z.of_nat (length (r_low val 0 24)) + 1) G HAR1
    Hin1 eq_refl HFSH1 ltac:(lia))|].
  split; [right; left; exists 5, pos; split; [exact Hin1|]; split; [lia|];
          change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); change (fs_frame_bytes 5) with 2048;
          unfold PF_O_L146; lia|].
  split; [lia | exact HCAT1]. }
assert (HEV : st_nev Sc + EV_reac_box_catalogue_by_token <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HCXp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEVp).
  unfold EV_reac_box_catalogue_by_token, EV_reac_segconf_parse_file in *. lia. }
assert (Hsp1 : spZ (ms_regs ms) = pf_s1 v) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
rewrite (SIGP SS_reac_box_catalogue_by_token
  ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_box_catalogue_by_token) with AF_reac_box_catalogue_by_token by (vm_compute; reflexivity).
(* ---- 0x88538: jal reac_box_catalogue_by_token (a0 = low146), returning at 0x8853c ---- *)
eapply SRr_bind.
{ eapply (cl_callS (fx := fx) B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc mdv 0
    STK_reac_box_catalogue_by_token [] EV_reac_box_catalogue_by_token (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + A11_RET_BT)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (seg_spec.cat_ptr catA (by_token (r_low val 0 24))) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) STK_reac_box_catalogue_by_token (fun _ => False) /\
       sa_noalloc B (p_ly v) Sc ly2 S2) HJ).
  - rewrite Hsp1. lia.
  - rewrite Zminus_mod, Hs16, G3. reflexivity.
  - lia.
  - unfold STK_reac_box_catalogue_by_token, STK_fuzz_catalogue_row, ESTACK. lia.
  - unfold STK_reac_box_catalogue_by_token, STK_fuzz_catalogue_row, ESTACK. rewrite SPF. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [change A11_RET_BT with 14344; lia | reflexivity].
  - rewrite unsigned_lit_small by (change A11_RET_BT with 14344; lia). change A11_RET_BT with 14344. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    replace (s0Z (ms_regs ms)) with (pf_sp0 v)
      by (unfold s0Z; rewrite Q8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    exact Hch.
  - intros HPRE1. eapply SRr_mono.
    { exact (BT fx (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 (pf_F v pos + PF_O_L146) (r_low val 0 24) HPRE1
        HROD1 Q10 ltac:(unfold PF_O_L146; lia) HBTP HEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Ha02 & Hkept2 & HNA2)).
destruct HNA2 as (HPm2 & Hly2 & (f2 & HS2e)). subst ly2.
replace (0 + EV_reac_box_catalogue_by_token) with 0 in HJ2 by (unfold EV_reac_box_catalogue_by_token; lia).
(* what the call kept: every byte outside its window [s1 - 8256, s1); the window stays present *)
assert (Hstk1 : STK_reac_box_catalogue_by_token = 8256) by reflexivity.
assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 8256 <= a < pf_s1 v) -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hn. apply (Hkept2 a Ha); [rewrite Hsp1, Hstk1; exact Hn | tauto]. }
assert (M12 : forall a, rdW Wc (ms_mem ms) a <> None -> rdW W2 mem2 a <> None).
{ intros a Hv. rewrite zm_aview_wrap. rewrite zm_aview_wrap in Hv.
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  destruct (Z_le_gt_dec (pf_s1 v - 8256) (a mod 2 ^ 64)) as [L1 | L1];
    [destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_s1 v)) as [L2 | L2]|].
  - pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
    apply (aview_some_of_apresent SEGS). apply Hpr. rewrite ?Hsp1, Hstk1. lia.
  - rewrite K12; [exact Hv | lia | lia].
  - rewrite K12; [exact Hv | lia | lia]. }
(* ---- 0x8853c: beqz a0, from a fresh seed at the return ---- *)
assert (HS2 : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) zb_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A11_RET_BT)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold zb_ss. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (EE2 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (Eimg (Ereg regs2 [])) n0 = getr regs2 r)
  by (intros n0 r Hn0; apply ew_Eimg_Ereg_nat; exact Hn0).
revert HS2 HEI2 EE2. generalize (Eimg (Ereg regs2 [])) as E2. intros E2 HS2 HEI2 EE2.
assert (SHOK2 : sh_ok SEGS zm_Bx [] E2 (mrestrict (w_H W2) mem2)) by constructor.
assert (E10 : ew E2 10 = Z_to_bv 64 (seg_spec.cat_ptr catA (by_token (r_low val 0 24)))).
{ rewrite (EE2 10%nat (Z_to_bv 5 10) eq_refl), (zm_getz regs2 10 10 eq_refl). exact Ha02. }
assert (Hrng : 0 <= seg_spec.cat_ptr catA (by_token (r_low val 0 24)) < 2 ^ 64).
{ destruct (by_token (r_low val 0 24)) as [i|] eqn:Hbt; cbn [seg_spec.cat_ptr]; [|lia].
  pose proof (a11f_by_token_lt _ _ Hbt). unfold catA, pin_spec.CAT_ROW. lia. }
psrr_branch_tok RUN BR HS2 SHOK2 Bspan.
- (* a0 = 0: no row; MISS 0x885a8 *)
  pose proof (zm_br_eq0 _ 10 _ _ E10 Hrng Hc) as L0. apply Z.eqb_eq in L0. clear Hc.
  destruct (by_token (r_low val 0 24)) as [i|] eqn:Hbt.
  { exfalso. rewrite ?Hbt in L0. cbn [seg_spec.cat_ptr] in L0. unfold catA, pin_spec.CAT_ROW in L0. lia. }
  unfold a11_post, a11_step. rewrite Hbt.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan PF_MISS.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    apply awr_ok_nil. }
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  assert (K23 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem2 (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  assert (M23 : forall a, rdW W2 mem2 a <> None -> rdW W2 (ms_mem ms0) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H W2) mem2 (ms_mem ms0) a HG Hv)).
  clear HF HFr HG.
  assert (HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ a11m_X v pos a -> rdW W2 (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha Hn. rewrite (K23 a Ha). apply K12; [exact Ha|]. intros Hw. apply Hn. left. rewrite SPF. lia. }
  assert (HV3 : forall a, rdW Wc (ms_mem ms) a <> None -> rdW W2 (ms_mem ms0) a <> None)
    by (intros a Hv; apply M23; apply M12; exact Hv).
  assert (HFSH3 : pf_fsh (rdW W2 (ms_mem ms0)) (pf_SH v pos) PF_SC_L146).
  { intros i Hi. unfold kLowMemEnd, kHighShadowEnd in G11, G12.
    rewrite (K23 (pf_SH v pos + i) ltac:(lia)), K12; [exact (HFSH1 i Hi) | lia | lia]. }
  assert (QF : forall r x, In (r, x) (a5_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++ [(20, pf_F v pos + PF_O_L146); (25, vp)]) ->
    getr (ms_regs ms0) (Z_to_bv 5 r) = w64 x).
  { intros r x Hr. pose proof (QR r x Hr) as Hq. unfold a5_FI, PF_RL, PF_RM in Hr. cbn [In app] in Hr.
    repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-;
      lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
        zm_rreg HS2; rewrite zm_den0;
        lazymatch goal with |- ew _ ?nn = _ => rewrite (EE2 nn (Z_to_bv 5 k) eq_refl) end;
        rewrite (HP2 k ltac:(unfold acallee_saved; lia)); exact Hq end |]).
    destruct Hr. }
  assert (HRG3 : pf_rg (ms_regs ms0) (a5_FI B v)).
  { unfold pf_rg. rewrite Forall_forall. intros [r x] Hx. apply QF. apply in_or_app. left. exact Hx. }
  pose proof (a11m_cx B n v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S2 W2 (ms_regs ms0)
    (ms_mem ms0) mdv2 CX1 HJ2 (ex_intro _ f2 HS2e) HPm2 HK3 HV3 HRG3 HFSH3) as CX3.
  pmkst HS2.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    change (Z_to_bv 64 (BASE + k)) with (w64 (BASE + PF_MISS)) end.
  apply (HMISS fx v pos (p_ly v) S2 W2 (ms_regs ms0) (ms_mem ms0) mdv2 cf nm o ln d gi vp val).
  destruct CX3 as (HB3 & HM3 & HST3 & HV3' & HIB3 & HSL3).
  split; [exact HB3|]. split; [exact HM3|]. split; [exact HST3|]. split; [exact HV3'|]. split; [exact HIB3|].
  split; [exact Hbt|]. split; [exact HSL3|].
  unfold pf_rg. rewrite Forall_forall. intros [r x] Hx. apply QF. apply in_or_app. right.
  apply in_app_or in Hx as [Hx | Hx]; [apply in_or_app; left; exact Hx | apply in_or_app; right].
  apply in_app_or in Hx as [Hx | Hx]; [apply in_or_app; left; exact Hx | apply in_or_app; right].
  destruct Hx as [Hx | []]. rewrite <- Hx. right. left. reflexivity.
- (* a0 <> 0: row i; HIT 0x88540 *)
  pose proof (zm_br_eq0 _ 10 _ _ E10 Hrng Hc) as L0. apply Z.eqb_neq in L0. clear Hc.
  destruct (by_token (r_low val 0 24)) as [i|] eqn:Hbt.
  2: { exfalso. rewrite ?Hbt in L0. apply L0. reflexivity. }
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan A11_HIT.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    apply awr_ok_nil. }
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  assert (K23 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem2 (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  assert (M23 : forall a, rdW W2 mem2 a <> None -> rdW W2 (ms_mem ms0) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H W2) mem2 (ms_mem ms0) a HG Hv)).
  clear HF HFr HG.
  assert (HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ a11m_X v pos a -> rdW W2 (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha Hn. rewrite (K23 a Ha). apply K12; [exact Ha|]. intros Hw. apply Hn. left. rewrite SPF. lia. }
  assert (HV3 : forall a, rdW Wc (ms_mem ms) a <> None -> rdW W2 (ms_mem ms0) a <> None)
    by (intros a Hv; apply M23; apply M12; exact Hv).
  assert (HFSH3 : pf_fsh (rdW W2 (ms_mem ms0)) (pf_SH v pos) PF_SC_L146).
  { intros j Hj. unfold kLowMemEnd, kHighShadowEnd in G11, G12.
    rewrite (K23 (pf_SH v pos + j) ltac:(lia)), K12; [exact (HFSH1 j Hj) | lia | lia]. }
  assert (QF : forall r x, In (r, x) (a5_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++ [(20, pf_F v pos + PF_O_L146); (25, vp)]) ->
    getr (ms_regs ms0) (Z_to_bv 5 r) = w64 x).
  { intros r x Hr. pose proof (QR r x Hr) as Hq. unfold a5_FI, PF_RL, PF_RM in Hr. cbn [In app] in Hr.
    repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-;
      lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
        zm_rreg HS2; rewrite zm_den0;
        lazymatch goal with |- ew _ ?nn = _ => rewrite (EE2 nn (Z_to_bv 5 k) eq_refl) end;
        rewrite (HP2 k ltac:(unfold acallee_saved; lia)); exact Hq end |]).
    destruct Hr. }
  assert (HRG3 : pf_rg (ms_regs ms0) (a5_FI B v)).
  { unfold pf_rg. rewrite Forall_forall. intros [r x] Hx. apply QF. apply in_or_app. left. exact Hx. }
  pose proof (a11m_cx B n v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val S2 W2 (ms_regs ms0)
    (ms_mem ms0) mdv2 CX1 HJ2 (ex_intro _ f2 HS2e) HPm2 HK3 HV3 HRG3 HFSH3) as CX3.
  (* the folded value, a C string in low146, kept by the call (it lies below alloc_ceiling) *)
  assert (HSTR3 : sa_str (rdW W2 (ms_mem ms0)) (pf_F v pos + PF_O_L146) (r_low val 0 24)).
  { destruct HSTR1 as ((Hz & Hn0) & Ht). split; [split; [|exact Hn0]|].
    - intros j Hj. pose proof Hj as Hj'. rewrite length_app in Hj'. cbn [length] in Hj'.
      unfold PF_O_L146 in *. rewrite (K23 (pf_F v pos + 736 + Z.of_nat j) ltac:(lia)), K12;
        [exact (Hz j Hj) | lia | lia].
    - intros x Hx. apply M23. apply M12. exact (Ht x Hx). }
  pmkst HS2.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
    change (Z_to_bv 64 (BASE + k)) with (w64 (BASE + A11_HIT)) end.
  apply (HHIT v pos (p_ly v) S2 W2 (ms_regs ms0) (ms_mem ms0) mdv2 cf nm o ln d gi vp val i).
  split; [exact CX3|]. split; [exact Hbt|]. split; [exact HSTR3|].
  unfold pf_rg. rewrite Forall_forall. intros [r x] Hx.
  apply in_app_or in Hx as [Hx | Hx].
  { apply QF. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  apply in_app_or in Hx as [Hx | Hx].
  { apply QF. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  destruct Hx as [Hx | Hx].
  + injection Hx as <- <-. zm_rreg HS2. rewrite zm_den0, E10, ?Hbt. reflexivity.
  + apply QF. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.
End e.
End f.
End d.
