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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 530 of its 593 lines of code are new or changed and 4990 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the RS1 cut of segment
   B11a of reac_segconf_parse_file's walk, b11_rs1_ok : HA_LOWOUT n -> B11_RS1_stmt n (lib/B/Prog/pf_seg_B11a_k.v,
   lib/B/Prog/pf_pieces.v). The B11a segment lane of the image-B G3 walk owner, 2026-10-30 (a sub-lane).
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, B11a's RS1 cut: the model_set store, the
   second snprintf, LOWOUT).
   WHAT IT PROVES. From the state at the return of snprintf(cur->model, 24, "%s", low) (0x88a08, INV_RS1: c holds
   b11_cf1 cf gi val, s3 = cur = &c->seg[gi], by_token's hit) the walk reaches the post of the model step's hit branch
   (b11_post = pf_postm of r_upd cf gi (rs_with_model (snprintf_s 24 F_s [AS low]) (snprintf_s 96 F_s [AS reading])))
   through LOWOUT (0x88c70), given H_LOWOUT at every FP state.
   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), every instruction this file walks:
     0x88a08 mv a3,s3; 0x88a0c addi a0,s3,60; 0x88a10 srli a1,a0,3; 0x88a14 add a1,a1,s4; 0x88a18 lb a1,0(a1);
     0x88a1c bnez a1 -> 0x89034                      check B#27 (store4 at cur + 60, cur->model_set)
     0x88a20 li a0,1; 0x88a24 sw a0,60(a3)           cur->model_set = 1
     0x88a28 addi a0,a3,64; 0x88a2c auipc / 0x88a30 addi a2 = 0x21340 "%s"; 0x88a34 li a1,96;
     0x88a38 ld a3,72(s1) (slot 0x48 = &c->reading); 0x88a3c jal wrapper_snprintf (0x43af0)
     0x88a40 li a0,-8; 0x88a44 j 0x88c70 (LOWOUT)
   The first fourteen are one token run of the symbolic executor (seed b11t_ss: every register its own atom, the slot
   0x48 chunk on s1's atom, a writable region [60, 64) on cur's atom 19 with the fact PTR 2, the shadow entry
   mkSHE 19 60 64); the call is RtFormat.asnprintf_realizes (Section hypothesis ASNPRINTF) through pf_seg_B11a_t_s.v's
   b11ts_aj_snprintf_atSF, and the last two are a plain run at the FP state snprintf returns.
   THE CHECK. B#27 (0x88a1c, slow arm 0x89034-0x89040, error call 0x892a8 errpath_store4): the run's shadow entry
   mkSHE 19 60 64 covers it, so it makes no obligation; the entry holds by YCbq.shent_ok_of_range from pf_obj's
   sa_addr c SEG_C_SIZE (cur + 60 lies in c's table since gi < 32, rconf_enc's bound). The slow arm and its error
   call are not reached. No UBSan trap lies in these instructions.
   THE CALL. snprintf(cur + 64, 96, "%s", c->reading): the format is pf_obj's sa_lit F_s at seg_litA_rc F_s = 0x21340
   (pf_pieces.pf_B_values; the run's a2 is the listing object atom A_OBJ 35, Section hypothesis VO); the argument is
   c->reading, an sa_str from sa_rconf's reading field (seg_spec.rconf_enc: cstr_enc 96 at RC_READING), its shadow and
   amem from the live block c; the text T = rc_reading cf has |T| < 96, so snprintf writes T and its NUL and
   snprintf_s 96 F_s [AS T] = T (SegModel.snprintf_s1). The destination lies in the block c and in RC_PARSE_W c's first
   range; the read-only view and the stack-protector cells are pf_obj's, carried over the store by the keep lemmas of
   pf_seg_B11a_g.v (no sa_ssp-at-every-state hypothesis); the rounding mode is pf_fi's sa_frm0.
   THE CUT REBUILT. At LOWOUT (FP state fx1): pf_base by b11t_base_fx (the cut's pf_base with the rounding mode of fx1,
   PaFx.fxrel_frm0) then b11_move at fx1 (write set b11_Wr with cw = b11_cw v gi: the store
   [cur + 60, cur + 64), the text [cur + 64, cur + 65 + |T|), snprintf's window [s1 - 8192, s1)); pf_mid unchanged;
   pf_st with c holding r_upd cf gi (rs_with_model m T) by pf_seg_B11a_f.v's b11f_rconf_model (the model field already
   holds m in b11_cf1, model_set holds le4 1, model_file T, NUL and the old bytes) and b11ts_cf1_model; the counters'
   room at the next line by pfA_facts.pf_cnt_mono / pf_next_skipn_lt; registers PF_RL ++ PF_RM ++ [(10, -8)].
   ADAPTED from a working branch + U piece walks; templates a lane clone
   lib/B/Prog/pf_seg_B3_p1.v (the B3 segment lane, f5fd160e1686: seed with a slot chunk, token run to the snprintf call, the
   call through the journal), a lane clone lib/B/Prog/pf_seg_B8b_s.v (the B8b segment lane,
   0207861118e1: the snprintf of c->reading into an entry's file field, the return's plain run, the cut at the callee's
   FP state), a lane clone lib/B/Prog/pf_seg_B11a_m.v (the B11a segment lane, db5280e50cc6: regions
   read back, b11_move), a lane clone lib/B/Prog/pf_seg_B11a_h.v (the B11a segment lane,
   b11h_base_fx), lib/B/Prog/trim_f.v (shent_ok_of_range). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11a_k pf_seg_B11a_g
  pf_seg_B11a_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B11a_t_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B11a_m.v's, pf_seg_B8b_s.v's) ---------- *)
Lemma b11t_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b11t_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v ->
  getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b11t_set_fs_id : forall s, set_fs (st_fs s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Ltac b11t_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac b11t_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* the 4 bytes of 1 as cur->model_set's int: seg_spec.flag_enc true *)
Lemma b11t_le4_1 : forall i, (i < 4)%nat ->
  bv_unsigned (nth i (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4 (Z_to_bv 64 1)) ZB0) =
  bv_unsigned (byte_of_word (Z_to_bv 64 1) (Z.of_nat i)).
Proof. intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.
(* a C string kept: its bytes and NUL read the same, every visible byte stays visible *)
Lemma b11t_str_keep : forall (rd rd' : reader) p s,
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> (forall x, rd x <> None -> rd' x <> None) ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s K V [[Hz Hn] Ht]. split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'. rewrite K by lia. exact (Hz i Hi).
- intros x Hx. exact (V x (Ht x Hx)).
Qed.

(* ---------- the seeds ---------- *)
(* RS1 (0x88a08): every register its own atom, atom 32 = slot 0x48's value (&c->reading); slot 0x48 read-only on
   s1's atom; cur->model_set [cur + 60, cur + 64) writable on s3's atom 19 *)
Definition b11t_r0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x48 0x50 0 0 [YP09.mkChunk 0x48 (CVal 8 (SOff 32 0))].
Definition b11t_r1 : YP09.region := YP09.mkRegion (Some 19%nat) 60 64 60 64 [].
Definition b11t_ss : sstate := mkSS B11_RET_SN1 sr_atoms [b11t_r0; b11t_r1] None
  (mkFacts [(19%nat, PTR 2); (32%nat, PTR 0); (20%nat, mkAF SB SB 0)] [] []).
Definition b11t_SH : list shent := [mkSHE 19 60 64].
(* the return 0x88a40: every register its own atom, no region *)
Definition b11t_ss2 : sstate := mkSS B11_RET_SN2 sr_atoms [] None (mkFacts [] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* pf_pieces.v's hypotheses for B11a's snprintf, and the listing's object atoms (B's SegObj) *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis VO : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the snprintf arguments at 0x88a3c *)
Definition b11t_ARGS (v : pfv) (gi : nat) : list (Z * Z) :=
  [(10, seg_spec.rseg_addr (p_c v) gi + 64); (11, 96); (12, seg_litA_rc F_s); (13, p_c v + seg_spec.RC_READING)].
Ltac b11t_in := cbv [PF_RL PF_RM PF_SL b11_FI b11t_ARGS app]; cbn [In]; repeat first [left; reflexivity | right].

Lemma b11t_obj35 : forall E, img_env VAL A_LIM E -> ew E 276%nat = w64 (seg_litA_rc F_s).
Proof.
intros E HE. rewrite (img_env_atomP E 276%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 276%nat with (A_OBJ 35). rewrite (VO 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* the 4 bytes of a CVal 4 (SLit z) chunk a run left in a region *)
Lemma b11t_word4_of_region : forall E H m n b lo hi wlo whi cs od z,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 (SLit z))) cs ->
  forall i, 0 <= i < 4 -> aview SEGS H m (b + od + i) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) i)).
Proof.
intros E H m n b lo hi wlo whi cs od z HR Hb Hin i Hi.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck i ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb in Hb2.
unfold aview. rewrite Hb2. reflexivity.
Qed.

(* a register of the token run's state at the call (pf_seg_B3_p1.v pb3_regq) *)
Ltac b11t_regq HS EE E32 HEI U19 RG1 RG2 :=
  lazymatch goal with |- getr (ms_regs ?ms) (Z_to_bv 5 ?k) = _ =>
    let Rk := fresh "Rk" in prreg HS (Z_to_bv 5 k) Rk; rewrite Rk; clear Rk end;
  first
  [ exact (b11t_obj35 _ HEI)
  | reflexivity
  | rewrite E32; reflexivity
  | rewrite U19; reflexivity
  | lazymatch goal with |- ew _ ?n = _ => let z := eval cbv in (Z.of_nat n) in rewrite (EE n (Z_to_bv 5 z) eq_refl) end;
    first [apply (b11_rg_get _ _ _ _ RG1); solve [b11t_in] | apply (b11_rg_get _ _ _ _ RG2); solve [b11t_in]] ].
(* a register at LOWOUT: kept by the plain run, callee-saved over snprintf, one of the call state's *)
Ltac b11t_kreg QK3 HP2 QR :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = _ =>
    rewrite (QK3 r ltac:(cbn [In]; repeat first [left; reflexivity | right]));
    rewrite (HP2 r) by (unfold acallee_saved; lia);
    apply (b11_rg_get _ _ _ _ QR); b11t_in end.

(* pf_base at another FP state: its only FP conjunct is pf_fi's rounding mode (pf_seg_B11a_h.v b11h_base_fx) *)
Lemma b11t_base_fx : forall (fa fb : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc,
  pf_base (fx := fa) B v pos lyc Sc Wc rX memc mdc sc -> sa_frm0 (fx := fb) ->
  pf_base (fx := fb) B v pos lyc Sc Wc rX memc mdc sc.
Proof.
intros fa fb v pos lyc Sc Wc rX memc mdc sc (HCX & (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8 & H9 & H10) & HO & HS & HF) Hf.
exact (conj HCX (conj (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj Hf (conj H8 (conj H9 H10)))))))))
  (conj HO (conj HS HF)))).
Qed.

Section x. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.

(* ---------- the seed at RS1 (0x88a08) ---------- *)
Lemma b11t_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 cur r48,
  getr rX (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 0x50 <= 2 ^ 64 ->
  getr rX (Z_to_bv 5 19) = w64 cur -> 4096 <= cur -> cur + 64 <= 140737479966720 -> cur mod 4 = 0 ->
  getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF ->
  rdword (rdW Wc memc) (s1 + 0x48) = Some r48 -> 4096 <= r48 <= 140737479966720 ->
  (forall a, cur + 60 <= a < cur + 64 -> apresent (w_H Wc) memc a) ->
  (s1 + 0x50 <= cur + 60 \/ cur + 64 <= s1 + 0x48) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 r48])) b11t_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B11_RET_SN1)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 cur r48 R9 H0 H1 R19 Hc1 Hc2 Hc4 R20 Hw Hr Hpr Hdj.
set (E := Eimg (Ereg rX [w64 r48])).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = cur)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 19 (Z_to_bv 5 19) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 20 (Z_to_bv 5 20) eq_refl), R20; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 r48) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U32 : bv_unsigned (ew E 32) = r48) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b11t_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, b11t_r0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|constructor].
    apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x48 8 (SOff 32 0) r48).
    * rewrite b11t_den_atom0, E32. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact Hw.
  + unfold region_ok, b11t_r1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpr. lia.
- cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint, b11t_r0, b11t_r1. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok].
  unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite U19, U32, U20.
  unfold SB, SHADOW_OFF. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia.
Qed.

(* ---------- the token run RS1 (0x88a08) -> the snprintf call (0x88a3c) ---------- *)
Lemma b11t_run1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (Q : world SEGS -> config -> Prop),
  INV_RS1 B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  (forall regsT memT mdT,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (seg_spec.rseg_addr (p_c v) gi + 60 <= a < seg_spec.rseg_addr (p_c v) gi + 64) ->
        rdW Wc memT a = rdW Wc memc a) ->
     (forall a, rdW Wc memc a <> None -> rdW Wc memT a <> None) ->
     (forall i, 0 <= i < 4 -> rdW Wc memT (seg_spec.rseg_addr (p_c v) gi + 60 + i) =
        Some (bv_unsigned (byte_of_word (Z_to_bv 64 1) i))) ->
     pf_rg regsT (b11t_ARGS v gi ++ b11_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++
                  [(19, seg_spec.rseg_addr (p_c v) gi)]) ->
     getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B11_RET_SN2) ->
     SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS))
       mdT) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_RET_SN1) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Q HI Kc.
destruct HI as (HCX & _ & HRG).
destruct HCX as (HBASE & HMID & HST & _).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HBASE) as (HGe & Hin & EF & Hfrs & HAR & Hly & _).
pose proof HGe as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5 & C16 & C4 & Cc & Capp & Cdj & _).
pose proof HBASE as (_ & HFI & HOBJ & HSL & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof HOBJ as (_ & _ & _ & HCA & HCH & _).
destruct HCH as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & _ & HbcP & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrq].
pose proof asan_consts as (AC1 & _).
destruct HST as (HRC & HCUR & _).
assert (Hgi : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & Hn32 & _)); cbn [pf_cur_ok] in HCUR; lia).
assert (Hcur : seg_spec.rseg_addr (p_c v) gi = p_c v + 356 * Z.of_nat gi) by reflexivity.
assert (ESZ : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ERD : seg_spec.RC_READING = 0x4080) by reflexivity.
assert (ERN : seg_spec.RC_N = 0x2c80) by reflexivity.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b11_rg_get rX _ 9 _ HRG0); b11t_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (seg_spec.rseg_addr (p_c v) gi))
  by (apply (b11_rg_get rX _ 19 _ HRG); b11t_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b11_rg_get rX _ 20 _ HRG0); b11t_in).
assert (Hw48 : rdword (rdW Wc memc) (pf_s1 v + 0x48) = Some (p_c v + seg_spec.RC_READING))
  by (apply (b11_slot_get _ _ _ 0x48 _ HSL); b11t_in).
pose proof (b11t_seed Wc rX memc (pf_s1 v) (seg_spec.rseg_addr (p_c v) gi) (p_c v + seg_spec.RC_READING)
  R9 ltac:(lia) ltac:(lia) R19 ltac:(lia) ltac:(lia) ltac:(lia) R20 Hw48 ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HbcP a ltac:(lia)))) ltac:(lia)) as HS.
set (E0 := Eimg (Ereg rX [w64 (p_c v + seg_spec.RC_READING)])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E0 k = getr rX r)
  by (intros k r Hk; unfold E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E0 32 = w64 (p_c v + seg_spec.RC_READING))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U19 : bv_unsigned (ew E0 19) = seg_spec.rseg_addr (p_c v) gi)
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
clearbody E0.
(* check B#27's shadow entry: cur->model_set lies in the block c, whose shadow sa_addr c SEG_C_SIZE gives *)
assert (SHOK : sh_ok SEGS (SOff 20 0) b11t_SH E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b11t_SH. apply Forall_cons; [|apply Forall_nil].
  pose proof HCA as (_ & _ & _ & HRAc & _).
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 (SOff 20 0) 19%nat (p_c v) seg_spec.SEG_C_SIZE
    (seg_spec.rseg_addr (p_c v) gi) 60 64 HRAc).
  - unfold U. rewrite b11t_den_atom0. exact U20.
  - unfold U. rewrite b11t_den_atom0. exact U19.
  - lia.
  - lia.
  - intros x Hx. change (Z.min 60 64) with 60 in Hx. change (Z.max 60 64) with 64 in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B11_RET_SN1)) with (Z_to_bv 64 (BASE + B11_RET_SN1)).
(* 0x88a08 .. 0x88a3c: check B#27 covered, sw 1 -> cur->model_set, the snprintf arguments, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bcl ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bcl fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U19 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [unfold seg_spec.RC_PARSE_W; left; reflexivity|].
    cbn [fst snd]. lia.
  - exists bc, mc. split; [exact Hbc | lia]. }
b11t_clear_md.
assert (KM : forall a, 0 <= a < 2 ^ 64 ->
    ~ (seg_spec.rseg_addr (p_c v) gi + 60 <= a < seg_spec.rseg_addr (p_c v) gi + 64) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms)
    (fun a => seg_spec.rseg_addr (p_c v) gi + 60 <= a < seg_spec.rseg_addr (p_c v) gi + 64) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U19 in Hrr; lia |]).
  destruct Hin'. }
assert (MV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
(* cur->model_set read back from the run's region *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth (segs := SEGS) Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity))
    as HR1;
  assert (U19x : bv_unsigned (ew Ex 19) = seg_spec.rseg_addr (p_c v) gi)
    by (first [exact U19 | cbn [ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
         repeat (rewrite ew_havoc_old; [|cbv; lia]); repeat (rewrite ew_ewset_other; [|lia]); exact U19])
end.
cbn [ms_mem restrict] in HR1.
assert (W4 : forall i, 0 <= i < 4 -> rdW Wc (ms_mem ms) (seg_spec.rseg_addr (p_c v) gi + 60 + i) =
    Some (bv_unsigned (byte_of_word (Z_to_bv 64 1) i))).
{ intros i Hi. exact (b11t_word4_of_region _ (w_H Wc) (ms_mem ms) 19 _ 60 64 60 64 _ 60 1 HR1 U19x
    ltac:(left; reflexivity) i Hi). }
(* the registers at the call *)
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B11_RET_SN2))
  by (prreg HS (Z_to_bv 5 1) R1; rewrite R1; reflexivity).
assert (QR : pf_rg (ms_regs ms) (b11t_ARGS v gi ++ b11_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++
    [(19, seg_spec.rseg_addr (p_c v) gi)])).
{ unfold pf_rg, b11t_ARGS, b11_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil];
    cbn [fst snd]; b11t_regq HS EE E32 HEI U19 HRG0 HRG. }
pmkst HS.
exact (Kc _ _ _ HJ KM MV W4 QR Q1).
Qed.

(* ---------- the snprintf at 0x88a3c, the return 0x88a40 .. 0x88a44, LOWOUT ---------- *)
Lemma b11t_call2 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regsT memT mdT,
  HA_LOWOUT B n ->
  INV_RS1 B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (seg_spec.rseg_addr (p_c v) gi + 60 <= a < seg_spec.rseg_addr (p_c v) gi + 64) ->
     rdW Wc memT a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memT a <> None) ->
  (forall i, 0 <= i < 4 -> rdW Wc memT (seg_spec.rseg_addr (p_c v) gi + 60 + i) =
     Some (bv_unsigned (byte_of_word (Z_to_bv 64 1) i))) ->
  pf_rg regsT (b11t_ARGS v gi ++ b11_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++
               [(19, seg_spec.rseg_addr (p_c v) gi)]) ->
  getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B11_RET_SN2) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT)
    (b11_post B v cf gi nm val o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regsT memT mdT LOWOUT HI HJT KMT MVT W4 QR Q1.
destruct HI as (HCX & (i0 & Hi0) & HRG).
destruct HCX as (HBASE & HMID & HST & _).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HBASE) as (HGe & Hin & EF & Hfrs & HAR & Hly & _).
pose proof HGe as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5 & C16 & C4 & Cc & Capp & Cdj & _ & Coff).
pose proof HBASE as (_ & HFI & HOBJ & _ & HFSH).
pose proof HFI as (_ & _ & _ & _ & _ & _ & HFRM & _).
pose proof HOBJ as (_ & _ & _ & _ & HCH & _).
destruct HCH as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrq].
pose proof HJT as (HART & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc memT mdT bc mc HART Hbc) as (_ & _ & _ & _ & HbcPT & _ & _).
pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof pf_B_values as (_ & _ & _ & Egw & Egd & _ & _ & _ & _ & _ & EFs).
destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
assert (Hgi' : (gi < length (rc_seg (b11_cf1 cf gi val)))%nat) by exact HCUR.
assert (Hgi : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & Hn32 & _)); lia).
assert (Hgic : (gi < length (rc_seg cf))%nat) by (unfold b11_cf1 in Hgi'; rewrite b11f_upd_len in Hgi'; exact Hgi').
assert (Hcur : seg_spec.rseg_addr (p_c v) gi = p_c v + 356 * Z.of_nat gi) by reflexivity.
assert (ESZ : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ERD : seg_spec.RC_READING = 0x4080) by reflexivity.
assert (ERN : seg_spec.RC_N = 0x2c80) by reflexivity.
assert (Hcw : b11_cw_ok v (b11_cw v gi)) by exact (b11_cw_ok_gi v gi Hgi).
(* the post: by_token's hit; snprintf(cur->model_file, 96, "%s", c->reading) writes the reading itself *)
unfold b11_post, b11_step. rewrite Hi0. cbv beta iota.
set (T := rc_reading cf).
pose proof (b11ts_reading_str (rdW Wc memc) (p_c v) (b11_cf1 cf gi val) HRC ltac:(lia)) as HSTR0.
change (rc_reading (b11_cf1 cf gi val)) with T in HSTR0.
pose proof (b11ts_reading_rng (rdW Wc memc) (p_c v) (b11_cf1 cf gi val) HRC) as HTr.
change (rc_reading (b11_cf1 cf gi val)) with T in HTr.
assert (HTl : (length T < 96)%nat)
  by (destruct HRC as (bs & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hl & _) & _)); exact Hl).
assert (HTn : ~ In 0 T) by (destruct HSTR0 as ((_ & Hn) & _); exact Hn).
rewrite (snprintf_s1 96 T HTn) by lia.
(* the registers at the call *)
assert (Q10 : getr regsT 10 = w64 (seg_spec.rseg_addr (p_c v) gi + 64))
  by (apply (b11t_bvr _ _ 10); [reflexivity | apply (b11_rg_get _ _ _ _ QR); b11t_in]).
assert (Q11 : getr regsT 11 = w64 96)
  by (apply (b11t_bvr _ _ 11); [reflexivity | apply (b11_rg_get _ _ _ _ QR); b11t_in]).
assert (Q12 : getr regsT 12 = w64 (seg_litA_rc F_s))
  by (apply (b11t_bvr _ _ 12); [reflexivity | apply (b11_rg_get _ _ _ _ QR); b11t_in]).
assert (Q2 : getr regsT 2 = w64 (pf_s1 v))
  by (apply (b11t_bvr _ _ 2); [reflexivity | apply (b11_rg_get _ _ _ _ QR); b11t_in]).
assert (Q3 : getr regsT 3 = w64 (as_gp B))
  by (apply (b11t_bvr _ _ 3); [reflexivity | apply (b11_rg_get _ _ _ _ QR); b11t_in]).
assert (Q4 : getr regsT 4 = w64 (as_tp B))
  by (apply (b11t_bvr _ _ 4); [reflexivity | apply (b11_rg_get _ _ _ _ QR); b11t_in]).
assert (Q1' : getr regsT 1 = Z_to_bv 64 (BASE + B11_RET_SN2)) by (apply (b11t_bvr _ _ 1); [reflexivity | exact Q1]).
assert (Hsp : spZ regsT = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* the cut's objects at the call's reader: the run wrote cur->model_set only *)
assert (KT : b11_kept v pos false (b11_cw v gi) (rdW Wc memc) (rdW Wc memT)).
{ split.
  - intros a Ha Hn. apply KMT; [exact Ha|]. intros Hw. apply Hn. unfold b11_Wr. right; right; right.
    cbv [b11_cw seg_spec.RS_MODEL]. lia.
  - intros a _ Hv. exact (MVT a Hv). }
pose proof (b11_keep_obj B v pos lyc Sc Wc memc mdc false (b11_cw v gi) _ _ HGe HAR Hin EF Hcw KT HOBJ) as HOBJT.
pose proof HOBJT as (_ & _ & _ & _ & _ & _ & T7 & T8 & T9).
assert (FMT : sa_lit SEGS B (rdW Wc memT) (seg_litA_rc F_s) F_s)
  by (apply T7; unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity).
(* the argument c->reading at the call's reader *)
assert (HSTRT : sa_str (rdW Wc memT) (p_c v + seg_spec.RC_READING) T).
{ apply (b11t_str_keep (rdW Wc memc) (rdW Wc memT) _ T); [| exact MVT | exact HSTR0].
  intros x Hx. apply KMT; lia. }
assert (HSAT : sa_addr (rdW Wc memT) (p_c v + seg_spec.RC_READING) (Z.of_nat (length T) + 1)).
{ split; [lia|]. split; [lia|].
  split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length T) + 1) HART Hbc ltac:(lia) ltac:(lia))|].
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length T) + 1) HART Hbc ltac:(lia) ltac:(lia))|].
  intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length T) + 1) HART Hbc ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (HSAM : amem_range (p_c v + seg_spec.RC_READING) (Z.of_nat (length T) + 8))
  by exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length T) + 8) HART Hbc ltac:(lia) ltac:(lia)).
assert (SNB : RtPFShared.sn_bytes (96 - 1) T = T ++ [0]).
{ unfold RtPFShared.sn_bytes. change (Z.to_nat (96 - 1)) with 95%nat. rewrite firstn_all2 by lia. reflexivity. }
assert (SNL : RtPFShared.sn_len (96 - 1) T = Z.of_nat (length T) + 1).
{ unfold RtPFShared.sn_len. rewrite SNB, length_app. cbn [length]. lia. }
(* 0x88a3c: snprintf(cur + 64, 96, "%s", c->reading) *)
eapply SRr_bind.
{ apply (b11ts_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (pa_sigma SS___interceptor_trampoline_snprintf)
    (ASNPRINTF fx) Wc regsT memT STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v)
    (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdT 0 (seg_spec.rseg_addr (p_c v) gi + 64) 96
    (seg_litA_rc F_s) T (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B11_RET_SN2)) HJT Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - apply b11_m16; [exact S6 | exact S3].
  - lia.
  - unfold CMD_SNP_K, ESTACK. rewrite ESTK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [unfold B11_RET_SN2, AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split.
    + right; left. split.
      * exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [unfold seg_spec.RC_PARSE_W; left; reflexivity|].
        cbn [fst snd]. lia.
      * exists bc, mc. split; [exact Hbc | lia].
    + unfold CMD_SNP_K, ESTACK. lia.
  - intros a Ha _ [[_ Hi] | Hs]; exfalso.
    + pose proof (pa_img_range a Hi) as Hr. unfold off_img, kImgEnd in *. lia.
    + lia.
  - exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (seg_spec.rseg_addr (p_c v) gi + 64) (96 + 8)
      HART Hbc ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (seg_spec.rseg_addr (p_c v) gi + 64) 96
      HART Hbc ltac:(lia) ltac:(lia)).
  - exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (seg_spec.rseg_addr (p_c v) gi + 64) 96
      HART Hbc ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite SNL. unfold off_img in *. lia.
  - unfold CMD_IMG_HI, CMD_SNP_K, ESTACK, kImgEnd. lia.
  - exact T9.
  - rewrite Egw. lia.
  - rewrite Egw. unfold CMD_IMG_HI, kImgEnd. lia.
  - rewrite Egd. lia.
  - rewrite Egd. unfold CMD_IMG_HI, kImgEnd. lia.
  - rewrite Egw. unfold CMD_IMG_LO. lia.
  - rewrite Egd. unfold CMD_IMG_LO. lia.
  - apply (b11ts_FR_s_regs (rdW Wc memT) _ (seg_litA_rc F_s) (p_c v + seg_spec.RC_READING) T regsT).
    + unfold argZ. change (10 + 3) with 13. rewrite (b11_rg_get _ _ 13 _ QR ltac:(b11t_in)). unfold w64.
      apply unsigned_lit_small. lia.
    + rewrite EFs. lia.
    + rewrite EFs. unfold CMD_IMG_LO. lia.
    + rewrite EFs. unfold CMD_GOTW. lia.
    + exact (proj1 (proj2 FMT)).
    + pose proof FMT as (_ & _ & Hp & _). pose proof (Hp lyc Sc Wc memT mdT HART) as Hpa.
      rewrite b11ts_F_s_len in Hpa. exact Hpa.
    + rewrite Hsp, SNL, EFs. unfold snp_out.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint; cbn [fst snd]. unfold off_img in *. lia.
    + lia.
    + exact (b11ts_bytes_range_aview SEGS (w_H Wc) memT _ T HSTRT).
    + lia.
    + exact HSTRT.
    + exact HSAT.
    + exact HSAM.
    + rewrite Hsp, SNL. unfold snp_out.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold seg_spec.cstr_span, CMD_SNP_K, ESTACK;
        pose proof (Z.mod_pos_bound (- (p_c v + seg_spec.RC_READING + Z.of_nat (length T) + 1)) 8 ltac:(lia)); lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint; cbn [fst snd]. unfold seg_spec.cstr_span.
      pose proof (Z.mod_pos_bound (- (p_c v + seg_spec.RC_READING + Z.of_nat (length T) + 1)) 8 ltac:(lia)). lia.
  - lia.
  - intros a (sg & Hsg & Hw & Hr) Ho He. exact (T8 a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
  - exact HFRM. }
(* back at 0x88a40 at the FP state fx1 the wrapper returns *)
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & _ & Hby & Hkp & _ & _).
rewrite SNL in Hby, Hkp. rewrite SNB in Hby.
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in Hkp by lia.
change CMD_SNP_K with 8192 in Hkp.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _). rewrite ESTK in HPRES2.
unfold pf_postm, PF_POSTr. eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx|].
(* 0x88a40 li a0,-8; 0x88a44 j LOWOUT: a plain run *)
set (E2 := Eimg (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = getr regs2 r)
  by (intros k r Hk; subst E2; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HS2 : st_ok_pi (fx := fx1) SEGS VAL E2 b11t_ss2
  (restrict (w_H Wc) (@mkst fx1 regs2 (Z_to_bv 64 (BASE + B11_RET_SN2)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b11t_ss2. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_LOWOUT.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG, HF.
b11t_clear_md.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E2 _ (w_H Wc) mem2 (ms_mem ms) (fun _ => False) HFr);
    [intros b0 wlo whi a0 Hin0 Hrr; vm_compute in Hin0; destruct Hin0 | exact Ha | tauto]. }
assert (QK3 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b11t_rreg HS2; rewrite b11t_den_atom0; apply EE2; reflexivity |]). destruct Hr. }
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (-8)).
{ b11t_rreg HS2. cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity. }
pmkst HS2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_LOWOUT) rg mm mdx) end.
(* what the store, the call and the run kept and wrote *)
assert (KF : forall a, 0 <= a < 2 ^ 64 ->
    ~ (seg_spec.rseg_addr (p_c v) gi + 60 <= a < seg_spec.rseg_addr (p_c v) gi + 64 + (Z.of_nat (length T) + 1)) ->
    ~ (pf_s1 v - 8192 <= a < pf_s1 v) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha H1 H2. rewrite (K3 a Ha). rewrite (Hkp a Ha); [|lia | exact H2]. apply KMT; [exact Ha | lia]. }
assert (K4 : forall i, 0 <= i < 4 -> rdW Wc (ms_mem ms) (seg_spec.rseg_addr (p_c v) gi + 60 + i) =
    Some (bv_unsigned (byte_of_word (Z_to_bv 64 1) i))).
{ intros i Hi. rewrite K3 by lia. rewrite Hkp by lia. exact (W4 i Hi). }
assert (KP : b11_kept v pos false (b11_cw v gi) (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split.
  - intros a Ha Hn. apply KF; [exact Ha | |].
    + intros Hq. apply Hn. unfold b11_Wr. right; right; right. cbv [b11_cw seg_spec.RS_MODEL]. lia.
    + intros Hq. apply Hn. unfold b11_Wr. left. rewrite ESTK. lia.
  - intros a Ha Hv. rewrite (K3 a Ha).
    destruct (Z_lt_le_dec a (pf_s1 v - 8192)) as [L1 | L1]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L2 | L2]].
    + destruct (Z_le_gt_dec (seg_spec.rseg_addr (p_c v) gi + 64) a) as [D1 | D1];
        [destruct (Z_lt_le_dec a (seg_spec.rseg_addr (p_c v) gi + 64 + (Z.of_nat (length T) + 1))) as [D2 | D2]|].
      * pose proof (Hby (a - (seg_spec.rseg_addr (p_c v) gi + 64)) ltac:(lia)) as Hb.
        replace (seg_spec.rseg_addr (p_c v) gi + 64 + (a - (seg_spec.rseg_addr (p_c v) gi + 64))) with a in Hb by lia.
        rewrite Hb. discriminate.
      * rewrite (Hkp a Ha) by lia. exact (MVT a Hv).
      * rewrite (Hkp a Ha) by lia. exact (MVT a Hv).
    + apply (aview_some_of_apresent SEGS). apply HPRES2. lia.
    + rewrite (Hkp a Ha) by lia. exact (MVT a Hv). }
(* the record: c holds r_upd cf gi (rs_with_model m T) (b11f_rconf_model over the bytes of c) *)
destruct HRC as (bs & Hbs & Henc).
pose proof Henc as (Hlen & _ & Hseg & _).
assert (Lbs : Z.of_nat (length bs) = 16616) by lia.
pose proof (Hseg gi Hgi') as Hsg. unfold b11_cf1 in Hsg. rewrite (b11f_nth_upd_same cf gi _ Hgic) in Hsg.
destruct Hsg as (_ & _ & _ & _ & _ & _ & Hmod & _).
assert (EM : seg_spec.fldz seg_spec.RS_MODEL 24 (seg_spec.fld (356 * gi) 356 bs) =
    seg_spec.fld (356 * gi + 36) 24 bs).
{ unfold seg_spec.fldz. change (Z.to_nat seg_spec.RS_MODEL) with 36%nat. change (Z.to_nat 24) with 24%nat.
  apply b11f_fld_fld. lia. }
rewrite EM in Hmod. cbn [rs_model b11_set_model] in Hmod.
set (rdp := fun a => if (a <? p_c v) || (p_c v + seg_spec.SEG_C_SIZE <=? a) then rdW Wc (ms_mem ms) a
                     else rdW Wc memc a).
assert (HRCp : sa_rconf rdp (p_c v) (b11_cf1 cf gi val)).
{ exists bs. split; [|exact Henc]. intros i Hi. unfold rdp; cbv beta.
  destruct ((p_c v + Z.of_nat i <? p_c v) || (p_c v + seg_spec.SEG_C_SIZE <=? p_c v + Z.of_nat i)) eqn:Eo.
  - exfalso. apply orb_true_iff in Eo as [Eo | Eo]; [apply Z.ltb_lt in Eo | apply Z.leb_le in Eo]; lia.
  - exact (Hbs i Hi). }
assert (HRC3 : sa_rconf (rdW Wc (ms_mem ms)) (p_c v)
    (r_upd (b11_cf1 cf gi val) gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)]) T))).
{ apply (b11f_rconf_model rdp (rdW Wc (ms_mem ms)) (p_c v) (b11_cf1 cf gi val) gi
    (snprintf_s 24 F_s [AS (r_low val 0 24)]) T HRCp Hgi' ltac:(lia) ltac:(lia)).
  split; [|split; [|split]].
  - intros a Ha N1 N2 N3. unfold rdp; cbv beta.
    destruct ((a <? p_c v) || (p_c v + seg_spec.SEG_C_SIZE <=? a)) eqn:Eo; [reflexivity|].
    apply orb_false_iff in Eo as [Eo1 Eo2]. apply Z.ltb_ge in Eo1. apply Z.leb_gt in Eo2.
    apply KF; [exact Ha | |]; unfold seg_spec.RS_MODEL, seg_spec.RS_MODEL_SET, seg_spec.RS_MODEL_FILE in *; lia.
  - exists (seg_spec.fld (356 * gi + 36) 24 bs). split; [exact (proj1 Hmod)|]. split; [|exact Hmod].
    intros i Hi. rewrite (proj1 Hmod) in Hi.
    rewrite KF by (unfold seg_spec.RS_MODEL; lia).
    rewrite b11f_fld_nth by lia.
    replace (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL + Z.of_nat i)
      with (p_c v + Z.of_nat (356 * gi + 36 + i)) by (unfold seg_spec.RS_MODEL; lia).
    exact (Hbs (356 * gi + 36 + i)%nat ltac:(lia)).
  - exists (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4 (Z_to_bv 64 1)). split; [|reflexivity].
    intros i Hi. rewrite OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.length_le4 in Hi.
    replace (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL_SET + Z.of_nat i)
      with (seg_spec.rseg_addr (p_c v) gi + 60 + Z.of_nat i) by (unfold seg_spec.RS_MODEL_SET; lia).
    rewrite (K4 (Z.of_nat i) ltac:(lia)). rewrite b11t_le4_1 by exact Hi. reflexivity.
  - assert (Lg : length (seg_spec.fld (356 * gi + 64) 96 bs) = 96%nat) by (rewrite b11f_fld_len; lia).
    pose proof (b11ts_cstr_put0 96 _ T Lg HTl HTn HTr) as HC96.
    exists (seg_spec.zb (T ++ [0]) ++ skipn (S (length T)) (seg_spec.fld (356 * gi + 64) 96 bs)).
    split; [exact (proj1 HC96)|]. split; [|exact HC96].
    assert (Lz : length (seg_spec.zb (T ++ [0])) = S (length T))
      by (unfold seg_spec.zb; rewrite length_map, length_app; cbn [length]; lia).
    intros i Hi. rewrite (proj1 HC96) in Hi.
    replace (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL_FILE + Z.of_nat i)
      with (seg_spec.rseg_addr (p_c v) gi + 64 + Z.of_nat i) by (unfold seg_spec.RS_MODEL_FILE; lia).
    destruct (Nat.lt_ge_cases i (S (length T))) as [Hl | Hl].
    + rewrite app_nth1 by lia.
      rewrite b11ts_nth_zb by (apply Forall_app; split; [exact HTr | constructor; [cbv beta; lia | constructor]]).
      rewrite K3 by lia. rewrite (Hby (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
    + rewrite app_nth2 by lia. rewrite Lz, b11ts_nth_skipn, b11f_fld_nth by lia.
      rewrite KF by lia.
      replace (seg_spec.rseg_addr (p_c v) gi + 64 + Z.of_nat i)
        with (p_c v + Z.of_nat (356 * gi + 64 + (S (length T) + (i - S (length T))))) by lia.
      exact (Hbs (356 * gi + 64 + (S (length T) + (i - S (length T))))%nat ltac:(lia)). }
rewrite b11ts_cf1_model in HRC3.
(* ---- LOWOUT at fx1 ---- *)
apply (LOWOUT fx1 v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv
  (r_upd cf gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)]) T)) nm o ln d gi).
split; [|split; [exact HMID | split]].
- (* pf_base at model low's scope, at fx1 (b11_move keeps the FP state: carry the cut's pf_base to fx1 first) *)
  assert (HFRM1 : sa_frm0 (fx := fx1)) by exact (fxrel_frm0 fx fx1 HFRM Hfx).
  apply (b11_move B fx1 v pos lyc Sc Wc rX memc mdc PF_SC_L146 Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_L146 false
    (b11_cw v gi) (b11t_base_fx fx fx1 v pos lyc Sc Wc rX memc mdc PF_SC_L146 HBASE HFRM1) Hcw HJ2
    ltac:(exists (st_fs Sc); symmetry; apply b11t_set_fs_id) (Permutation_refl _) KP).
  + unfold pf_rg, b11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; b11t_kreg QK3 HP2 QR.
  + exact HFRM1.
  + exact (b11_keep_fsh v pos (b11_cw v gi) _ _ PF_SC_L146 HGe Hcw KP HFSH).
- (* pf_st: c holds the record, cur in slot 0xc0, cur_name, the counters' room at the next line *)
  split; [exact HRC3|].
  split; [cbn [pf_cur_ok]; rewrite b11f_upd_len; exact Hgic|].
  split; [exact (b11_keep_nm v pos false (b11_cw v gi) _ _ nm HGe Hcw KP HNM)|].
  split.
  + apply b11f_cnt_upd. apply (pf_cnt_mono cf (length (skipn o (p_s v)))); [|exact HCNT].
    destruct HMID as (Ho & _). pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
  + exact (b11_keep_slot v pos false (b11_cw v gi) _ _ 0xc0 _ HGe Hcw KP ltac:(lia) HC0).
- (* the registers *)
  unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [exact R10 | b11t_kreg QK3 HP2 QR].
Qed.

Lemma b11t_rs1 : forall n, HA_LOWOUT B n -> B11_RS1_stmt (fx := fx) B n.
Proof.
intros n LOWOUT v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
apply (b11t_run1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ HI).
intros regsT memT mdT HJT KMT MVT W4 QR Q1.
exact (b11t_call2 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regsT memT mdT LOWOUT HI HJT KMT MVT W4 QR Q1).
Qed.

End x.

(* the cut at every FP state *)
Theorem b11_rs1_ok : forall (fx : YK11.FPState) (n : nat), HA_LOWOUT B n -> B11_RS1_stmt (fx := fx) B n.
Proof. intros fx n H. exact (b11t_rs1 (fx := fx) n H). Qed.
End d.
