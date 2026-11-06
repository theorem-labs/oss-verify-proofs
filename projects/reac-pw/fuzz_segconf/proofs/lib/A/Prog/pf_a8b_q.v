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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 552 of its 667 lines of code are new or changed and 4938 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a1.v, with its module paths and module names changed; 154 of its 196 lines of code are new or changed and 625 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: the mid-walk seed of segment A8b's cut JOIN (0x889b4) of
   reac_segconf_parse_file's walk, for a run of the token executor (lib/A/Prog/SegPaLib.v paj_run_to_tok) through
   JOIN's two inline checks #38 (load4 c->gen) and #39 (store4
   seg[i].seen_gen). Segment A8b's proof (the JOIN sub-walk), by the G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk): a seed and its helpers; the lane's
   rule-24 record is the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md
   (reuse verdict: none, written new).

   THE SHAPE. Check #38 loads the shadow byte at a3 = shadow_addr (c + RC_GEN), a value INV_A8B_JOIN gives as a
   literal word. The token executor recognises a checked load only when its address has the syntactic shape
   (x >> 3) + Bx (YCbn.v match_x), so the seed pins register 13 to the term pfq_sh 24 RC_GEN =
   ((s8 + RC_GEN) >> 3) + s6, with s8 = c (atom 24) and s6 = SHADOW_OFF (atom 22, Bx = pfq_Bx); pfq_sh_denot shows
   the term denotes w64 (shadow_addr (c + RC_GEN)) (the donor's cr_s10 / denot_s10 in
   proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_sd.v at 501c0d516c69). Check #39 forms its address
   inline from s4 (atom 20) and s6, so it needs no
   pin. Both checked granules are covered by pfj_SH, so the run decides both checks with no obligation.
   The regions (pfj_regions): 0 the two spill slots the run reads, s1 + 0x40 = c + RC_GEN and s1 + 0x50 =
   F + PF_O_CN (atom 9 = s1, read-only); 1 c->gen (atom 24, [RC_GEN, RC_GEN + 4), read-only, the extra atom 33);
   2 seg[i].seen_gen (atom 20 = rseg_addr c i, [0x160, 0x164), writable: the store `sw a1,0(a0)`).
   The extra atoms: 32 = F + PF_O_CN (cur_name, the snprintf destination), 33 = rc_gen cf.
   Executor facts read off the listing (build-20261030T180123Z.log): from pfj_ss the token run to PF_PROV2 stops
   there with no obligation and no token; a0 = atom 32, a1 = 16, a2 = atom 276 (A_OBJ 35, "%s"), a3 = atom 25
   (np), and region 2 holds CVal 4 (SExt true 32 (SOff 33 0)). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces pf_a8b_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a8b_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The shadow-address term and the token executor's shadow base *)
(* (x + off) >> 3 + s6, x the value of atom m: the shape YCbn.match_x reads as the checked address x + off *)
Definition pfq_sh (m : nat) (off : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m off) (SLit 3)) (SOff 22 0).
(* the shadow base Bx: s6's own atom (pf_fi gives getr rX 22 = w64 SHADOW_OFF) *)
Definition pfq_Bx : sv := SOff 22 0.

(** ** JOIN's seed *)
Definition pfj_regs : list sv := sr_set sr_atoms (13%bv : bv 5) (pfq_sh 24 seg_spec.RC_GEN).
Definition pfj_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 0x40 0x58 0 0
    [YP09.mkChunk 0x40 (CVal 8 (SOff 24 seg_spec.RC_GEN)); YP09.mkChunk 0x50 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 24%nat) seg_spec.RC_GEN (seg_spec.RC_GEN + 4) 0 0
    [YP09.mkChunk seg_spec.RC_GEN (CVal 4 (SOff 33 0))];
  YP09.mkRegion (Some 20%nat) seg_spec.RS_SEEN_GEN (seg_spec.RS_SEEN_GEN + 4)
    seg_spec.RS_SEEN_GEN (seg_spec.RS_SEEN_GEN + 4) [] ].
Definition pfj_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, PTR 2); (22%nat, mkAF SB SB 0); (24%nat, PTR 4);
          (32%nat, PTR 5); (33%nat, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
Definition pfj_ss : sstate := mkSS PF_A8B_JOIN pfj_regs pfj_regions None pfj_facts.
(* the two checked granules: c->gen (#38) and seg[i].seen_gen (#39) *)
Definition pfj_SH : list shent :=
[ mkSHE 24 seg_spec.RC_GEN (seg_spec.RC_GEN + 8); mkSHE 20 seg_spec.RS_SEEN_GEN (seg_spec.RS_SEEN_GEN + 8) ].

(** ** Helpers *)
Lemma pfq_sh_denot : forall (E : env) (m : nat) (x off : Z),
  ew E m = Z_to_bv 64 x -> ew E 22 = Z_to_bv 64 SHADOW_OFF -> 0 <= x -> 0 <= off -> x + off < 2 ^ 47 ->
  sv_denot E (pfq_sh m off) = w64 (shadow_addr (x + off)).
Proof.
intros E m x off Hm H22 Hx Ho Hxo. rewrite denot_lit_U. unfold w64. f_equal.
unfold pfq_sh. rewrite U_SAlu, U_srl3, !U_SOff, Hm, H22.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite Z.add_0_r, (zcanon_id (x + off)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
cbn [zalu_raw]. unfold shadow_addr.
assert (0 <= (x + off) / 8 <= x + off) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* the 4 little-endian bytes of v *)
Lemma pfq_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  nth k (Mem.le4 (Z_to_bv 64 v)) ZB0 = Z_to_bv 8 (le_byte v 4 k).
Proof.
intros v k Hv Hk. unfold Mem.le4. rewrite unsigned_lit_small by lia. unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth];
  rewrite ?Z_to_bv_unsigned, ?Z.shiftr_shiftr by lia; cbn [Z.of_nat Z.mul Z.add Pos.mul Pos.add];
  unfold bv_wrap; change (bv_modulus 8) with 256; rewrite ?Z.shiftr_0_r, ?Z.mod_mod by lia; reflexivity.
Qed.

(* a u32 field of a byte list the reader holds, as rd32 *)
Lemma pfq_rd32_field : forall (rd : reader) (a : Z) (bs : list byte) (off : nat) (v : Z),
  sa_bytes rd a bs -> seg_spec.u32_enc v (seg_spec.fld off 4 bs) -> (off + 4 <= length bs)%nat ->
  rd32 rd (a + Z.of_nat off) v.
Proof.
intros rd a bs off v Hb (Hv & Hf) Hl k Hk.
assert (E : nth (off + k) bs ZB0 = Z_to_bv 8 (le_byte v 4 k)).
{ rewrite <- (pfq_le4_nth v k Hv Hk), <- Hf. unfold seg_spec.fld.
  rewrite pf_a8b_m.pfa8b_nth_firstn by exact Hk. rewrite pf_a8b_m.pfa8b_nth_skipn. reflexivity. }
replace (a + Z.of_nat off + Z.of_nat k) with (a + Z.of_nat (off + k)) by lia.
rewrite (Hb (off + k)%nat ltac:(lia)), E. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* c->gen as rd32, from the struct's encoding *)
Lemma pfq_rd32_gen : forall (rd : reader) (c : Z) (cf : rconf),
  sa_rconf rd c cf -> rd32 rd (c + seg_spec.RC_GEN) (rc_gen cf).
Proof.
intros rd c cf (bs & Hb & Henc).
destruct Henc as (Hlen & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgen).
unfold seg_spec.fldz in Hgen.
pose proof (pfq_rd32_field rd c bs (Z.to_nat seg_spec.RC_GEN) (rc_gen cf) Hb Hgen) as H.
rewrite Z2Nat.id in H by (unfold seg_spec.RC_GEN; lia).
apply H. unfold seg_spec.SEG_C_SIZE, seg_spec.RC_GEN in *. lia.
Qed.

(* 4 bytes val_mem gives, as the little-endian list sa_bytes reads *)
Lemma pfq_sa_bytes_le4 : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 4 v -> 0 <= v < 2 ^ 32 ->
  sa_bytes (aview segs H mem) a (Mem.le4 (Z_to_bv 64 v)).
Proof.
intros segs H mem a v Hv Hr i Hi. rewrite Mem.length_le4 in Hi.
unfold aview. rewrite (Hv i Hi). cbn [option_map]. rewrite (pfq_le4_nth v i Hr Hi). reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section sd. Context {fx : YK11.FPState}.

(* JOIN's environment: atoms 0..31 the registers, 32 = F + PF_O_CN, 33 = rc_gen cf *)
Definition pfj_E (rX : bvmap 5 word) (fcn g : Z) : env := Eimg (Ereg rX [Z_to_bv 64 fcn; Z_to_bv 64 g]).
Lemma pfj_E_reg : forall rX fcn g n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (pfj_E rX fcn g) n = getr rX r.
Proof. intros rX fcn g n r Hn. unfold pfj_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma pfj_E32 : forall rX fcn g, ew (pfj_E rX fcn g) 32 = Z_to_bv 64 fcn.
Proof. intros rX fcn g. unfold pfj_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0). Qed.
Lemma pfj_E33 : forall rX fcn g, ew (pfj_E rX fcn g) 33 = Z_to_bv 64 g.
Proof. intros rX fcn g. unfold pfj_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 1). Qed.
Lemma pfj_E_img : forall rX fcn g, img_env VAL A_LIM (pfj_E rX fcn g).
Proof. intros. unfold pfj_E. apply Eimg_env. Qed.
Lemma pfj_E_agree : forall rX fcn g, env_agree 32 (Ereg rX []) (pfj_E rX fcn g).
Proof.
intros rX fcn g. split; [|reflexivity]. intros n Hn. unfold pfj_E. rewrite Eimg_low by (unfold A_TEXT; lia).
cbn [Ereg ew]. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity.
Qed.

(* the seed at JOIN *)
Lemma pfa8b_jseed : forall (Wc : world SEGS) (rX : bvmap 5 word) (memc : word -> option byte) s1 c ri fcn g,
  getr rX 9 = w64 s1 -> getr rX 13 = w64 (shadow_addr (c + seg_spec.RC_GEN)) -> getr rX 20 = w64 ri ->
  getr rX 22 = w64 SHADOW_OFF -> getr rX 24 = w64 c ->
  2 ^ 46 <= s1 -> s1 + 0x58 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= 140737479966720 -> c mod 16 = 0 ->
  c <= ri -> ri + 0x164 <= c + seg_spec.RC_GEN -> ri mod 4 = 0 ->
  4096 <= fcn <= 140737479966720 -> fcn mod 32 = 0 -> 0 <= g < 2 ^ 32 ->
  c + seg_spec.SEG_C_SIZE <= s1 ->
  rdword (rdW Wc memc) (s1 + 0x40) = Some (c + seg_spec.RC_GEN) ->
  rdword (rdW Wc memc) (s1 + 0x50) = Some fcn ->
  rd32 (rdW Wc memc) (c + seg_spec.RC_GEN) g ->
  (forall a, ri + 0x160 <= a < ri + 0x164 -> apresent (w_H Wc) memc a) ->
  st_ok_pi SEGS VAL (pfj_E rX fcn g) pfj_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_A8B_JOIN)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 c ri fcn g R9 R13 R20 R22 R24 Hs1a Hs1b Hs1c Hc0 Hc1 Hc2 Hr0 Hr1 Hr2 Hf0 Hf1 Hg Hcs
  K40 K50 KG KP.
assert (EG : seg_spec.RC_GEN = 16608) by reflexivity. assert (ES : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ER : seg_spec.RS_SEEN_GEN = 352) by reflexivity. assert (EO : SHADOW_OFF = 2147450880) by reflexivity.
set (E := pfj_E rX fcn g).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (exact (eq_trans (pfj_E_reg rX fcn g 9 9%bv eq_refl) R9)).
assert (E20 : ew E 20 = Z_to_bv 64 ri) by (exact (eq_trans (pfj_E_reg rX fcn g 20 20%bv eq_refl) R20)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (pfj_E_reg rX fcn g 22 22%bv eq_refl) R22)).
assert (E24 : ew E 24 = Z_to_bv 64 c) by (exact (eq_trans (pfj_E_reg rX fcn g 24 24%bv eq_refl) R24)).
pose proof (pfj_E32 rX fcn g) as E32. pose proof (pfj_E33 rX fcn g) as E33. fold E in E32, E33.
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = ri) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = c) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = fcn) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = g) by (rewrite E33; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold pfj_ss. apply pa_entry_st_ok_full.
- unfold pfj_regs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite R13. symmetry. apply pfq_sh_denot; [exact E24 | exact E22 | lia | lia | lia].
- vm_compute. reflexivity.
- unfold pfj_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat s1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 0x40 8 (SOff 24 seg_spec.RC_GEN) (c + seg_spec.RC_GEN));
        [rewrite denot_lit_U, (U_atom_off E 24 c seg_spec.RC_GEN E24) by lia; reflexivity | cbn; lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ K40).
    * apply (chunk_ok_val SEGS E _ s1 0x50 8 (SOff 32 0) fcn);
        [rewrite denot_lit_U, (U_atom E 32 fcn E32) by lia; reflexivity | cbn; lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ K50).
  + rewrite (VB 24%nat c E24) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ c seg_spec.RC_GEN 4 (SOff 33 0) g);
      [rewrite denot_lit_U, (U_atom E 33 g E33) by lia; reflexivity | cbn; lia | lia |].
    exact (val_mem_of_rd32 SEGS (w_H Wc) memc _ _ KG).
  + rewrite (VB 20%nat ri E20) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply KP. lia.
- apply pairwise_disjoint_of_extents. unfold pfj_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat s1 E9) by lia. rewrite (VB 24%nat c E24) by lia. rewrite (VB 20%nat ri E20) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [pfj_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U9, U20, U22, U24, U32, U33.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End sd.
End f.
End d.
