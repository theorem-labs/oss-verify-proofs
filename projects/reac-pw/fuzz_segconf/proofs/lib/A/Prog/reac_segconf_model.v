(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of arg_line (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8b128 = BASE + AF_arg_line, 304 bytes, 76 instructions): targ_line_spec of a Theorem Labs lane's
   lib/B/Prog/arg_line_c.v, proved as stated, over its callee contract rec_canonical_c and the strlen wrapper, each
   taken at the walk's FP state (the statement states them at every FP state).

   The B re-walk of the A walk lib/A/Prog/arg_line.v (a Theorem Labs lane a60bdbabd8f), on B's code as measured with capstone
   (symbol-keyed; B adds five UBSan trap branches and a fourth inline check, the store4 of c->nargs; the calls and the
   shadow-check pattern are A's). arg_line(c, line) (recorder.c:229-233): c in a0, line in a1; s1 = c, s0 = c + 4,
   s4 = the shadow byte address of c + 4, s3 = the shadow base (through the GOT word 0xa5f50 = A_OBJ 0 and the cell
   0xb0c38 = A_OBJ 12: an auipc-paired object slot, so no A_HI value is read). c->nargs is read once before the calls
   and once after them; the path splits on it (c->nargs = 6: return, al_walk6; c->nargs < 6: strlen, rec_canonical,
   c->nargs := m + 1, c->args[m] := p, al_walk_lt). On the second path c->nargs is an atom of value 0..5 up to the
   last segment, where the walk splits it into its six values, so that the stores' addresses are constant offsets
   of c.

   Report and UBSan trap edges, each refuted at its branch by the token executor's run (CmdPaLib.v's paj_run, sound by
   SRr_run_pi_tok_AJ), which decides the branch from the symbolic state's shadow entry al_SH (a check) or its facts
   (a trap):
     0x8b224 (__asan_report_load4; guards 0x8b174 bnez, 0x8b21c blt): refuted by the check token of the run at
       al_walk6 / al_walk_lt's first paj_run_tok, from sh_ok al_SH of al_entry / al_entry_lt, i.e. al_slot_addressable
       (the slot premise: c + 4 is in g_rec's or record.spill's zero-shadow range, CmdZsh.cmd_addressable_in).
     0x8b238 (__asan_report_load4; guards 0x8b19c bnez, 0x8b230 blt), 0x8b24c (__asan_report_store4; guards 0x8b1b0
       bnez, 0x8b244 blt), 0x8b254 (__asan_report_store8; guard 0x8b1e8 bnez): refuted by the check tokens of
       al_walk_lt's last paj_run_tok, from SHOK3 (al_slot_addressable at the state after rec_canonical; c + 4 and
       c + 8 + 8m lie in [c, c + 56)), from the slot premise.
     0x8b144 (beqz c -> unimp 0x8b210): refuted by the run's facts: atom 10 = c lies in [A_G_REC, A_REC_SPILL]
       (al_facts / al_facts_lt, facts_ok by al_entry / al_entry_lt's HG), from the slot premise (al_slot_facts).
     0x8b150 (bnez (c & 7) -> unimp): refuted by the same facts' alignment (af_al2 = 3: c mod 8 = 0, al_slot_facts).
     0x8b1a8 (blt (m + 1) m, the signed overflow of c->nargs++): refuted by al_walk_lt's last run on the literal m,
       one of 0..5 (the nargs premise m <= 6 and the branch at 0x8b180, which the first run decides on atom 33's fact
       0 <= m <= 5; the slot is outside rec_canonical's footprint, so the value reloaded at 0x8b1a0 is m: VN).
     0x8b1c4 (beqz (c + 8 + 8m)) and 0x8b1d8 (the pointer c + 8 + 8m wraps below c + 8): refuted by al_walk_lt's last
       run, from the facts on atom 10 (c in [A_G_REC, A_REC_SPILL]) and the literal m.

   Section hypotheses beyond the statement's (named as the lemmas a Theorem Labs lane states only at PI := PB_cmd): HB (CmdBSyms,
   the per-binary allocator record), MTL (the meter's laws), cmd_val_objs_PB (CmdObj.v's cmd_val_objs: the GOT word and
   the shadow cell), cmd_sig_prog_PB (CmdObj.v's cmd_sig_prog: rec_canonical's call target), cmd_img_facts_tfib
   (a Theorem Labs lane's CmdRecImg.v lemma, at this walk's abstract segments) and PRW (the core's prog_rw, for CmdRecCells'
   PROG_WRITABLE: the two stores into the slot). LAWS is AR_laws_ok; PALib's fields are CmdRecCells' cmd_cf_got,
   cmd_cf_cell and cmd_cf_env. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/arg_line.v, with its module paths, module names and numbers changed; 415 of its 490 lines of code are new or changed and 653 lines of the source are left out. *)
(* The walk of reac_segconf_model on fuzz_segconf.asan (image A, 0x897e8 = BASE + AF_reac_segconf_model,
   27 instructions): reac_segconf_model_contract (reac_segconf_model_c.v) from its callee's contract
   reac_segconf_find_contract (reac_segconf_find_c.v), in plugin-hostd/fuzz_command's lib/A/Prog form (arg_line.v
   at origin/ossv/recipes 501c0d516c69: the symbolic executor over the listing, a program call through cl_callS,
   the symbolic state carried over the call by jafter_call_keep_pi, the inline check removed by a shadow entry).

   Shape (the plan: provenance/evidence/listing-plans/plan-reac_segconf_model.md): 0x897e8-0x897fc the 16-byte frame, the spills
   of ra and s0, s0 := the shadow base through the GOT word (listing object 0) and the cell (object 12);
   0x89800 `jal reac_segconf_find` with a0 = c, a1 = name; 0x89804 `beqz a0` to the epilogue when find returns
   0; else the check of the 4-byte load at s + 0x3c (0x89808-0x89818: the shadow byte of s + 0x3c, which the
   shadow entry [s + 0x3c, s + 0x40) makes 0, so the slow path 0x89840-0x89848 and the error arm 0x8984c-0x89850
   are not reached), `lw a1,60(a0)` (s->model_set, 0 or 1), the mask, a0 := s + 0x24 or 0; the epilogue
   0x89830-0x8983c restores ra and s0 and returns. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaSB PaDenot PaLibG PaLibF PaCall SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_find_c reac_segconf_model_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* Image A's numbers for the two contracts are SegInstA's (the image-A owner's lib/A/Prog/SegInstA.v): find's stack
   STK_reac_segconf_find = 32 + 2 * ESTACK (its 32-byte frame and the 2 * ESTACK window the strcmp wrapper asks
   below it), the model's STK_reac_segconf_model = 16 + STK_reac_segconf_find (its 16-byte frame above find's
   window), and the read-only window RLO_A / RHI_A = SegGlob's SEG_RLO / SEG_RHI. *)

(* ============================== facts of the model and of the byte lists ============================== *)
Lemma md_find_go_lt : forall segs nm k i, r_find_go segs nm k = Some i -> (k <= i < k + length segs)%nat.
Proof.
induction segs as [|s segs IH]; intros nm k i H; cbn [r_find_go] in H; [discriminate|].
destruct (strcmp (rs_name s) nm =? 0); [injection H as <-; cbn [length]; lia|].
apply IH in H. cbn [length]. lia.
Qed.
Lemma md_find_lt : forall rcs nm i, r_find rcs nm = Some i -> (i < length (rc_seg rcs))%nat.
Proof. intros rcs nm i H. apply md_find_go_lt in H. lia. Qed.

Lemma md_nth_firstn : forall {A} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros n k d Hk; destruct n as [|n]; try lia; cbn [firstn].
- destruct k; reflexivity.
- destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma md_nth_skipn : forall {A} (l : list A) o k d, nth k (skipn o l) d = nth (o + k) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; cbn [skipn]; [destruct k; reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma md_nth_fld : forall (l : list byte) o n k d, (k < n)%nat -> nth k (seg_spec.fld o n l) d = nth (o + k) l d.
Proof. intros l o n k d Hk. unfold seg_spec.fld. rewrite md_nth_firstn by exact Hk. apply md_nth_skipn. Qed.

(* the four bytes of a flag word (seg_spec.flag_enc: le4 of 0 or 1) *)
Lemma md_flag_byte : forall (b : bool) (f : list byte) k, seg_spec.flag_enc b f -> (k < 4)%nat ->
bv_unsigned (nth k f ZB0) = if (Nat.eqb k 0 && b)%bool then 1 else 0.
Proof. intros b f k Hf Hk. unfold seg_spec.flag_enc in Hf. subst f. destruct b; destruct k as [|[|[|[|k]]]]; try lia; vm_compute; reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The symbolic entry state. Atoms 0..31: the registers at the entry (a0 = c atom 10, a1 = name atom 11, sp atom
   2); atom 32: the shadow base 0x7fff8000; A_OBJ 0 / A_OBJ 12: the GOT word of the shadow-base cell and the cell
   (SegAddr's seg_objs 0 and 12). Regions: the 16-byte frame below the entry sp, the GOT word, the cell. The call
   returns a0 as the fresh atom 68 (havoc from 64, a0 at CLOB index 4); on the path where find found entry i the
   walk adds that atom's range, the 4-byte region s->model_set holding the flag f, and the one shadow entry
   [s + 0x3c, s + 0x40), which removes the check of 0x89808-0x89818. *)
Definition md_Bx : sv := SOff 32 0.
Definition md_regs : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition md_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition md_ss : sstate := mkSS AF_reac_segconf_model sr_atoms md_regs None md_facts.
Definition md_extra : list word := map (Z_to_bv 64) [SB].
Definition md_flag (f : Z) : YP09.region := YP09.mkRegion (Some 68%nat) 60 64 60 60 [YP09.mkChunk 60 (CVal 4 (SLit f))].
Definition md_SH : list shent := [mkSHE 68 60 64].

Section e.
Variable B : asyms.
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
(* the callee's contract, at every FP state, at image A's numbers *)
Hypothesis FIND : forall fx0 : YK11.FPState,
  reac_segconf_find_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_find) SegInstA.STK_reac_segconf_find
    SegInstA.RLO_A SegInstA.RHI_A.
(* the listing's records the walk reads (fuzz_command's walks take them with these roles): the GOT word and the
   cell of the shadow base as the listing's objects 0 and 12 (PALib, SegPaLib.v), and the program functions' call
   targets against the listing's base (seg_sig_prog, SegObj.v) *)
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).

Lemma md_sig_find : SIGMA SS_reac_segconf_find = BASE + AF_reac_segconf_find.
Proof using SIGP.
rewrite (SIGP SS_reac_segconf_find); [reflexivity|].
cbn [seg_prog_syms In]. repeat (first [left; reflexivity | right]).
Qed.

(* a region of the symbolic state is kept over a call when the call keeps its bytes and leaves its window present *)
Lemma md_kept_region : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof using.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hk Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hk. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

(* the flag word as the chunk of its region holds it *)
Lemma md_val_flag : forall H mem a (b : bool),
(forall k, (k < 4)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (if (Nat.eqb k 0 && b)%bool then 1 else 0)) ->
val_mem SEGS (mrestrict H mem) a 4 (if b then 1 else 0).
Proof using.
intros H mem a b Hk k Hk4. destruct (aview_byte SEGS H mem _ _ (Hk k Hk4)) as (x & Hx & Hv & _).
rewrite Hx. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hv.
destruct b; destruct k as [|[|[|[|k]]]]; try lia; vm_compute; reflexivity.
Qed.

(* where the query's objects lie: below alloc_ceiling (the block, a side-stack frame or the image) *)
Lemma md_qp_bounds : forall ly S (W : world SEGS) mem md rd c name rcs nm,
AR SEGS B ly S W mem md -> query_pre SEGS B ly S rd c name rcs nm ->
4096 <= c /\ c + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
0 <= name /\ name + Z.of_nat (length nm) + 1 <= alloc_ceiling.
Proof using.
intros ly S W mem md rd c name rcs nm HAR (Hc0 & Hc16 & _ & (p & m & Hin & Hp & Hpe) & _ & Hn0 & _ & HLOC & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos m) as Hrq.
assert (Hm0 : 0 <= m) by (destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm); lia).
specialize (Hrq Hm0).
split; [lia|]. split; [lia|].
destruct HLOC as [(q & k & Hq & Hqn & Hqe) | [(cid & pos & Hf & Hcid & Hfa & Hfe) | HI]].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hq) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)). lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hf) as (Hf0 & Hfc & _). lia.
- destruct (HI name ltac:(lia)) as (Hi0 & _).
  destruct (HI (name + Z.of_nat (length nm)) ltac:(lia)) as (Hi1 & _).
  pose proof (pa_segs_low _ Hi0). pose proof (pa_segs_low _ Hi1).
  pose proof asan_consts as (C1 & _). unfold kLowMemEnd in *. lia.
Qed.

(* the query's facts hold at a reader that agrees with the entry's below lo, when lo is at or above
   alloc_ceiling: each of them reads bytes of the block, of the name or of their shadow *)
Lemma md_qp_kept : forall ly S (W : world SEGS) mem md rd rd' lo hi c name rcs nm,
AR SEGS B ly S W mem md -> query_pre SEGS B ly S rd c name rcs nm ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a) -> alloc_ceiling <= lo ->
query_pre SEGS B ly S rd' c name rcs nm.
Proof using.
intros ly S W mem md rd rd' lo hi c name rcs nm HAR HQ HK Hlo.
destruct (md_qp_bounds ly S W mem md rd c name rcs nm HAR HQ) as (Hc4 & Hce & Hn0 & Hne).
pose proof asan_consts as (C1 & C2 & _).
destruct HQ as (Hc0 & Hc16 & (bs & HBS & HE) & HH & (A0 & A1 & A2 & A3 & A4) & Hnz & ((HZ & HN0) & HT) & HL &
  (N0 & N1 & N2 & N3 & N4) & HLEN).
pose proof HE as (HLb & _).
assert (HCK : forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) by (intros a Ha; apply HK; lia).
refine (conj Hc0 (conj Hc16 (conj _ (conj HH (conj _ (conj Hnz (conj _ (conj HL (conj _ HLEN))))))))).
- exists bs. split; [|exact HE]. intros i Hi. rewrite HCK by (unfold seg_spec.SEG_C_SIZE in *; lia). exact (HBS i Hi).
- split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
  + exact (range_addressable_kept_win rd rd' lo hi c seg_spec.SEG_C_SIZE HK ltac:(lia) A0
      ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) A3).
  + intros Hp. exact (shadow_hull_vis_kept_win rd rd' lo hi c seg_spec.SEG_C_SIZE HK ltac:(lia) A0
      ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) Hp (A4 Hp)).
- split; [split; [|exact HN0]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HCK by lia. exact (HZ i ltac:(rewrite length_app; cbn [length]; lia)).
  + intros x Hx. assert (He8 : name + Z.of_nat (length nm) - (name + Z.of_nat (length nm)) mod 8 + 8 <= alloc_ceiling).
    { pose proof (Z.mod_pos_bound (name + Z.of_nat (length nm)) 8 ltac:(lia)) as Hm8.
      pose proof (proj2 alloc_ceiling_value) as Ha8.
      clear - Hne Ha8 Hm8. Z.div_mod_to_equations. lia. }
    rewrite HCK by lia. exact (HT x Hx).
- split; [exact N0|]. split; [exact N1|]. split; [exact N2|]. split.
  + exact (range_addressable_kept_win rd rd' lo hi name (Z.of_nat (length nm) + 1) HK ltac:(lia) N0 ltac:(lia) N3).
  + intros Hp. exact (shadow_hull_vis_kept_win rd rd' lo hi name (Z.of_nat (length nm) + 1) HK ltac:(lia) N0 ltac:(lia) Hp (N4 Hp)).
Qed.

(* the read-only view of the entry holds at a state that differs from the entry only in [lo, hi) above the image:
   no byte of [lo, hi) is an image byte, and each is mapped at the entry (fuzz_command arg_line.v al_arod_kept) *)
Lemma md_arod_kept : forall (W : world SEGS) mem mem' rlo rhi lo hi,
arodata_okP SEGS rlo rhi B (rdW W mem) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W mem' a = rdW W mem a) ->
(forall a, lo <= a < hi -> rdW W mem a <> None) -> kLowMemEnd <= lo -> hi <= 2 ^ 64 ->
arodata_okP SEGS rlo rhi B (rdW W mem').
Proof using.
intros W mem mem' rlo rhi lo hi HR HK Hv Hlo Hhi a Hro Ho He.
pose proof (HR a Hro Ho He) as Ha.
assert (Hm : forall m x, aview SEGS (w_H W) m x = aview SEGS (w_H W) m (x mod 2 ^ 64)).
{ intros m x. unfold aview, mbyte, mrestrict.
  replace (Z_to_bv 64 (x mod 2 ^ 64)) with (Z_to_bv 64 x); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
set (a' := a mod 2 ^ 64). pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha'. fold a' in Ha'.
assert (Er : seg_rom SEGS (Z_to_bv 64 a) = seg_rom SEGS (Z_to_bv 64 a')).
{ f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  subst a'. rewrite Z.mod_mod by lia. reflexivity. }
rewrite Hm in Ha |- *. fold a' in Ha |- *. rewrite Er in Ha |- *.
destruct (Z_lt_le_dec a' lo) as [Hl | Hl]; [|destruct (Z_lt_le_dec a' hi) as [Hh | Hh]].
- rewrite (HK a' Ha') by lia. exact Ha.
- exfalso. apply (Hv a' ltac:(lia)). rewrite Ha.
  rewrite (seg_rom_none SEGS a' Ha'); [reflexivity|].
  intros Hi. pose proof (pa_segs_low a' Hi). lia.
- rewrite (HK a' Ha') by lia. exact Ha.
Qed.

Lemma md_entry : forall W ly S regs mem md ch,
afn_pre SEGS B SegInstA.STK_reac_segconf_model ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs md_extra)) md_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_model)) mem (seg_rom SEGS))).
Proof using TL.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SegInstA.STK_reac_segconf_model = 8240) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as V0. pose proof (pa_obj_img 12%nat ltac:(lia)) as V12.
pose proof (pal_got_cell B TL) as VGC. unfold kImgEnd in V0, V12.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs md_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold md_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold md_regs. constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok, stack_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok, got_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok, bcell_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 md_Bx SB);
    [cbn [sv_denot md_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold md_regs, stack_region, got_regionP, bcell_regionP, extent_of_region;
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia; rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia;
  cbn [base_val]; rewrite Usp; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 FFS Hstk0 V0 V12 VGC; clear; intros; repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [md_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 FFS Hstk0. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* a run of the executor changes the memory only in the write windows of its regions: here the 16-byte frame
   [base - 16, base), the only writable region (the GOT word, the cell and s->model_set are read-only) *)
Local Ltac md_kept_frame HFr base Hbase KO :=
  lazymatch type of HFr with frame_of ?Ef _ (mrestrict ?Hh ?m0) (mrestrict _ ?m1) =>
    assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (base - 16 <= a < base) -> aview SEGS Hh m1 a = aview SEGS Hh m0 a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
        intros a Ha Hna;
        apply (kept_of_frame (segs:=SEGS) Ef _ Hh m0 m1 (fun a => base - 16 <= a < base) HFr); [| exact Ha | exact Hna];
        let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
        let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
        intros b wlo whi a' Hin Hr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?Hbase in Hr; lia|]);
        destruct Hin)
  end.

(* the post's sa_kept: outside [sp0 - STK, sp0) the exit reader is the entry's, through the last run (KOF: only the
   frame), find's own sa_kept (only find's window below sp0 - 16) and the first run (KO1: only the frame) *)
Local Ltac md_post_kept KOF HKf KO1 Hsp1 HTS HTF :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let Hf := fresh "Hf" in
  unfold sa_kept; intros a Ha Hw Hf; rewrite HTS in Hw;
  rewrite (KOF a Ha ltac:(lia));
  rewrite (HKf a Ha ltac:(rewrite Hsp1, HTF; lia) (fun x => x));
  exact (KO1 a Ha ltac:(lia)).

(* reac_segconf_model_contract (reac_segconf_model_c.v) at image A's numbers *)
Theorem reac_segconf_model_walk :
  reac_segconf_model_contract SEGS B (BASE + AF_reac_segconf_model) SegInstA.STK_reac_segconf_model
    SegInstA.RLO_A SegInstA.RHI_A.
Proof using FIND TL SIGP.
unfold reac_segconf_model_contract.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Hc64 H11 Hn64 HQ Hev.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HTS : SegInstA.STK_reac_segconf_model = 8240) by reflexivity.
assert (HTF : SegInstA.STK_reac_segconf_find = 8224) by reflexivity.
destruct (md_qp_bounds ly S W mem md _ c name rcs nm HAR HQ) as (Hc4 & Hce & Hn0 & Hne).
pose proof (md_entry W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SegInstA.STK_reac_segconf_model [] ly S W regs mem md ch HPRE) as HJ.
assert (SHOK : sh_ok SEGS md_Bx [] (Eimg (Ereg regs md_extra)) (mrestrict (w_H W) mem)) by apply Forall_nil.
remember (Eimg (Ereg regs md_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn'; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs md_extra) E)
  by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_model)) with (Z_to_bv 64 (BASE + AF_reac_segconf_model)).
unfold md_ss, md_regs in HS.
(* 0x897e8 .. 0x897fc: the frame, the spills, s0 := the shadow base; the run stops at the call of find *)
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hna. apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms) (fun a => spZ regs - 16 <= a < spZ regs) HFr);
  [| exact Ha | exact Hna].
  intros b wlo whi a' Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp in Hr; lia|]); destruct Hin. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
pmkst HS.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -16)
  by (change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, Usp, unsigned_lit_small by lia; reflexivity).
assert (Hvis : forall a, spZ regs - 16 <= a < spZ regs -> rdW W mem a <> None)
  by (intros a Ha; apply (aview_some_of_apresent SEGS); apply Hpres; lia).
assert (HROD2 : arodata_okP SEGS SegInstA.RLO_A SegInstA.RHI_A B (rdW W (ms_mem ms)))
  by (apply (md_arod_kept W mem (ms_mem ms) _ _ (spZ regs - 16) (spZ regs) HROD KO1 Hvis); unfold kLowMemEnd; lia).
assert (HQ2 : query_pre SEGS B ly S (rdW W (ms_mem ms)) c name rcs nm)
  by exact (md_qp_kept ly S W mem md _ _ (spZ regs - 16) (spZ regs) c name rcs nm HAR HQ KO1 ltac:(lia)).
(* 0x89800: the call of reac_segconf_find (a0 = c, a1 = name), returning to 0x89804 = BASE + 19152 *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (SIGMA SS_reac_segconf_find))
    SegInstA.STK_reac_segconf_model (spZ regs) []
    ly S W mem md [] ly S _ 0 SegInstA.STK_reac_segconf_find [] EV_reac_segconf_find (-16) (Z_to_bv 64 (BASE + 19152)) []
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (seg_spec.find_ptr c rcs nm) /\
       sa_kept SEGS W (ms_mem ms) W2 mem2 (ms_regs ms) SegInstA.STK_reac_segconf_find (fun _ => False) /\
       sa_noalloc B ly S ly2 S2)
    HJ Hsp1).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8, E32. rewrite unsigned_lit_small by (unfold SB; lia). unfold SB. lia.
  - intros HPRE2. rewrite md_sig_find. eapply SRr_mono.
    { apply (FIND fx ly S W (ms_regs ms) (ms_mem ms) _ [] c name rcs nm HPRE2 HROD2).
      - rewrite R10, (EE 10%nat 10%bv eq_refl). exact H10.
      - exact Hc64.
      - rewrite R11, (EE 11%nat 11%bv eq_refl). exact H11.
      - exact Hn64.
      - exact HQ2.
      - exact Hev. }
    cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HK3).
    exists ly3, S3, regs3, mem3, md3. split; [rewrite R1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HK3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Hp10 & HKf & HNA)).
(* back at 0x89804: the symbolic state over the call, with a0..a7, t0..t6 and ra fresh atoms 64..79 *)
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & GB3 & _ & _ & _ & Hpres3 & _).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot2. rewrite (pal_cell B TL) in Kcell2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot3. rewrite (pal_cell B TL) in Kcell3.
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - eapply md_kept_region; [exact Usp | intros a Ha | intros a Ha; apply Hpres3; lia].
    apply G1; [lia | lia | apply inFP_nil].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 64 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n0, (n0 < 64)%nat -> ew E2 n0 = ew E n0) by (intros n0 Hk0; rewrite HE2; apply YN3v.ew_havoc_old; exact Hk0).
assert (HAE2 : env_agree 32 (Ereg regs md_extra) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E68 : ew E2 68 = getr regs3 10%bv) by (rewrite HE2; unfold havoc; cbn [ew]; reflexivity).
clear HE2.
rewrite Hp10 in E68. unfold w64 in E68.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (E32b : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (SHOK2 : sh_ok SEGS md_Bx [] E2 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
destruct HNA as (HPm & Hly3 & HS3f).
pose proof HQ as (Hc0 & Hc16 & (bs & HBS & HENC) & (pb & mb & Hinb & Hpb & Hpbe) & _).
pose proof HENC as (HLb & HLS & HSEG & _).
assert (Hinb3 : In (pb, mb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm | exact Hinb]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb mb HAR Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hmb).
pose proof (req_size_pos mb ltac:(lia)) as [_ Hreq].
unfold seg_spec.find_ptr in E68.
destruct (r_find rcs nm) as [i|] eqn:RF.
- (* find found entry i: s = c + 356 i *)
  pose proof (md_find_lt rcs nm i RF) as Hi.
  unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE in E68.
  remember (c + 356 * Z.of_nat i) as s eqn:Hs.
  assert (Hs64 : s + 64 <= c + seg_spec.SEG_C_SIZE) by (unfold seg_spec.SEG_C_SIZE; lia).
  assert (Hs0 : 4096 <= s) by lia.
  psrr_branch_tok RUN BR HS SHOK2 Bspan.
  + (* the branch to the epilogue is not taken: s is not 0 *)
    exfalso. rewrite branch_eq_U, (U_atom E2 68 s E68) in Hc by lia.
    change (U E2 (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. lia.
  + (* 0x89808 .. 0x8983c: the check, the load of s->model_set, the mask, the epilogue *)
    pose proof (HSEG i Hi) as HRS. change (nth i (rc_seg rcs) rseg_d) with (r_seg rcs i) in HRS.
    pose proof HRS as (_ & _ & _ & _ & _ & _ & _ & HMS & _).
    (* the flag word after the call: the block's bytes are kept by find (empty footprint) *)
    assert (HFB : forall k, (k < 4)%nat ->
      rdW W3 mem3 (s + 60 + Z.of_nat k) = Some (if (Nat.eqb k 0 && rs_model_set (r_seg rcs i))%bool then 1 else 0)).
    { intros k Hk.
      replace (s + 60 + Z.of_nat k) with (pb + (s + 60 + Z.of_nat k - pb)) by lia.
      rewrite (GB3 pb mb (s + 60 + Z.of_nat k - pb) Hinb Hinb3 ltac:(lia) (inFP_nil _)).
      replace (pb + (s + 60 + Z.of_nat k - pb)) with (c + Z.of_nat (356 * i + 60 + k)) by lia.
      rewrite (HBS (356 * i + 60 + k)%nat) by (unfold seg_spec.SEG_C_SIZE in HLb; lia).
      assert (Hnth : nth (356 * i + 60 + k) bs ZB0 =
        nth k (seg_spec.fldz seg_spec.RS_MODEL_SET 4 (seg_spec.fld (356 * i) 356 bs)) ZB0).
      { unfold seg_spec.fldz, seg_spec.RS_MODEL_SET. change (Z.to_nat 60) with 60%nat. change (Z.to_nat 4) with 4%nat.
        rewrite md_nth_fld by lia. rewrite md_nth_fld by lia. f_equal. lia. }
      rewrite Hnth, (md_flag_byte _ _ k HMS Hk). reflexivity. }
    pose proof (md_val_flag (w_H W3) mem3 (s + 60) (rs_model_set (r_seg rcs i)) HFB) as VF.
    assert (Hs4 : s mod 4 = 0) by (rewrite Hs; clear - Hc16; Z.div_mod_to_equations; lia).
    assert (HF68 : afact_ok E2 68 (PTR 2)).
    { unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]. rewrite E68, unsigned_lit_small by lia.
      change (2 ^ 2) with 4. clear - Hs0 Hs64 Hpbe Hreq Hbceil C1 Hs4. lia. }
    pose proof (st_ok_pi_add_fact E2 _ _ 68 _ HS HF68) as HS1. clear HS.
    (* the flag value as a variable: vm_compute of the symbolic state below must not meet the open term
       rs_model_set (r_seg rcs i); the split into 1 and 0 comes just before the run *)
    remember (if rs_model_set (r_seg rcs i) then 1 else 0) as f eqn:Ef in VF.
    assert (HR68 : region_ok SEGS E2 (mrestrict (w_H W3) mem3) (md_flag f)).
    { unfold region_ok, md_flag; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E68, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E2 _ s 60 4 (SLit f) f); [reflexivity | rewrite Ef; destruct (rs_model_set _); cbn; lia | lia | exact VF]. }
    pose proof (blk_off_imgP B ly S W mem md pb mb HAR Hinb) as Hoff. unfold off_img in Hoff.
    pose proof (pa_obj_img 0%nat ltac:(lia)) as V0. pose proof (pa_obj_img 12%nat ltac:(lia)) as V12. unfold kImgEnd in V0, V12.
    lazymatch type of HS1 with st_ok_pi _ _ _ ?s0 _ => let r := eval vm_compute in (ss_mem s0) in
      assert (HD68 : all_disjoint E2 (md_flag f) r) end.
    { apply all_disjoint_of_extents. unfold md_flag, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
      rewrite E68, unsigned_lit_small by lia. rewrite Usp2.
      rewrite (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)).
      change (VAL 241%nat) with (VAL (A_OBJ 0)). change (VAL 253%nat) with (VAL (A_OBJ 12)).
      cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HTS in Hslo.
      clear - Hs Hs0 Hs64 Hpbe Hpb Hreq Hbceil Hceil Hslo Hoff V0 V12. repeat split; first [exact I | lia]. }
    clear Hoff V0 V12.
    pose proof (st_ok_pi_add_region E2 _ _ (md_flag f) HS1 eq_refl HR68 HD68) as HS. clear HS1.
    lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?s0 ?mm => let s' := eval vm_compute in s0 in change (st_ok_pi sg vl Ev s' mm) in HS end.
    assert (RA : range_addressable (rdW W3 mem3) SHADOW_OFF (s + 60) 4)
      by exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 pb mb (s + 60) 4 HAR3 Hinb3 ltac:(lia) ltac:(lia)).
    assert (SHOK3 : sh_ok SEGS md_Bx md_SH E2 (mrestrict (w_H W3) mem3)).
    { constructor; [|constructor].
      apply (shent_ok_of_range SEGS (w_H W3) mem3 E2 md_Bx 68 (s + 60) 4 s 60 64 RA).
      - unfold U, md_Bx. cbn [sv_denot]. rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned.
        rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
      - apply U_atom; [exact E68 | lia].
      - lia.
      - lia.
      - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF. lia. }
    clear SHOK2.
    destruct (rs_model_set (r_seg rcs i)) eqn:MS; cbv iota in Ef; subst f.
    * paj_run_tok RUN HS HJ3 SHOK3 Bspan. { awr_ok_tac. first [exact Usp2 | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp2]. }
      md_kept_frame HFr (spZ regs) Usp2 KOF.
      prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
      eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly3, S3, rg, m, d end.
      split; [cbn [ms_regs]; rewrite Rra; rewrite ?ew_ewset_other by lia; rewrite OLD2, (EE 1%nat 1%bv eq_refl) by lia;
              unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_reac_segconf_find);
              [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | unfold EV_reac_segconf_find, EV_reac_segconf_model; lia]|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs md_extra HS);
              [first [exact HAE2 | destruct HAE2 as [HA HD]; split;
                      [intros n Hn; rewrite ?ew_ewset_other by lia; apply HA; exact Hn | rewrite ?ed_ewset; exact HD]]
              | vm_compute; reflexivity]|].
      split; [|split; [md_post_kept KOF HKf KO1 Hsp1 HTS HTF | split; [exact HPm | split; [exact Hly3 | exact HS3f]]]].
      cbn [ms_regs]. rewrite Ra0. unfold seg_spec.model_ptr. rewrite RF. unfold r_model. rewrite RF, MS.
      unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_MODEL, w64. rewrite <- Hs.
      rewrite ?ew_ewset_other by lia. rewrite ?E68.
      (* the executor folds the all-ones mask: a0 = s + 0x24 *)
      apply bv_eq. rewrite ?Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_small s (2 ^ 64)) by lia. reflexivity.
    * paj_run_tok RUN HS HJ3 SHOK3 Bspan. { awr_ok_tac. first [exact Usp2 | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp2]. }
      md_kept_frame HFr (spZ regs) Usp2 KOF.
      prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
      eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly3, S3, rg, m, d end.
      split; [cbn [ms_regs]; rewrite Rra; rewrite ?ew_ewset_other by lia; rewrite OLD2, (EE 1%nat 1%bv eq_refl) by lia;
              unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_reac_segconf_find);
              [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | unfold EV_reac_segconf_find, EV_reac_segconf_model; lia]|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs md_extra HS);
              [first [exact HAE2 | destruct HAE2 as [HA HD]; split;
                      [intros n Hn; rewrite ?ew_ewset_other by lia; apply HA; exact Hn | rewrite ?ed_ewset; exact HD]]
              | vm_compute; reflexivity]|].
      split; [|split; [md_post_kept KOF HKf KO1 Hsp1 HTS HTF | split; [exact HPm | split; [exact Hly3 | exact HS3f]]]].
      cbn [ms_regs]. rewrite Ra0. unfold seg_spec.model_ptr. rewrite RF. unfold r_model. rewrite RF, MS.
      unfold w64. rewrite ?ew_ewset_other by lia. rewrite ?E68.
      (* the executor folds the zero mask: a0 = 0 *)
      first [reflexivity
            | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); reflexivity].
- (* find found nothing: a0 = 0, the branch to the epilogue is taken *)
  psrr_branch_tok RUN BR HS SHOK2 Bspan.
  + paj_run_tok RUN HS HJ3 SHOK2 Bspan. { awr_ok_tac. exact Usp2. }
    md_kept_frame HFr (spZ regs) Usp2 KOF.
    prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
    eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly3, S3, rg, m, d end.
    split; [cbn [ms_regs]; rewrite Rra, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_reac_segconf_find);
            [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | unfold EV_reac_segconf_find, EV_reac_segconf_model; lia]|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E2 _ _ regs md_extra HS); [exact HAE2 | vm_compute; reflexivity]|].
    split; [|split; [md_post_kept KOF HKf KO1 Hsp1 HTS HTF | split; [exact HPm | split; [exact Hly3 | exact HS3f]]]].
    cbn [ms_regs]. rewrite Ra0, E68. unfold seg_spec.model_ptr. rewrite RF. reflexivity.
  + (* not taken: impossible, a0 = 0 *)
    exfalso. rewrite branch_eq_U, (U_atom E2 68 0 E68) in Hc by lia.
    change (U E2 (SLit 0)) with 0 in Hc. apply Z.eqb_neq in Hc. lia.
Qed.
End e.
End f.
End d.

Print Assumptions reac_segconf_model_walk.
About reac_segconf_model_walk.
