(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's op_add, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_op_add.v, with its module paths and module names changed; 6719 of its 6853 lines of code are new or changed and 2614 lines of the source are left out. *)
(* rule 24: proves function write_value (CONFIRM R24Writer 2026-10-30): write_value_holds, at the end of Section cl.
   fuzz_preset image A, slice S7b (S7bWriteValue of the S7b walk's lane): the program walk of write_value (A 0x86c8c, 258
   instructions, self-recursive) over the ONE image-A program listing (lib/A/Listing_prog.v, a Theorem Labs lane), generic in
   the image facts (Context PAImg) and in the allocator relation ARx (LAWS : AR_laws_x), concluding the kit's text
   twrite_value_specX (lib/A/PRH_FnWriter.v blob d89d3c67b78c, PRH_Base.v blob ef7c8ca98529, at the kit's cut 7cdbb61b5fa0) for every depth n.
   KIT MIGRATION (walkkit-next preset-tree-at-2026-10-29T11-52-53Z.tsv (sha256 7a1c7c129aef; internal record), merged preset-tree-at-2026-10-29T12-21-32Z.tsv (sha256 177285bb87d5; internal record)): fQmn over YAkMemnorm (the marked PLAWJ is GONE; each
   walk lemma instantiates the runner's invariant once at srr_inv_laws_memnorm_k); fpre's `raZ regs < alloc_ceiling`;
   the put family's TWO-case cut and indent's plain cut. PREMISES THAT MOVED BECAUSE OF A CALLEE TEXT (not for the
   invariant): wv_call_put / wv_call_indent / wv_call_put_string / wv_call_self now take the callee's ra bound
   `bv_unsigned raw < alloc_ceiling` (fpre's new conjunct; each site cites PRW_StepKit.pa_slot_lt_ceil), and ONE chain
   `s0Z regsc = o` with the two words of the kit's case 1 (form (a), PRH_FnWriter.v c1c0eee43164: rdword (o - 8),
   rdword (o - 16) < alloc_ceiling) at the call memory and `sp0 + oc + 16 <= o` (the caller chain from o that
   aj_call_xWR needs is built from them by wv_chain1g), replacing the old three-case cut + implication; wv_tail_put /
   wv_tail_put_string / wv_put_close / wv_leaf_lit take the two-case cut. Consumers: none outside this file.
   Engine: YC80x / YC1fPx (paj_run_x / paj_run_to_x and their R forms) over YCbqG's ajournal_x / ajournal_xR; the
   journal-free steps (branch, jr, return) are YC1fP's (YSRrG's paj_branchR at R); the caller-window post is discharged
   with YCbqGcallW (aj_call_xWR / aj_call_xWFR) and PRW_CallerJ (cj_kept); the tree survives a call by the kit's
   PRH_Reader (pj_nodeR_frame over pj_agreeR).
   THE RE-HIDING MOVE (the primed writer texts): tput / tindent / tput_string / twrite_value conclude SRr' segs
   RZ_cf with their posts at wle' segs RZ_cf (fpostWmR / fpostWFmR), since a put's realloc re-hides shadow. Every
   run of this file that reaches one of them is stated the same way: the tails and leaves (posts fpostWmR / fpostWFmR /
   fpostWR at wle'), the inner calls wv_call_* (journals at wle'), wv_post_P, wv_Qfin and wv_common's journal (restated in
   place at wle'), wv_cont and the loop's segments. A stretch before the first call runs at SRr and enters the primed
   form through wv_srr_pre; its journal enters wle' through wv_jlift. Every call uses aj_call_xWR / aj_call_xWFR at
   wle'; every walk after a call uses the runners at wle' (paj_run_x_invR / paj_run_to_x_invR, paj_branchR).
   NO IMAGE VALUE IS TYPED HERE: the function's offset is 4 * its generated slot (PAImg_prog A_prog_slot), and every
   .rodata address the code forms is read out of the generated listing itself (wv_addhi_off below reads the addend of
   the PAddHi at a named slot), so a re-pin is a regeneration, not a rewrite.
   #102 RE-FIT (2026-10-29; the kit texts by path: PRH_FnWriter
   2b497bc72172, PRH_Base fdb45545469b; the internal file REFIT-WRITER.md A-D, F, H and its float-threading design): the ledger's #102
   cells most / own after the rp_* binders (each lemma that states a ledger binds them implicitly); put's refused arm
   `f' = 1`; fpre's FRM0-ENTRY conjunct; the float posts of put_string / write_value (fpostWFm). FLOAT THREADING:
   the walk's lemmas are proved in Sections with `Context {fx}` that are CLOSED before a later lemma uses them at
   another float state; the container record wvx carries the ENTRY float state y_fx (wv_pre: y_fx X = fx), every join
   (wv_common) the current one's frm_zero and fs0-fs11 relation to it, the final post wv_Qfin is the float form at
   y_fx X, the callee texts are Section hypotheses quantified over the float state, and the self text is quantified
   the same way in the loop's segments; after put_string (the key) and the self call the walk goes on at the call's
   fx'. The item loop (formerly PRW_write_value_lp.v, WalkS7bR.WvLoopR's donor) is merged here: wvl_seg_210 / 193 /
   185 / 181 / 162 / 158 / 153 and wv_loop (induction over the items, at every current float state).
   The batch kit RE-FIT (WalkS7bR.WriteValueB, 2026-10-30; the batch kit's texts a working branch 44123abafeb7:
   PRH_FnWriter d89d3c67b78c, PRH_Base 6d0ab94b8f66): DW is gone (prh_univ_closure B CTX0); every writer text takes
   PRH_Base.prh_cons_from at entry, supplied to put / indent / put_string / the self call from the caller's window
   (wv_cons_next); the LIVE_<fn> sums are replaced by PRH_Base.prh_live_evs, supplied from the caller's by the blocks
   arms of prhWriter_blk (wv_live_next); the posts carry prh_granted (S7a_WriterRet's prhWriter_retg /
   prhWriter_ret_pos); wv_gap is DELETED (src_rd / cstr_ok lost their `+ 8`): twrite_value_specI is the batch kit's
   twrite_value_specX verbatim.
   ON THE KIT'S CUT 7cdbb61b5fa0 (the one rebind, 2026-10-30): merged forward with no proof or statement change; the cut's
   PRH_FnWriter is the same blob d89d3c67b78c, its PRH_Base is ef7c8ca98529 and its YCbqG 219748197d6b.
   Numerals: 4 (LENGTH: instruction bytes), 176 (LENGTH: write_value's own frame, its `addi sp, sp, -176`),
   0 .. 56 (LENGTH: the node's field offsets and its size, PRH_Reader pj_hdrR), 2 ^ 46 / 2 ^ 47 (LENGTH: the stack
   atom's range), 2 ^ 44 (LENGTH: the shadow span), 6 (WORD: the largest tag, PjTree.tag). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
(* the re-hiding move: SRr' / wle' (YA0nH) and their bind / mono / return (YSRrG), preset's zone RZ_cf
   (YGcfRehidePost), the caller-window call rules over a world relation (YCbqGcallW) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YCbqGcallW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the function's place in the generated listing, and the .rodata addends the generated listing carries ----
   (no typed image value: both read a generated source) *)
Definition WV_SLOT : nat := A_prog_slot AS_write_value.
Definition AF_write_value : Z := 4 * Z.of_nat WV_SLOT.
(* the addend of the PAddHi / PLdHi at write_value + 4 k (the .rodata literal the code forms there) *)
Definition wv_addhi_off (k : nat) : Z :=
  match nth (WV_SLOT + k) A_prog_listing (PW 0) with
  | PAddHi _ _ _ _ off => off
  | PLdHi _ _ _ _ off _ _ => off
  | _ => 0
  end.
(* the jump table of the tag switch: the PAddHi at write_value + 4 * 31 (A 0x86d08) *)
Definition WV_JT : Z := wv_addhi_off 31.
(* the word of the switch's `jr a1` at write_value + 4 * 35 (A 0x86d18), read out of the listing *)
Definition WV_JR_W : Z := match nth (WV_SLOT + 35) A_prog_listing (PW 0) with PW w => w | _ => 0 end.

(* ---- the pure pieces of a container, as the item loop needs them: the inner fix of WriterValue.wvpieces named, its
   split at an index, and its behaviour on an appended item list (the loop's invariant is about the first i items) ---- *)
Fixpoint wv_arr_go (p : bool) (dep : Z) (i : nat) (l : list PjTree.jv) : list (list Z) :=
  match l with
  | [] => []
  | x :: r => WriterValue.wcomma i ++ WriterValue.wind p (dep + 1) ++ WriterValue.wvpieces x p (dep + 1)
              ++ wv_arr_go p dep (S i) r
  end.

Fixpoint wv_obj_go (p : bool) (dep : Z) (i : nat) (l : list (list Z * PjTree.jv)) : list (list Z) :=
  match l with
  | [] => []
  | (k, x) :: r => WriterValue.wcomma i ++ WriterValue.wind p (dep + 1) ++ WriterSpec.spieces k
                  ++ [WriterValue.wsep p] ++ WriterValue.wvpieces x p (dep + 1) ++ wv_obj_go p dep (S i) r
  end.

Lemma wv_arr_pieces : forall items p dep,
  WriterValue.wvpieces (PjTree.JArr items) p dep =
  [91] :: wv_arr_go p dep 0 items
       ++ (match items with [] => [] | _ :: _ => WriterValue.wind p dep end) ++ [[93]].
Proof.
intros items p dep. cbn [WriterValue.wvpieces]. f_equal. f_equal.
generalize 0%nat as i. induction items as [|x r IH]; intros i; [reflexivity|].
cbn [wv_arr_go]. rewrite <- IH. reflexivity.
Qed.

Lemma wv_obj_pieces : forall members p dep,
  WriterValue.wvpieces (PjTree.JObj members) p dep =
  [123] :: wv_obj_go p dep 0 members
        ++ (match members with [] => [] | _ :: _ => WriterValue.wind p dep end) ++ [[125]].
Proof.
intros members p dep. cbn [WriterValue.wvpieces]. f_equal. f_equal.
generalize 0%nat as i. induction members as [|[k x] r IH]; intros i; [reflexivity|].
cbn [wv_obj_go]. rewrite <- IH. reflexivity.
Qed.

Lemma wv_arr_go_app : forall l1 l2 p dep i,
  wv_arr_go p dep i (l1 ++ l2) = wv_arr_go p dep i l1 ++ wv_arr_go p dep (i + length l1) l2.
Proof.
induction l1 as [|x l1 IH]; intros l2 p dep i; cbn [app wv_arr_go length].
- rewrite Nat.add_0_r. reflexivity.
- replace (i + S (length l1))%nat with (S i + length l1)%nat by lia.
  rewrite IH, !app_assoc. reflexivity.
Qed.

Lemma wv_obj_go_app : forall l1 l2 p dep i,
  wv_obj_go p dep i (l1 ++ l2) = wv_obj_go p dep i l1 ++ wv_obj_go p dep (i + length l1) l2.
Proof.
induction l1 as [|[k x] l1 IH]; intros l2 p dep i.
- cbn [app wv_obj_go length]. rewrite Nat.add_0_r. reflexivity.
- change (((k, x) :: l1) ++ l2) with ((k, x) :: (l1 ++ l2)).
  cbn [wv_obj_go length].
  replace (i + S (length l1))%nat with (S i + length l1)%nat by lia.
  rewrite IH, !app_assoc. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

Definition WV_Bx : sv := SOff 32 0.
Definition WV_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* the symbolic entry state: write_value's own frame, the GOT word and the shadow-base cell, and the tree node at v
   (read only: 56 bytes, its tag / str / kids / keys / n fields as chunks) *)
Definition wv_regions (tg : Z) : smem :=
  [ stack_region 176; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 11%nat) 0 56 0 0
      [ YP09.mkChunk 0 (CVal 4 (SLit tg));
        YP09.mkChunk 16 (CVal 8 (SOff 34 0));
        YP09.mkChunk 24 (CVal 8 (SOff 35 0));
        YP09.mkChunk 32 (CVal 8 (SOff 36 0));
        YP09.mkChunk 40 (CVal 8 (SOff 37 0)) ] ].
(* atom ranges are CLOSED numerals so the engine's vm_compute runs on a closed term: CEIL_MAX is YM05's bound on
   every run's alloc_ceiling (a class field, not a numeral) *)
Definition wv_facts (tg : Z) : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (11%nat, mkAF 4096 (2 ^ 47 - 56) 3) ] [] [].
Definition wv_ss (tg : Z) : sstate := mkSS AF_write_value sr_atoms (wv_regions tg) None (wv_facts tg).
Definition wv_SH : list shent := [ mkSHE 11 0 56 ].
(* the entry environment: the registers, then the extra atoms 32 (shadow base), 33 (v), 34 .. 37 (str, kids, keys,
   n: the node's field values) and 38 (jw: the jump-table word the tag selects, an ATOM so the engine's terms stay
   closed; its value BASE + case - table is a class projection, not a numeral) *)
Definition wv_extra (v str kids keys nn jw : Z) : list word :=
  [ Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 v; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 nn;
    Z_to_bv 64 jw ].
Definition wv_E (regs : bvmap 5 word) (v str kids keys nn jw : Z) : env :=
  Eimg (Ereg regs (wv_extra v str kids keys nn jw)).

(* ---- the tag switch's jump table (A 0x86d04-0x86d18): seven rel32 words at WV_JT, each the offset of its case
   label FROM THE TABLE. The case labels are slot deltas from write_value's entry (DERIVED, measured on
   Listing_prog: null 121, false 125, true 102, number 105, string 61, array / object 36), not addresses. ---- *)
Definition WV_CASE (k : nat) : Z :=
  match k with
  | 0%nat => 121 | 1%nat => 125 | 2%nat => 102 | 3%nat => 105 | 4%nat => 61 | _ => 36
  end.
Definition AF_wv_case (k : nat) : Z := AF_write_value + 4 * WV_CASE k.
Definition WV_JTW (k : nat) : Z := BASE + AF_wv_case k - (VAL (A_OBJ 2) + WV_JT).
(* the one table word the tag tg selects (read only), its value the atom 38 *)
Definition wv_jt_region (tg : Z) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 2)) (WV_JT + 4 * tg) (WV_JT + 4 * tg + 4) 0 0
    [ YP09.mkChunk (WV_JT + 4 * tg) (CVal 4 (SOff 38 0)) ].
Definition wv_ss2 (tg : Z) : sstate :=
  add_atom (mkSS AF_write_value sr_atoms (wv_jt_region tg :: wv_regions tg) None (wv_facts tg))
    38 (mkAF 0 (2 ^ 31 - 1) 0).

(* ---- THE ITEM LOOP's HEAD (A 0x86ef0, write_value + 4 * 153), seated by hand at every iteration: every register is
   its own atom except the five the code derived from v (s2 = shadow (v + 40), s4 = v + 40, s7 = v + 24,
   s10 = shadow (v + 24), s11 = shadow v); the own frame's slots (sp = the head's sp, atom 2); the node's tag, kids,
   keys and n (base v = s1, atom 9); for an object the current key slot (base atom 39 = keys + 8 i, its word the atom
   40). Extra atoms: 32 the shadow base, 33 dep, 34 the separator literal, 35 the comma literal, 36 kids, 37 keys,
   38 n, 39 keys + 8 i, 40 the key pointer, 41 kids + 56 i, 42 .. 54 the entry's s0, s1, s2 .. s11, ra (the saved
   slots 160, 152, 144 .. 72, 168). Two aliases name keys + s6 (atom 39) and kids + s9 (atom 41), so the loop's two
   indexed addresses stay atoms. Measured layout: the engine's own state at the head (cb, this base, 13:08Z). ---- *)
Definition WVH_PC : Z := AF_write_value + 4 * 153.
Definition wvh_sh (k : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0).
Definition wvh_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18%bv (wvh_sh 9 40)) 20%bv (SOff 9 40)) 23%bv (SOff 9 24))
    26%bv (wvh_sh 9 24)) 27%bv (wvh_sh 9 0).
Definition wvh_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 176 0 176
    [ YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
      YP09.mkChunk 24 (CVal 8 (wvh_sh 9 32));
      YP09.mkChunk 32 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)));
      YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 9 32));
      YP09.mkChunk 56 (CVal 8 (SOff 35 0)); YP09.mkChunk 64 (CVal 8 (SOff 32 0));
      YP09.mkChunk 72 (CVal 8 (SOff 53 0)); YP09.mkChunk 80 (CVal 8 (SOff 52 0));
      YP09.mkChunk 88 (CVal 8 (SOff 51 0)); YP09.mkChunk 96 (CVal 8 (SOff 50 0));
      YP09.mkChunk 104 (CVal 8 (SOff 49 0)); YP09.mkChunk 112 (CVal 8 (SOff 48 0));
      YP09.mkChunk 120 (CVal 8 (SOff 47 0)); YP09.mkChunk 128 (CVal 8 (SOff 46 0));
      YP09.mkChunk 136 (CVal 8 (SOff 45 0)); YP09.mkChunk 144 (CVal 8 (SOff 44 0));
      YP09.mkChunk 152 (CVal 8 (SOff 43 0)); YP09.mkChunk 160 (CVal 8 (SOff 42 0));
      YP09.mkChunk 168 (CVal 8 (SOff 54 0)) ].
Definition wvh_node (tg : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0
    [ YP09.mkChunk 0 (CVal 4 (SLit tg)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
      YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 38 0)) ].
Definition wvh_key : YP09.region := YP09.mkRegion (Some 39%nat) 0 8 0 0 [ YP09.mkChunk 0 (CVal 8 (SOff 40 0)) ].
Definition wvh_mem (tg : Z) : smem := wvh_frame :: wvh_node tg :: (if Z.eqb tg 6 then [wvh_key] else []).
Definition wvh_facts (tg : Z) : facts :=
  mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
             (9%nat, mkAF 4096 (2 ^ 47 - 56) 3) ] ++
           (if Z.eqb tg 6 then [(39%nat, mkAF 4096 (2 ^ 47 - 8) 3)] else []))
    [ mkAC BC_NE (SOff 38 0) (SLit 0) ]
    ([ (SAlu ALU_ADD (SOff 36 0) (SOff 25 0), SOff 41 0) ] ++
     (if Z.eqb tg 6 then [(SAlu ALU_ADD (SOff 37 0) (SOff 22 0), SOff 39 0)] else [])).
Definition wv_ssH (tg : Z) : sstate := mkSS WVH_PC wvh_regs (wvh_mem tg) None (wvh_facts tg).
Definition wvh_SH (tg : Z) : list shent := mkSHE 9 0 56 :: (if Z.eqb tg 6 then [mkSHE 39 0 8] else []).
(* the head environment: the registers, then atoms 32 .. 54 *)
Definition wvh_extra (dep sep comma kids keys nn ka kp ca : Z) (sv13 : list Z) : list word :=
  map (Z_to_bv 64) ([SHADOW_OFF; dep; sep; comma; kids; keys; nn; ka; kp; ca] ++ sv13).
Definition wv_EH (regs : bvmap 5 word) (dep sep comma kids keys nn ka kp ca : Z) (sv13 : list Z) : env :=
  Eimg (Ereg regs (wvh_extra dep sep comma kids keys nn ka kp ca sv13)).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* image facts of the instance, discharged at PI_prog_A (A_entry_write_value / A_prog_obj_img) *)
Hypothesis Hent : SIGMA AS_write_value = BASE + AF_write_value.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* the memory invariant the m-form posts keep (the kit's fQmn over YAkMemnorm, PRH_Base.v blob ef7c8ca98529 at the cut): each walk
   lemma instantiates the runner's invariant ONCE as `fun m => memnorm mem0 -> memnorm m` (srr_inv_laws_imp at
   srr_inv_laws_memnorm_k); each callee keep comes from that callee's own m-form post. *)
(* ---- THE FLOAT STATE (the internal file REFIT-WRITER.md's float-threading design, the #102 kit's float posts): fregs_kept_x is
   reflexive and transitive (YCbqG.v:26 defines it pointwise; no copy of these two in the kit); fpre's one float
   conjunct (FRM0-ENTRY) moves to any float state whose rounding mode is 0; a caller-window post that keeps the
   float state is the float form at an earlier state when the rounding mode is 0 and fs0-fs11 are kept ---- *)
Lemma wv_fk_refl : forall f : YK11.FPState, fregs_kept_x f f.
Proof. intros f r _. reflexivity. Qed.
Lemma wv_fk_trans : forall f1 f2 f3 : YK11.FPState, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma wv_fpre_fx : forall (f1 f2 : YK11.FPState) STK ly S Hp (W : world SEGS) regs mem md ch,
  fpre (fx := f1) B ARx STK ly S Hp W regs mem md ch -> YK0o.frm_zero (@YK11.fp_csr f2) ->
  fpre (fx := f2) B ARx STK ly S Hp W regs mem md ch.
Proof.
intros f1 f2 STK ly S Hp W regs mem md ch (H1 & H2 & H3 & H4 & _) Hz.
exact (conj H1 (conj H2 (conj H3 (conj H4 Hz)))).
Qed.
(* over any world relation R of the journal: the plain posts are the R forms at wle (PRH_Base fpostW_R_wle) *)
Lemma wv_postWF_of_W : forall {R : world SEGS -> world SEGS -> Prop} (f0 f1 : YK11.FPState) STK d FP regs ly S Hp
  (W : world SEGS) mem md
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  YK0o.frm_zero (@YK11.fp_csr f1) -> fregs_kept_x f0 f1 ->
  fpostWR (fx := f1) B ARx SK R STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWFR (fx := f0) B ARx SK R STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R f0 f1 STK d FP regs ly S Hp W mem md Q W' c' HZ HK
  (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HX & HP & HQ).
exists f1, ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact HZ|]. split; [exact HK|]. split; [exact HJ|]. split; [exact HX|].
split; [exact HP | exact HQ].
Qed.

Section h1. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).

(* ---- THE RE-HIDING MOVE (a free, or a realloc of a live block, re-hides shadow): a run that crosses one is stated at
   SRr' SEGS RZ_cf with its journal at wle' SEGS RZ_cf (YA0nH). A stretch that crosses none runs at SRr and enters the
   primed form through wv_srr_pre; its journal enters wle' through wv_jlift (wle_wle'). ---- *)
Lemma wv_srr_pre : forall (W : world SEGS) c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => SRr' SEGS YGcfRehidePost.RZ_cf W' c' Q) -> SRr' SEGS YGcfRehidePost.RZ_cf W c Q.
Proof.
intros W c Q H.
exact (SRr'_bind SEGS YGcfRehidePost.RZ_cf W c _ Q (SRr_SRr' SEGS YGcfRehidePost.RZ_cf W c _ H) (fun W' c' _ HQ => HQ)).
Qed.
Lemma wv_jlift : forall STK sp0 FP ly S Hp (W : world SEGS) mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
    STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_xwR_mono (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k [] HJ).
Qed.

(* two byte ranges, one in the image's segments and one in none, are disjoint (the S3 walk's disj_img) *)
Lemma wv_disj_img : forall g o n, 0 < n ->
  (forall i, 0 <= i < 8 -> in_img SEGS (g + i)) -> (forall a, o <= a < o + n -> ~ in_img SEGS a) ->
  o + n <= g \/ g + 8 <= o.
Proof.
intros g o n Hn Hg Ho. destruct (Z_le_gt_dec (o + n) g) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (g + 8) o) as [H'|H']; [right; exact H'|]. exfalso.
assert (Ha : o <= Z.max o g < o + n) by lia. apply (Ho _ Ha).
replace (Z.max o g) with (g + (Z.max o g - g)) by lia. apply Hg. lia.
Qed.

(* the same at any width of the image range (the tag table's words are four bytes) *)
Lemma wv_disj_img_n : forall g gn o n, 0 < n -> 0 < gn ->
  (forall i, 0 <= i < gn -> in_img SEGS (g + i)) -> (forall a, o <= a < o + n -> ~ in_img SEGS a) ->
  o + n <= g \/ g + gn <= o.
Proof.
intros g gn o n Hn Hgn Hg Ho. destruct (Z_le_gt_dec (o + n) g) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (g + gn) o) as [H'|H']; [right; exact H'|]. exfalso.
assert (Ha : o <= Z.max o g < o + n) by lia. apply (Ho _ Ha).
replace (Z.max o g) with (g + (Z.max o g - g)) by lia. apply Hg. lia.
Qed.

(* a caller's chain at one frame base reads at the SAME base for any lower window bound the records clear: every
   record of a chain from v sits at or above v (fpchain_fps_increase), so the bound only has to clear v *)
Lemma wv_achain_at : forall ly rd sp sp' v ch, achain ly rd sp v ch -> sp' + 16 <= v -> achain ly rd sp' v ch.
Proof.
intros ly rd sp sp' v ch [H | (H1 & H2 & H3 & H4 & H5)] Hv; [left; exact H|].
right. split; [exact Hv|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
eapply Forall_impl; [|exact (fpchain_fps_increase (rdword rd) v (ly_top ly) ch H4)].
intros r Hr. cbn beta in Hr. lia.
Qed.

(* ---- the entry state of the walk, for a node v anywhere the text puts it: below the own frame (a harness block or
   a fake frame, both below alloc_ceiling) or above sp (the real stack), off the shadow band and off the image ---- *)
Lemma wv_entry : forall ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn jw,
  176 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= spZ regs - 176 \/ spZ regs <= v) ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a /\ writable_at SEGS (mrestrict (w_H W) mem) a) ->
  val_mem SEGS (mrestrict (w_H W) mem) v 4 tg -> 0 <= tg < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 16) 8 str -> 0 <= str < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 24) 8 kids -> 0 <= kids < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 40) 8 nn -> 0 <= nn < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  st_ok_pi SEGS VAL (wv_E regs v str kids keys nn jw) (wv_ss tg)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_write_value)) mem (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx wv_SH (wv_E regs v str kids keys nn jw) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn jw HSTK HPRE H10 H11 H12 H13
  Hv8 Hv4096 Hv47 Hvst Hband Hvimg Vtg Rtg Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn Hra.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_val_range (A_OBJ 0)) as RG. pose proof (pa_val_range (A_OBJ 12)) as RC.
assert (Hnimg : forall a, v <= a < v + 56 -> ~ in_img SEGS a) by (intros a Ha; exact (proj1 (Hvimg a Ha))).
assert (DG : v + 56 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v).
{ apply (wv_disj_img (VAL (A_OBJ 0)) v 56); [lia | intros i Hi; exact (proj1 (Hobj i Hi)) | exact Hnimg]. }
assert (DC : v + 56 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v).
{ apply (wv_disj_img (VAL (A_OBJ 12)) v 56); [lia | intros i Hi; exact (proj2 (Hobj i Hi)) | exact Hnimg]. }
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_segs_low (VAL (A_OBJ 0) + 7) (proj1 (Hobj 7 ltac:(lia)))) as LG.
pose proof (pa_segs_low (VAL (A_OBJ 12) + 7) (proj2 (Hobj 7 ltac:(lia)))) as LC.
rewrite restrict_mkst_fx.
set (E := wv_E regs v str kids keys nn jw).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn jw)) k)
  by (intros k Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E34 : ew E 34 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 kids) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 keys) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 nn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hkl : 0 <= kLowMemEnd <= YM05.alloc_ceiling) by (unfold kLowMemEnd; lia).
assert (Hv64 : 0 <= v < 2 ^ 64) by lia.
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
split.
- unfold wv_ss. apply pa_entry_st_ok_full.
  + unfold E, wv_E. apply (regs_ok_agree 32 (Ereg regs (wv_extra v str kids keys nn jw))).
    * split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    * vm_compute. reflexivity.
    * apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + unfold wv_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 WV_Bx SHADOW_OFF);
        [cbn [sv_denot WV_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 11%nat v E11) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ v 0 4 (SLit tg) tg);
         [cbn [sv_denot]; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vtg].
      -- apply (chunk_ok_val SEGS E _ v 16 8 (SOff 34 0) str);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vstr].
      -- apply (chunk_ok_val SEGS E _ v 24 8 (SOff 35 0) kids);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vkids].
      -- apply (chunk_ok_val SEGS E _ v 32 8 (SOff 36 0) keys);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vkeys].
      -- apply (chunk_ok_val SEGS E _ v 40 8 (SOff 37 0) nn);
         [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vnn].
  + apply pairwise_disjoint_of_extents.
    unfold wv_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 11%nat v E11) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowMemEnd in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [wv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E11, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, wv_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E WV_Bx 11 v 56 v 0 56 Hra).
  + unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* ---- the entry state WITH the table word the tag selects (atom 38 = jw), from that word in the current memory
   and the fact that its 4 bytes miss the own frame, the node, the GOT word and the shadow cell ---- *)
Lemma wv_entry2 : forall E tg ms sp vv jw,
  st_ok_pi SEGS VAL E (wv_ss tg) ms ->
  base_val E (Some (A_OBJ 2)) = VAL (A_OBJ 2) ->
  base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0) ->
  base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12) ->
  base_val E (Some 2%nat) = sp -> base_val E (Some 11%nat) = vv ->
  ew E 38 = Z_to_bv 64 jw -> 0 <= jw <= 2 ^ 31 - 1 ->
  val_mem SEGS (ms_mem ms) (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 jw ->
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * tg /\ VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= 2 ^ 64 ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= sp - 176 \/ sp <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= vv \/ vv + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  region_wf (wv_jt_region tg) = true ->
  st_ok_pi SEGS VAL E (wv_ss2 tg) ms.
Proof.
intros E tg ms sp vv jw HS Hbase Hbg Hbc Hbsp Hbv E38 Hjw Hval Hlohi Dsp Dg Dc Dv Hwf.
unfold wv_ss2. apply st_ok_pi_add_fact.
2:{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
apply (st_ok_pi_add_region E (wv_ss tg) ms (wv_jt_region tg) HS).
- exact Hwf.
- unfold region_ok, wv_jt_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Hbase. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E (ms_mem ms) (VAL (A_OBJ 2)) (WV_JT + 4 * tg) 4 (SOff 38 0) jw).
  + cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + cbn. lia.
  + zside.
  + replace (VAL (A_OBJ 2) + (WV_JT + 4 * tg)) with (VAL (A_OBJ 2) + WV_JT + 4 * tg) by lia. exact Hval.
- unfold wv_ss, wv_regions, wv_jt_region, stack_region, got_regionP, bcell_regionP.
  cbn [ss_mem all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite Hbase, Hbg, Hbc, Hbsp, Hbv.
  repeat split; lia.
Qed.

(* ---- the tag switch's indirect jump (A 0x86d18, write_value + 4 * 35): a1 holds the case label the table word
   selects, so the walk goes on at the case's own offset. MEASURED with the engine on this file's entry state at
   tag 5: the run from wv_ss2 5 stops at this pc with
   a1 = SAlu ALU_ADD (SOff 38 WV_JT) (SOff (A_OBJ 2) 0), that is jw + WV_JT + VAL (A_OBJ 2), which at
   jw = WV_JTW 5 is BASE + AF_wv_case 5 (cb on base preset-tree-at-2026-10-28T23-23-18Z.tsv (sha256 eb0f0ad37373; internal record), log, the internal file build-20261029T075917Z.log). ---- *)
Lemma wv_jr_step : forall E ss ms W md Q tgt,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_pc ss = AF_write_value + 4 * 35 ->
  ss_resv ss = None ->
  getr (ms_regs ms) 11 = Z_to_bv 64 tgt ->
  0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 ->
  (forall mat' ms1,
     ms1 = mkst (ms_regs ms) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom SEGS) ->
     st_ok SEGS E (mkSST tgt (ss_regs ss) (ss_fregs ss) (ss_mem ss) None (ss_facts ss)) (restrict (w_H W) ms1) ->
     SRr SEGS W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros E ss ms W md Q tgt HS Hpc Hrv H11 Hr Hev HK.
apply (SRr_jr_pi (PL := PL_prog_A) (PI := PA) W E ss ms md Q WV_JR_W (11%bv : bv 5) tgt HS Hrv).
- rewrite Hpc. (vm_compute; reflexivity).
- vm_refl_bv.
- exact H11.
- exact Hr.
- exact Hev.
- exact HK.
Qed.

(* the state wv_jr_step hands on, read back as a listing-relative state at the case offset c (definitional: abs_ss
   adds BASE to the pc and keeps every other field) *)
Lemma wv_pi_at : forall E ss c ms,
  st_ok SEGS E (mkSST (BASE + c) (ss_regs ss) (ss_fregs ss) (ss_mem ss) None (ss_facts ss)) ms ->
  st_ok_pi SEGS VAL E (mkSST c (ss_regs ss) (ss_fregs ss) (ss_mem ss) None (ss_facts ss)) ms.
Proof.
intros E ss c ms H. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
exact H.
Qed.

(* ---- the seated entry state: wv_entry + the table word of tag tg (wv_entry2) ---- *)
Lemma wv_seat : forall ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn,
  176 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= spZ regs - 176 \/ spZ regs <= v) ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a /\ writable_at SEGS (mrestrict (w_H W) mem) a) ->
  val_mem SEGS (mrestrict (w_H W) mem) v 4 tg -> 0 <= tg < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 16) 8 str -> 0 <= str < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 24) 8 kids -> 0 <= kids < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 40) 8 nn -> 0 <= nn < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 (WV_JTW (Z.to_nat tg)) ->
  0 <= WV_JTW (Z.to_nat tg) <= 2 ^ 31 - 1 ->
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * tg /\ VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= 2 ^ 64 ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= spZ regs - 176 \/ spZ regs <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
  region_wf (wv_jt_region tg) = true ->
  st_ok_pi SEGS VAL (wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) (wv_ss2 tg)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_write_value)) mem (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx wv_SH (wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn HSTK HPRE H10 H11 H12 H13
  Hv8 Hv4096 Hv47 Hvst Hband Hvimg Vtg Rtg Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn Hra
  HJTv HJTr HJTlo HJTs HJTg HJTc HJTn Hwf.
destruct (wv_entry ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn (WV_JTW (Z.to_nat tg)) HSTK
  HPRE H10 H11 H12 H13 Hv8 Hv4096 Hv47 Hvst Hband Hvimg Vtg Rtg Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn Hra)
  as [HS0 SHOK].
split; [|exact SHOK].
set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) in *.
assert (EL : forall k, (k < A_TEXT)%nat ->
    ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) k)
  by (intros k Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk).
assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat tg)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z)
  by (intros k z Hk Hz; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hz).
apply (wv_entry2 E tg _ (spZ regs) v (WV_JTW (Z.to_nat tg)) HS0).
- apply (VB (A_OBJ 2) _ EJ). apply pa_val_range.
- apply (VB (A_OBJ 0) _ EG). apply pa_val_range.
- apply (VB (A_OBJ 12) _ EC). apply pa_val_range.
- cbn [base_val]. rewrite E2. reflexivity.
- apply (VB 11%nat v E11). lia.
- exact E38.
- exact HJTr.
- cbn [ms_mem restrict mkst]. exact HJTv.
- exact HJTlo.
- exact HJTs.
- exact HJTg.
- exact HJTc.
- exact HJTn.
- exact Hwf.
Qed.

(* ---- the jr target: a1 = jw + WV_JT + VAL (A_OBJ 2) (the engine's term at the jr, measured) is the case label of
   tag k, given the image fact jw = WV_JTW k; and that target is a 4-aligned text address ---- *)
Lemma wv_case_bounds : forall k, 0 <= AF_wv_case k < 2 ^ 32.
Proof.
intros k. assert (HA : 0 <= AF_write_value < 2 ^ 31) by (unfold AF_write_value, WV_SLOT; vm_compute; split; congruence).
unfold AF_wv_case. destruct k as [|[|[|[|[|k]]]]]; cbn [WV_CASE]; lia.
Qed.

Lemma wv_jr_target : forall E k,
  ew E 38 = Z_to_bv 64 (WV_JTW k) -> ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)) ->
  0 <= WV_JTW k <= 2 ^ 31 - 1 ->
  alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned (ew E 38) + WV_JT)) (ew E (A_OBJ 2)) = Z_to_bv 64 (BASE + AF_wv_case k) /\
  0 <= BASE + AF_wv_case k < 2 ^ 64 /\ (BASE + AF_wv_case k) mod 2 = 0.
Proof.
intros E k E38 EJ Hjw.
assert (HJT : 0 <= WV_JT < 2 ^ 32) by (unfold WV_JT, wv_addhi_off, WV_SLOT; vm_compute; split; congruence).
pose proof (wv_case_bounds k) as HAF. pose proof (pa_val_range (A_OBJ 2)) as HV.
pose proof (@pa_B_ok _ A_prog_listing PA) as (HB0 & HB1 & HB4).
assert (HAF4 : AF_wv_case k mod 4 = 0).
{ unfold AF_wv_case, AF_write_value. rewrite Z.add_mod, Z.mul_comm, Z_mod_mult, Z.add_0_l by lia.
  rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
split; [|split; [lia|]].
- rewrite E38, EJ, (unsigned_lit_small (WV_JTW k)) by lia.
  rewrite zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. f_equal.
  cbn [zalu_raw]. rewrite !YP0m.zcanon_small by lia. unfold WV_JTW. lia.
- assert (H4 : (BASE + AF_wv_case k) mod 4 = 0) by (rewrite Z.add_mod, HB4, HAF4 by lia; reflexivity).
  apply Z.mod_divide in H4; [|lia]. destruct H4 as [q Hq]. rewrite Hq.
  replace (q * 4) with ((2 * q) * 2) by lia. apply Z_mod_mult.
Qed.

(* ---- a read-only image value read in the current memory: the image fact is stated over the ROM alone
   (`val_mem SEGS (fun _ => None)`: mbyte falls through to seg_rom), and fpre's arodata_okP carries it to any state
   whose image bytes are not the runtime's own and not errno ---- *)
Lemma wv_ro_val : forall (W : world SEGS) (mem : word -> option byte) a n v,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (forall i, 0 <= i < Z.of_nat n -> in_roP SEGS pa_relro_lo pa_relro_hi (a + i) /\
     ~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4)) ->
  val_mem SEGS (fun _ => None) a n v ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v HRO Hro Hv k Hk.
specialize (Hv k Hk). unfold mbyte in Hv. cbn beta iota in Hv.
destruct (Hro (Z.of_nat k) ltac:(lia)) as (Hr & Ho & He).
pose proof (HRO (a + Z.of_nat k) Hr Ho He) as Ha. unfold aview in Ha. rewrite Hv in Ha. cbn [option_map] in Ha.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b1|] eqn:Hm; cbn [option_map] in Ha;
  [|discriminate Ha].
injection Ha as Ha. f_equal. apply bv_eq. exact Ha.
Qed.

(* ---- BYTE AGREEMENT: a byte outside the image has no ROM backing, so the view determines the memory, and a byte
   set the view agrees on is a pj_agreeR set: this is what carries the tree across every call ---- *)
Lemma wv_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> seg_rom SEGS (Z_to_bv 64 a) = None.
Proof.
intros a Ha Hn. apply MemNorm.seg_rom_unmapped. rewrite unsigned_lit_small by exact Ha.
destruct (find_segment SEGS a 1) as [s|] eqn:E; [exfalso | reflexivity].
destruct (find_segment_hit SEGS a 1 s E) as (Hin & Hlo & Hhi). apply Hn. exists s. split; [exact Hin | lia].
Qed.

Lemma wv_mrestrict_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H' m' a = aview SEGS H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn Heq. pose proof (mbyte_of_aview SEGS H H' m m' a Heq) as X.
unfold mbyte in X. rewrite (wv_rom_none a Ha Hn) in X.
destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|]; destruct (mrestrict H m (Z_to_bv 64 a)) as [b|];
  first [reflexivity | discriminate X | exact X].
Qed.

Lemma wv_agree_of_aview : forall (W1 W2 : world SEGS) (m1 m2 : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) ->
  (forall x, X x -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) ->
  pj_agreeR SEGS (mrestrict (w_H W1) m1) (mrestrict (w_H W2) m2) X.
Proof.
intros W1 W2 m1 m2 X Hr Heq x Hx. destruct (Hr x Hx) as [Hb Hi]. split.
- apply (mbyte_of_aview SEGS). exact (Heq x Hx).
- apply (writable_at_eq SEGS). exact (wv_mrestrict_of_aview _ _ _ _ x Hb Hi (Heq x Hx)).
Qed.

(* THE TREE ACROSS A CALL: the node keeps its bytes when the view agrees on its footprint *)
Lemma wv_nodeR_keep : forall (W1 W2 : world SEGS) (m1 m2 : word -> option byte) Lam v t D,
  pj_nodeR SEGS (mrestrict (w_H W1) m1) (prh_lin Lam) v t D ->
  (forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) ->
  (forall x, pj_footR v D x -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) ->
  pj_nodeR SEGS (mrestrict (w_H W2) m2) (prh_lin Lam) v t D.
Proof.
intros W1 W2 m1 m2 Lam v t D Hn Hr Heq.
exact (pj_nodeR_frame SEGS t _ _ _ _ _ Hn (wv_agree_of_aview W1 W2 m1 m2 (pj_footR v D) Hr Heq)).
Qed.

(* two distinct members of a pairwise-disjoint list are disjoint (YG0f's pairwise; YI04's pairwise_in2 is another) *)
Lemma wv_pairwise_in2 : forall {X} (R : X -> X -> Prop) l x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in Hx, Hy; [destruct Hx|].
destruct HP as [HFa HP]. rewrite Forall_forall in HFa.
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. exact (Hne eq_refl).
- left. exact (HFa _ Hy).
- right. exact (HFa _ Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.

(* a member of the left half and one of the right half of a pairwise-disjoint append are disjoint *)
Lemma wv_pairwise_app : forall {X} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; cbn in Hx; [destruct Hx|].
cbn in HP. destruct HP as [HFa HP]. rewrite Forall_forall in HFa.
destruct Hx as [<-|Hx]; [apply HFa; apply in_or_app; right; exact Hy | exact (IH l2 x y HP Hx Hy)].
Qed.

(* a pair of integers has a decidable equality (for the "block still live" case split) *)
Lemma wv_zz_dec : forall p q : Z * Z, {p = q} + {p <> q}.
Proof.
intros [p1 p2] [q1 q2]. destruct (Z.eq_dec p1 q1) as [->|H1]; [|right; congruence].
destruct (Z.eq_dec p2 q2) as [->|H2]; [left; reflexivity | right; congruence].
Qed.

(* ---- THE LEDGER: read through the kit's named projections (PRH_Base.v d1cbe3c301d6, Section ledger_proj) only; these
   three and wv_led_keep are the walk's one place for them ---- *)
Lemma wv_led_hbs : forall {most own : Z} ly S Hp W mem Lam peak cnt fail ran,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  forall ak, In ak Lam -> prh_hblock (PA := PA) B ly S Hp W mem (fst ak) (snd ak).
Proof.
intros most own ly S Hp W mem Lam peak cnt fail ran LG. pose proof LG as HF. apply prh_ledger_blocks in HF.
rewrite Forall_forall in HF. exact HF.
Qed.

Lemma wv_led_nodup : forall {most own : Z} ly S Hp W mem Lam peak cnt fail ran,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> NoDup (map fst Lam).
Proof. intros most own ly S Hp W mem Lam peak cnt fail ran LG. apply prh_ledger_nodup in LG. exact LG. Qed.

Lemma wv_led_cnt : forall {most own : Z} ly S Hp W mem Lam peak cnt fail ran,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= cnt.
Proof. intros most own ly S Hp W mem Lam peak cnt fail ran LG. apply prh_ledger_bounds in LG. lia. Qed.

(* ---- A TREE BLOCK ACROSS A CALL: a byte of a live harness block OTHER THAN THE BUFFER, outside the struct, is kept
   by the journal (its block cannot have gone: a gone block's every byte is in FP) ---- *)
Lemma wv_blk_keep : forall {most own : Z} {R : world SEGS -> world SEGS -> Prop} ly S Hp W mem md o buf cap Lam peak
    cnt fail ran a k0 x
    ly2 S2 Hp2 W2 mem2 md2 STK0 sp0 k,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k0) Lam -> a <> buf -> a <= x < a + k0 ->
  0 <= cap -> (cap <> 0 -> In (buf, cap) Lam) ->
  ~ (o <= x < o + 32) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK0 sp0 (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros most own R ly S Hp W mem md o buf cap Lam peak cnt fail ran a k0 x ly2 S2 Hp2 W2 mem2 md2 STK0 sp0 k
  HAR HLED Hin Hab Hx Hcap0 Hbuf Hoff HJ.
pose proof asan_consts as (C1 & _). pose proof cf_head_nonneg as Hh0.
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k0) Hin) as (Hk0 & Hbl & _ & Ha16 & _). cbn [fst snd] in Hk0, Hbl, Ha16.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k0 + cf_head) HAR Hbl)
  as (H16 & H4096 & Hpc & Happ & Hpre & Hpw).
assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
assert (Himg : ~ in_img SEGS x).
{ refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR _)).
  left. exists (a - cf_head), (k0 + cf_head). split; [exact Hbl | lia]. }
assert (HnFP : ~ inFP (prhWriter_cfp o buf cap) x).
{ intros Hf. unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [exact (Hoff Hf)|].
  unfold prhWriter_fp in Hf. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [exact (inFP_nil x Hf)|].
  pose proof (HF (buf, cap) (Hbuf Hc0)) as (_ & Hblb & _). cbn [fst snd] in Hblb.
  destruct Hf as (r & Hr & Hrr). unfold ablocks_fp in Hr. cbn [map In] in Hr.
  destruct Hr as [Hr | []]. subst r. cbn [fst snd] in Hrr.
  destruct (wv_pairwise_in2 zdisjoint _ (a - cf_head, req_size (k0 + cf_head))
      (buf - cf_head, req_size (cap + cf_head)) Hpw
      (in_map (fun b => (fst b, req_size (snd b))) _ _ Hbl)
      (in_map (fun b => (fst b, req_size (snd b))) _ _ Hblb)
      ltac:(intros E; injection E as E1 _; lia)) as [Hd|Hd];
    unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia. }
pose proof (ajxR_blk HJ) as KEEPBLK. pose proof (ajxR_gone HJ) as GONEFP.
set (i := x - (a - cf_head)).
assert (Hxi : x = a - cf_head + i) by (subst i; lia).
assert (Hib : 0 <= i < req_size (k0 + cf_head)) by (subst i; lia).
assert (Hin2 : In (a - cf_head, k0 + cf_head) (ablocks B ly2 S2)).
{ destruct (in_dec wv_zz_dec (a - cf_head, k0 + cf_head) (ablocks B ly2 S2)) as [Hi2|Hi2]; [exact Hi2|].
  exfalso. apply HnFP. rewrite Hxi.
  exact (GONEFP (a - cf_head) (k0 + cf_head) i Hbl Hi2 Hib). }
split; [split; [exact Hx64 | exact Himg]|].
rewrite Hxi. apply (KEEPBLK (a - cf_head) (k0 + cf_head) i Hbl Hin2 Hib).
rewrite <- Hxi. exact HnFP.
Qed.

(* ---- THE TREE'S FOOTPRINT ACROSS A CALL: every byte of pj_footR v D is kept, whichever of the kit's three locations the
   node has. The node's own 56 bytes: on the real stack they are in the caller window (kept outside FP) or above it
   (the journal's high clause); in a block or a frame, by the block / frame clause. Its blocks: wv_blk_keep. ---- *)
Lemma wv_foot_keep : forall {most own : Z} {R : world SEGS -> world SEGS -> Prop} ly S Hp W regs mem md STKv STK0 d o
    buf cap Lam peak cnt fail ran v D
    ly2 S2 Hp2 W2 mem2 md2 k,
  176 <= STKv -> 0 <= d ->
  ARx ly S Hp W mem md -> astk_ok STKv ly (spZ regs) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  0 <= cap -> (cap <> 0 -> In (buf, cap) Lam) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK0 (spZ regs + d) (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  forall x, pj_footR v D x ->
    (0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros most own R ly S Hp W regs mem md STKv STK0 d o buf cap Lam peak cnt fail ran v D ly2 S2 Hp2 W2 mem2 md2 k
  HSTK Hd HAR Hstk HLED HLOC HD Hoff Hcap0 Hbuf HJ HWIN x Hx.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
pose proof (ajxR_hi HJ) as KEEPHI. pose proof (ajxR_frm HJ) as KEEPFR.
destruct Hx as [Hhdr | (b & HbD & Hb)].
- destruct HLOC as [(Hv1 & Hv2) | [(y0 & z0 & Hin & Hyb & Hyv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
  + assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
    assert (Himg : ~ in_img SEGS x)
      by (intros Hi; pose proof (pa_segs_low x Hi); unfold kLowMemEnd in *; lia).
    assert (HnFP : ~ inFP (prhWriter_cfp o buf cap) x).
    { intros Hf. unfold prhWriter_cfp in Hf. apply inFP_cons in Hf.
      destruct Hf as [Hf | Hf]; [exact (Hoff x Hf (or_introl Hhdr))|].
      unfold prhWriter_fp in Hf. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [exact (inFP_nil x Hf)|].
      pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
      pose proof (HF (buf, cap) (Hbuf Hc0)) as (_ & Hblb & _). cbn [fst snd] in Hblb.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (buf - cf_head) (cap + cf_head) HAR Hblb)
        as (_ & _ & Hpc & _ & _ & _).
      destruct Hf as (r & Hr & Hrr). unfold ablocks_fp in Hr. cbn [map In] in Hr.
      destruct Hr as [Hr | []]. subst r. cbn [fst snd] in Hrr. lia. }
    split; [split; [exact Hx64 | exact Himg]|].
    destruct (Z_lt_le_dec x (spZ regs + d)) as [Hlt|Hge].
    * exact (HWIN x ltac:(lia) HnFP).
    * exact (KEEPHI x ltac:(lia) ltac:(lia)).
  + exact (wv_blk_keep ly S Hp W mem md o buf cap Lam peak cnt fail ran y0 z0 x ly2 S2 Hp2 W2 mem2 md2
      STK0 (spZ regs + d) k HAR HLED Hin Hyb ltac:(lia) Hcap0 Hbuf
      ltac:(intros Ho; exact (Hoff x Ho (or_introl Hhdr))) HJ).
  + destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (_ & Hfapp & _).
    destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (Hpw & Hfb).
    rewrite Forall_forall in Hfb. pose proof (Hfb (cid, pos) Hfr) as (Hf4096 & Hfc).
    cbn [fst snd] in Hf4096, Hfc.
    assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
    assert (Himg : ~ in_img SEGS x).
    { refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR _)).
      right. left. exists cid, pos. split; [exact Hfr | lia]. }
    assert (HnFP : ~ inFP (prhWriter_cfp o buf cap) x).
    { intros Hf. unfold prhWriter_cfp in Hf. apply inFP_cons in Hf.
      destruct Hf as [Hf | Hf]; [exact (Hoff x Hf (or_introl Hhdr))|].
      unfold prhWriter_fp in Hf. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [exact (inFP_nil x Hf)|].
      pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
      pose proof (HF (buf, cap) (Hbuf Hc0)) as (_ & Hblb & _). cbn [fst snd] in Hblb.
      destruct Hf as (r & Hr & Hrr). unfold ablocks_fp in Hr. cbn [map In] in Hr.
      destruct Hr as [Hr | []]. subst r. cbn [fst snd] in Hrr.
      pose proof (wv_pairwise_app zdisjoint _ _ (buf - cf_head, req_size (cap + cf_head))
          (frame_addr ly cid pos, fs_frame_bytes cid) Hpw
          (in_map (fun b0 => (fst b0, req_size (snd b0))) _ _ Hblb)
          (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) Hfr)) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia. }
    split; [split; [exact Hx64 | exact Himg]|].
    apply (KEEPFR cid pos x Hfr); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- destruct b as [a k0]. destruct (HD a k0 HbD) as (Hin & Hab).
  exact (wv_blk_keep ly S Hp W mem md o buf cap Lam peak cnt fail ran a k0 x ly2 S2 Hp2 W2 mem2 md2
    STK0 (spZ regs + d) k HAR HLED Hin Hab Hb Hcap0 Hbuf
    ltac:(intros Ho; exact (Hoff x Ho (or_intror (ex_intro _ (a, k0) (conj HbD Hb))))) HJ).
Qed.

(* ---- a .rodata literal is a legal put source: its home is kept (kept_at's read-only arm, which does not read the
   ledger) and it is apart from the buffer, because the buffer is a client block and the literal is image ---- *)
Lemma wv_lit_home : forall {most own : Z} ly S Hp W mem md Lam peak cnt fail ran buf cap s n,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (cap <> 0 -> In (buf, cap) Lam) -> 0 <= cap -> 0 < n ->
  kept_at B [] s n ->
  (forall a, s <= a < s + n -> in_img SEGS a) ->
  prhWriter_src_home B ly S Lam buf cap s n.
Proof.
intros most own ly S Hp W mem md Lam peak cnt fail ran buf cap s n HAR HLED Hbuf Hcap0 Hn Hkept Himg.
pose proof cf_head_nonneg as Hh0.
split.
- left. destruct Hkept as [(b & m & Hin & _) | [H2 | H3]];
    [destruct Hin | right; left; exact H2 | right; right; exact H3].
- destruct (Z.eq_dec cap 0) as [->|Hc0]; [left; reflexivity|].
  destruct (Z_le_gt_dec (s + n) buf) as [Hle|Hgt]; [right; left; exact Hle|].
  destruct (Z_le_gt_dec (buf + cap) s) as [Hle2|Hgt2]; [right; right; exact Hle2|].
  exfalso.
  pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
  pose proof (HF (buf, cap) (Hbuf Hc0)) as (_ & Hblb & _). cbn [fst snd] in Hblb.
  assert (Hrq : cap + cf_head <= req_size (cap + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); lia).
  set (x := Z.max s buf).
  assert (Hx1 : s <= x < s + n) by (subst x; lia).
  assert (Hx2 : buf - cf_head <= x < buf - cf_head + req_size (cap + cf_head)) by (subst x; lia).
  refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR _) (Himg x Hx1)).
  left. exists (buf - cf_head), (cap + cf_head). split; [exact Hblb | exact Hx2].
Qed.

(* ---- WHAT write_value's OWN STEPS KEEP. Its straight-line code writes only its own frame [sp - 176, sp) (the one
   region of the seated state with a write window): the struct (at or above the entry sp), the buffer and every
   harness block, the ledger's statics, the image and the tree all lie outside it. Each keep below is stated over a
   write set P with the two side conditions the walk discharges once (P misses everything below alloc_ceiling, and
   P misses the struct), so the item loop reuses them after every call. ---- *)
Definition wv_wr (sp a : Z) : Prop := sp - 176 <= a < sp.

(* the powers this walk compares, as numerals (with the euclidean-division flag off, lia treats 2 ^ k as an atom) *)
Lemma wv_pow_facts : 2 ^ 47 < 2 ^ 64 /\ 2 ^ 31 < 2 ^ 47 /\ 0 < 2 ^ 44 /\ 2 ^ 32 < 2 ^ 47.
Proof. repeat split; vm_compute; congruence. Qed.

(* a run's frame (its regions' write windows inside P) keeps every byte outside P *)
Lemma wv_keep_frame : forall (H : word -> bool) E rs (m0 m1 m2 : word -> option byte) (P : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros H E rs m0 m1 m2 P K1 Hfr Hsub a Ha Hp. rewrite <- (K1 a Ha Hp).
apply (aview_eq_of SEGS). apply Hfr. rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hp (Hsub a Hw)).
Qed.

Lemma wv_vm_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a (w : nat) x,
  (forall j, (j < w)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a w x -> val_mem SEGS (mrestrict H' m') a w x.
Proof. intros H H' m m' a w x Hk Hv j Hj. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hk j Hj)). exact (Hv j Hj). Qed.

(* the shadow address of a byte below 2 ^ 47 is itself below alloc_ceiling *)
Lemma wv_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < YM05.alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _).
assert (P47 : 2 ^ 47 = 140737488355328) by (vm_compute; reflexivity). rewrite P47 in Hx.
assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (Hd : x / 8 < 17592186044416)
  by (apply Z.div_lt_upper_bound; [lia | change (8 * 17592186044416) with 140737488355328; lia]).
unfold SHADOW_OFF. set (q := x / 8) in *. clearbody q. lia.
Qed.

(* the whole shadow hull of a window below 2 ^ 47 likewise *)
Lemma wv_hull_low : forall a n s, 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 -> 0 <= s < YM05.alloc_ceiling.
Proof.
intros a n s Ha Hn Hpos Hs. pose proof asan_consts as (C1 & _). unfold shadow_addr in Hs.
assert (P47 : 2 ^ 47 = 140737488355328) by (vm_compute; reflexivity). rewrite P47 in Hn.
pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)).
assert (Hd0 : 0 <= a / 8) by (apply Z.div_pos; lia).
assert (Hd : (a + n - 1) / 8 < 17592186044416)
  by (apply Z.div_lt_upper_bound; [lia | change (8 * 17592186044416) with 140737488355328; lia]).
unfold SHADOW_OFF in *. lia.
Qed.

(* THE LEDGER: its seven statics are image bytes (generated addresses, all below kLowMemEnd) and each harness block's
   hidden head is in a block, so a write set that misses everything below alloc_ceiling keeps the ledger *)
Lemma wv_led_keep : forall {most own : Z} ly S Hp W md mem mem' Lam peak cnt fail ran (P : Z -> Prop),
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ P a) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros most own ly S Hp W md mem mem' Lam peak cnt fail ran P HAR LG HK HP.
pose proof LG as HND. apply prh_ledger_nodup in HND. pose proof LG as HHB. apply prh_ledger_blocks in HHB.
pose proof LG as HPm. apply prh_ledger_heads in HPm.
pose proof LG as G1. apply prh_ledger_live in G1. pose proof LG as G2. apply prh_ledger_peak in G2.
pose proof LG as G3. apply prh_ledger_count in G3. pose proof LG as G4. apply prh_ledger_fail in G4.
pose proof LG as G5. apply prh_ledger_ran in G5. pose proof LG as Gr. apply prh_ledger_bounds in Gr.
(* #102's two cells g_most / g_own_ran_out (the E sweep), by the named projections *)
pose proof LG as G6. apply prh_ledger_most in G6. pose proof LG as G7. apply prh_ledger_own in G7.
destruct G6 as (G6 & G6r). destruct G7 as (G7 & G7r).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Hh0.
(* the generated static addresses and widths, read off the image class *)
assert (HGA : (0 <= pi_g_live /\ pi_g_live + 8 <= kLowMemEnd) /\ (0 <= pi_g_peak /\ pi_g_peak + 8 <= kLowMemEnd) /\
              (0 <= pi_g_count /\ pi_g_count + 8 <= kLowMemEnd) /\ (0 <= pi_g_fail /\ pi_g_fail + 8 <= kLowMemEnd) /\
              (0 <= pi_g_ran_out /\ pi_g_ran_out + 8 <= kLowMemEnd) /\ (0 <= pi_g_most /\ pi_g_most + 8 <= kLowMemEnd) /\
              (0 <= pi_g_own_ran_out /\ pi_g_own_ran_out + 8 <= kLowMemEnd))
  by (repeat split; vm_compute; congruence).
assert (HGZ : (pi_gz_live <= 8)%nat /\ (pi_gz_peak <= 8)%nat /\ (pi_gz_count <= 8)%nat /\ (pi_gz_fail <= 8)%nat /\
              (pi_gz_ran_out <= 8)%nat /\ (pi_gz_most <= 8)%nat /\ (pi_gz_own_ran_out <= 8)%nat)
  by (repeat split; vm_compute; lia).
destruct HGA as ((A1a & A1b) & (A2a & A2b) & (A3a & A3b) & (A4a & A4b) & (A5a & A5b) & (A6a & A6b) & (A7a & A7b)).
destruct HGZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
split; [|split; [exact HND | split; [|exact HPm]]].
- split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G1); intros j Hj; apply HK; [lia | apply HP; lia]|].
  split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G2); intros j Hj; apply HK; [lia | apply HP; lia]|].
  split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G3); intros j Hj; apply HK; [lia | apply HP; lia]|].
  split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G4); intros j Hj; apply HK; [lia | apply HP; lia]|].
  split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G5); intros j Hj; apply HK; [lia | apply HP; lia]|].
  split; [split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G6); intros j Hj; apply HK; [lia | apply HP; lia] | exact G6r]|].
  split; [split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ G7); intros j Hj; apply HK; [lia | apply HP; lia] | exact G7r]|].
  exact Gr.
- rewrite Forall_forall in HHB |- *. intros [a k] Hin. destruct (HHB _ Hin) as (H1 & H2 & H3 & H4 & H5).
  cbn [fst snd] in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR H2) as (Hb16 & Hb4096 & Hbc & _).
  assert (Hrq : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  refine (wv_vm_keep _ _ _ _ _ _ _ _ H5). intros j Hj. apply HK; [lia | apply HP; lia].
Qed.

(* THE WRITER STRUCT and its buffer: the struct's 32 bytes at o and the buffer's bytes (a harness block) *)
Lemma wv_out_keep : forall {most own : Z} ly1 S1 Hp1 (W1 W2 : world SEGS) mem1 mem2 md1 Lam peak1 cnt1 fail1 ran1 o buf st
  (P : Z -> Prop),
  ARx ly1 S1 Hp1 W1 mem1 md1 ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam peak1 cnt1 fail1 ran1 most own ->
  prhWriter_out W1 mem1 Lam o buf st ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  (forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ P a) ->
  prhWriter_out W2 mem2 Lam o buf st.
Proof.
intros most own ly1 S1 Hp1 W1 W2 mem1 mem2 md1 Lam peak1 cnt1 fail1 ran1 o buf st P HAR HLEDx HO HK HP HOP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Hh0.
destruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10).
assert (HKo : forall a (w : nat), o <= a -> a + Z.of_nat w <= o + 32 ->
  forall j, (j < w)%nat -> aview SEGS (w_H W2) mem2 (a + Z.of_nat j) = aview SEGS (w_H W1) mem1 (a + Z.of_nat j)).
{ intros a w Hlo Hhi j Hj. destruct (HOP (a + Z.of_nat j) ltac:(lia)) as [R1 R2]. apply HK; assumption. }
split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ O4); apply (HKo o 8%nat); lia|].
split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ O5); apply (HKo (o + 8) 8%nat); lia|].
split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ O6); apply (HKo (o + 16) 8%nat); lia|].
split; [refine (wv_vm_keep _ _ _ _ _ _ _ _ O7); apply (HKo (o + 24) 4%nat); lia|].
split; [exact O8|]. split; [exact O9|].
destruct O10 as [Hz | (Hgrid & Hin & Hlen & (rest & Hr1 & Hr2) & Hsh)]; [left; exact Hz|].
pose proof HLEDx as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
destruct (HHB _ Hin) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
destruct (alx_blocks SEGS B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR Hab) as (_ & H4096 & Hc & _).
assert (Hrq : WriterApp.w_cap st + cf_head <= req_size (WriterApp.w_cap st + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); lia).
assert (HKb : forall a, buf <= a < buf + WriterApp.w_cap st ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) by (intros a Ha; apply HK; [lia | apply HP; lia]).
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [exact Hlen|]. split.
- exists rest. split; [exact Hr1|]. unfold PRH_Base.bytes_at, garr8 in Hr2 |- *. intros j Hj.
  destruct (Hr2 j Hj) as [Hv Hb]. split; [|exact Hb].
  refine (wv_vm_keep _ _ _ _ _ _ _ _ Hv). intros i Hi. apply HKb. cbn in Hj. lia.
- intros Hf0. destruct (Hsh Hf0) as [Hra0 Hhull]. split.
  + apply (range_addressable_agree (aview SEGS (w_H W1) mem1) (aview SEGS (w_H W2) mem2) SHADOW_OFF buf
      (WriterApp.w_cap st)); [|exact Hra0].
    intros x Hx. unfold shadow_of_addr. pose proof (wv_shadow_low x ltac:(lia)) as Hs. apply HK; [lia | apply HP; lia].
  + intros s Hs. destruct (wv_hull_low buf (WriterApp.w_cap st) s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as [Hs1 Hs2].
    rewrite (HK s ltac:(lia) (HP s ltac:(lia))). exact (Hhull s Hs).
Qed.

(* THE TREE'S BLOCKS stay C-visible, and v's shadow addressable, when every byte below alloc_ceiling is kept *)
Lemma wv_tree_vis_keep : forall (W W' : world SEGS) mem mem' D (P : Z -> Prop),
  prhWriter_tree_vis W mem D ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  prhWriter_tree_vis W' mem' D.
Proof.
intros W W' mem mem' D P HT HK HP a k Hin. destruct (HT a k Hin) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the kit's tree_vis_cf rounds the block up to its granule; with the euclidean-division flag off, lia needs the
   round-up inequality as a fact *)
assert (HG8 : a + k <= (a + k + 7) / 8 * 8).
{ pose proof (Z.div_mod (a + k + 7) 8 ltac:(lia)) as Dv. pose proof (Z.mod_pos_bound (a + k + 7) 8 ltac:(lia)) as Mv.
  lia. }
assert (HKa : forall y, 0 <= y < YM05.alloc_ceiling -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y)
  by (intros y Hy; apply HK; [lia | apply HP; lia]).
split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|]. split; [|split].
- apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') SHADOW_OFF a k); [|exact T5].
  intros x Hx. apply HKa. unfold shadow_of_addr. apply wv_shadow_low. lia.
- intros Hk0 s Hs. destruct (wv_hull_low a k s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as [Hs1 Hs2].
  rewrite (HKa s ltac:(lia)). exact (T6 Hk0 s Hs).
- intros x Hx. rewrite (HKa x) by lia. exact (T7 x Hx).
Qed.

Lemma wv_ra_keep : forall (W W' : world SEGS) mem mem' v n (P : Z -> Prop),
  0 <= v -> v + n <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  range_addressable (aview SEGS (w_H W') mem') SHADOW_OFF v n.
Proof.
intros W W' mem mem' v n P Hv0 Hv1 HR HK HP. pose proof asan_consts as (C1 & _).
apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') SHADOW_OFF v n); [|exact HR].
intros x Hx. unfold shadow_of_addr. pose proof (wv_shadow_low x ltac:(lia)) as Hs.
apply HK; [lia | apply HP; lia].
Qed.

(* the read-only view: image bytes, all below kLowMemEnd *)
Lemma wv_arodata_keep : forall (W W' : world SEGS) mem mem' (P : Z -> Prop),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros W W' mem mem' P HRO HK HP a Hro Ho He. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
pose proof (pa_segs_low a Himg) as Hl.
rewrite HK; [exact (HRO a Hro Ho He) | unfold kLowMemEnd in Hl; lia | apply HP; unfold kLowMemEnd in Hl; lia].
Qed.

(* ---- THE TAIL CALLS (put at write_value + 4 * 236, put_string at + 4 * 86): the epilogue has put sp and ra back, so
   the callee runs at write_value's OWN entry sp with its entry ra, and its post IS write_value's: aj_call_xWR at
   o = - d, e1 = d (the callee's window reaches the caller's window top, which holds the struct). ---- *)
(* ---- the only writable window of the seated state is the own frame [sp - 176, sp): a journal whose stack window
   covers it admits every write the straight-line code makes ---- *)
Lemma wv_awr : forall E tg STK sp0 FP bl0 blc ly own spe,
  bv_unsigned (ew E 2) = spe -> sp0 - STK <= spe - 176 -> spe <= sp0 ->
  awr_ok E (ss_mem (wv_ss2 tg)) STK sp0 FP bl0 blc ly own.
Proof.
intros E tg STK sp0 FP bl0 blc ly own spe Hsp H1 H2.
unfold wv_ss2, add_atom, wv_regions, wv_jt_region, stack_region, got_regionP, bcell_regionP.
cbn [ss_mem].
apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP bl0 blc ly own 2%nat (spe - sp0));
  [reflexivity | rewrite Hsp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn; lia|].
apply awr_ok_cons_ro; [cbn; lia|].
apply awr_ok_cons_ro; [cbn; lia|].
apply awr_ok_nil.
Qed.

(* ---- THE ONE USE of the kit's location premise (PRH_FnWriter.v twrite_value_specX): the node v is on the real stack
   between sp and ly_stk_hi, in a live harness block of the ledger, or in a live fake frame; in each case it is off
   the image, off the shadow band, 4096 or above, below 2 ^ 47, and apart from write_value's own 176-byte frame ---- *)
Lemma wv_loc : forall {most own : Z} ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v,
  176 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= spZ regs - 176 \/ spZ regs <= v) /\
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) /\ (forall a, v <= a < v + 56 -> ~ in_img SEGS a).
Proof.
intros most own ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v HSTK HPRE HLED HLOC.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
destruct HLOC as [(Hv1 & Hv2) | [(x & y & Hin & Hxb & Hxv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
- split; [lia|]. split; [lia|]. split; [right; exact Hv1|]. split; [right; unfold SHADOW_OFF; lia|].
  intros a Ha Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
- pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
  pose proof (HF (x, y) Hin) as (Hy0 & Hbl & _ & Hx16 & _). cbn [fst snd] in Hy0, Hbl, Hx16.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (x - cf_head) (y + cf_head) HAR Hbl)
    as (Hp16 & Hp4096 & Hpc & Hpapp & _ & _).
  assert (Hrq : y + cf_head <= req_size (y + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (y + cf_head) 0); lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [left; lia|].
  split; [unfold SHADOW_OFF; lia|].
  intros a Ha. refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HAR _)).
  left. exists (x - cf_head), (y + cf_head). split; [exact Hbl | lia].
- destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (_ & Hfapp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  split; [lia|]. split; [lia|]. split; [left; lia|].
  split; [unfold SHADOW_OFF; lia|].
  intros a Ha. refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HAR _)).
  right. left. exists cid, pos. split; [exact Hfr | lia].
Qed.

(* ---- THE TREE IS OFF write_value's OWN FRAME: every byte of the tree's footprint is a non-image byte either at or
   above the entry sp (the kit's stack arm) or below alloc_ceiling (a harness block, a fake frame), so the straight-line
   code cannot touch it ---- *)
Lemma wv_foot_wr : forall {most own : Z} ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v D,
  176 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ wv_wr (spZ regs) x.
Proof.
intros most own ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v D HSTK HPRE HLED HLOC HD x Hx.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Hh0.
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v HSTK HPRE HLED HLOC)
  as (Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
destruct Hx as [Hhdr | ([a k0] & HbD & Hb)].
- split; [lia|]. split; [exact (Hv5 x Hhdr)|]. unfold wv_wr. lia.
- unfold pj_holdsR in Hb. cbn [fst snd] in Hb.
  destruct (HD a k0 HbD) as (Hin & _).
  pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
  pose proof (HF (a, k0) Hin) as (Hk0 & Hbl & _). cbn [fst snd] in Hk0, Hbl.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k0 + cf_head) HAR Hbl)
    as (H16 & H4096 & Hpc & Happ & _ & _).
  assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  split; [lia|]. split.
  + refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR _)).
    left. exists (a - cf_head), (k0 + cf_head). split; [exact Hbl | lia].
  + unfold wv_wr. lia.
Qed.

(* a callee-saved register of the state at a stop, where the engine still shows its entry atom *)
Lemma wv_pres_of_st : forall (H : word -> bool) E ss ms (regs : bvmap 5 word),
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall r : Z, acallee_saved r -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
  (forall r : Z, acallee_saved r -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  aregs_preserved regs (ms_regs ms).
Proof.
intros H E ss ms regs HS Hsr HE r Hc.
rewrite (st_ok_pi_restrict_reg H E ss ms (Z_to_bv 5 r) HS), (Hsr r Hc).
cbn [sv_denot]. rewrite (HE r Hc), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

End h1.

(* ---- the .rodata literals write_value puts, by the ATOM AND ADDEND the generated listing carries at the slot that
   forms them (no typed address): the PAddHi at write_value + 4 * k ---- *)
Definition wv_addhi_atom (k : nat) : nat :=
  match nth (WV_SLOT + k) A_prog_listing (PW 0) with
  | PAddHi _ _ _ a _ => a
  | PLdHi _ _ _ a _ _ _ => a
  | _ => O
  end.
Definition WV_STR (k : nat) : Z := VAL (wv_addhi_atom k) + wv_addhi_off k.
(* the ten literals write_value puts, by the slot of the PAddHi that forms each (read out of A_prog_listing):
   null 122, false 126, true 103, the empty string 70, the empty number 114, "[" 39, "{" 42, ": " 59, ":" 130,
   "," 151, "]" 216, "}" 219 *)
Definition wv_lits : list (nat * list Z) :=
  [ (122%nat, [110; 117; 108; 108]); (126%nat, [102; 97; 108; 115; 101]); (103%nat, [116; 114; 117; 101]);
    (39%nat, [91]); (42%nat, [123]); (59%nat, [58; 32]); (130%nat, [58]); (151%nat, [44]);
    (216%nat, [93]); (219%nat, [125]) ].

(* ---- IMAGE FACTS OF THE INSTANCE (discharged at PI_prog_A), both read off the generated listing ----
   the tag switch's seven table words: each is a ROM word of the read-only band, apart from the GOT word and from
   the shadow-base cell, and inside the image's low range *)
Hypothesis HJT : forall k : nat, (k < 7)%nat ->
  val_mem SEGS (fun _ => None) (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) 4 (WV_JTW k) /\
  0 <= WV_JTW k <= 2 ^ 31 - 1 /\
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k /\
  VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= kLowMemEnd /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 0) \/
   VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 12) \/
   VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (forall i, 0 <= i < 4 -> in_img SEGS (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     in_roP SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     ~ Exists (in_zr (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i)) (as_owned_static B) /\
     ~ (as_errno B <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i < as_errno B + 4)).
(* and the literals: at any state of the run each is a legal put source whose home is kept (put_string's HLIT17
   shape), its bytes being the image's *)
Hypothesis HLIT : forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) wv_lits ->
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (WV_STR k) bs /\ kept_at B [] (WV_STR k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WV_STR k + i)).
(* IMAGE FACT (discharged at PI_prog_A by S1ImgA.pst_not_ro_A): no static of alloc.c lies in the read-only band, so
   a journal's image clause keeps the band (the same text as put_string's and pj_write's walks) *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).

Section h2. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).

(* ---- THE CONTAINER CASE, support: the facts every inner call site needs, carried along write_value's own run of
   puts from its entry ---- *)
Lemma wv_aview_range : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256.
Proof.
intros H m a v Hv. unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.

Lemma wv_rdword_nonneg : forall (H : word -> bool) (m : word -> option byte) a w,
  rdword (aview SEGS H m) a = Some w -> 0 <= w.
Proof.
intros H m a w Hw. unfold rdword in Hw.
destruct (aview SEGS H m a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (wv_aview_range _ _ _ _ E0). pose proof (wv_aview_range _ _ _ _ E1). pose proof (wv_aview_range _ _ _ _ E2).
pose proof (wv_aview_range _ _ _ _ E3). pose proof (wv_aview_range _ _ _ _ E4). pose proof (wv_aview_range _ _ _ _ E5).
pose proof (wv_aview_range _ _ _ _ E6). pose proof (wv_aview_range _ _ _ _ E7). lia.
Qed.

(* THE ONE-RECORD CHAIN (the kit's ruled case-1 form): from the two words below a frame pointer v at or above the
   ceiling, the lower one below the ceiling, a chain from v exists at any base 16 below v *)
Lemma wv_chain1 : forall ly rd sp v ra nfp,
  rdword rd (v - 8) = Some ra -> rdword rd (v - 16) = Some nfp -> 0 <= ra ->
  nfp < YM05.alloc_ceiling -> YM05.alloc_ceiling <= v -> v mod 8 = 0 -> sp + 16 <= v ->
  exists ch, achain ly rd sp v ch.
Proof.
intros ly rd sp v ra nfp H8 H16 Hra0 Hn Hv Hal Hsp.
destruct (Z_lt_le_dec v (ly_top ly - 16)) as [Ht|Ht].
2:{ exists []. left. split; [right; left; lia | reflexivity]. }
destruct (Z_lt_le_dec ra 4096) as [Hr|Hr].
- exists []. right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [|constructor].
  cbn [fpchain]. exists ra. split; [exact H8 | lia].
- exists [(v, ra, nfp)]. right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|].
    split; [lia|].
    assert (Hb : bad_next v (ly_top ly) nfp = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb. reflexivity.
  + constructor; [cbn; lia | constructor].
Qed.

(* the general form: any v (a v below the ceiling, at the top or misaligned gets the empty chain) *)
Lemma wv_chain1g : forall ly rd sp v ra nfp,
  rdword rd (v - 8) = Some ra -> rdword rd (v - 16) = Some nfp -> 0 <= ra ->
  nfp < YM05.alloc_ceiling -> sp + 16 <= v -> exists ch, achain ly rd sp v ch.
Proof.
intros ly rd sp v ra nfp H8 H16 Hra0 Hn Hsp.
destruct (Z_lt_le_dec v YM05.alloc_ceiling) as [Hv|Hv].
{ exists []. left. split; [left; exact Hv | reflexivity]. }
destruct (Z.eq_dec (v mod 8) 0) as [Hal|Hal].
- exact (wv_chain1 ly rd sp v ra nfp H8 H16 Hra0 Hn Hv Hal Hsp).
- exists []. left. split; [right; right; exact Hal | reflexivity].
Qed.

(* a reader change that keeps 8 bytes keeps the word they form *)
Lemma wv_rdword_ext : forall (rd rd' : Z -> option Z) a,
  (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H.
pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
pose proof (H 1 ltac:(lia)) as E1. pose proof (H 2 ltac:(lia)) as E2. pose proof (H 3 ltac:(lia)) as E3.
pose proof (H 4 ltac:(lia)) as E4. pose proof (H 5 ltac:(lia)) as E5. pose proof (H 6 ltac:(lia)) as E6.
pose proof (H 7 ltac:(lia)) as E7.
unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. reflexivity.
Qed.

(* The kit's case-1 words (form (a)) survive any change that keeps [o - 16, o) *)
Lemma wv_reca_keep : forall (rd rd' : Z -> option Z) o,
  (forall a, o - 16 <= a < o -> rd' a = rd a) ->
  (exists ra, rdword rd (o - 8) = Some ra /\
     exists nfp, rdword rd (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  exists ra, rdword rd' (o - 8) = Some ra /\
    exists nfp, rdword rd' (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling.
Proof.
intros rd rd' o H (ra & Hra & nfp & Hnfp & Hn).
exists ra. split; [rewrite (wv_rdword_ext rd rd') by (intros j Hj; apply H; lia); exact Hra|].
exists nfp. split; [rewrite (wv_rdword_ext rd rd') by (intros j Hj; apply H; lia); exact Hnfp | exact Hn].
Qed.

(* the caller footprint opens no sink *)
Lemma wv_cfp_closed : forall o buf cap, 0 < o -> (cap <> 0 -> 0 < buf - cf_head) ->
  ~ YI16.sink_open_fp (prhWriter_cfp o buf cap).
Proof.
intros o buf cap Ho Hb. apply sink_closed_pos. unfold prhWriter_cfp, prhWriter_fp.
constructor; [cbn; lia|]. destruct (Z.eqb_spec cap 0) as [_|Hc]; [constructor|].
unfold ablocks_fp. cbn [map]. constructor; [cbn; apply Hb; exact Hc | constructor].
Qed.

(* the read-only view through a journal (its image clause; HPSTRO) *)
Lemma wv_arodata_j : forall {R : world SEGS -> world SEGS -> Prop} STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2
    md2 k,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k HJ Hcl HRO a Hro Ho He.
pose proof (ajxR_img HJ) as F3.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
rewrite (F3 a Himg Ho He (HPSTRO a Hro) (fp_spares_closed FP a Hcl)). exact (HRO a Hro Ho He).
Qed.

(* ---- the writer's run: the room and the text bound for the next piece (the allocator-bytes identity across a run is
   S7a_WriterRet.prhWriter_blk_bb, the one copy) ---- *)

Lemma wv_capgrid_out : forall (W : world SEGS) mem Lam o buf st,
  prhWriter_out W mem Lam o buf st -> prhWriter_capgrid (WriterApp.w_cap st).
Proof.
intros W mem Lam o buf st (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc & _) | (Hg & _)]);
  [left; exact Hc | right; exact Hg].
Qed.

Lemma wv_wmax_next : forall ok st P1 P2 P3,
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (P1 ++ P2 ++ P3))) + 1 <= prhWriter_WMAX ->
  Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok st P1))) + Z.of_nat (length (concat P2)) + 1
    <= prhWriter_WMAX.
Proof.
intros ok st P1 P2 P3 H. pose proof (prhWriter_putN_len_le ok st P1) as L.
rewrite !concat_app, !length_app in H. lia.
Qed.

(* ---- THE LIVE ROOM AT EACH EVENT ACROSS A RUN OF PUTS (the batch kit's PRH_Base.prh_live_evs, which replaced the LIVE_<fn>
   entry sums in tput / tindent / tput_string / twrite_value). The live requests (PresetRoom.rs_live: the sizes of the
   allocator's blocks) are the writer buffer's request (wv_bl: none at capacity 0) plus a rest R that a run of puts
   does not touch; the run's all-granted events move the first exactly as prhWriter_blk's blocks arms move the blocks.
   So a callee's prh_live_evs at the join after the pieces P follows from the caller's over P ++ P2 ++ P3
   (wv_live_next), and its consumer window from the caller's (wv_cons_next, PRH_Base.prh_cons_from_sub). ---- *)
Definition wv_bl (st : WriterApp.wst) : list Z :=
  if WriterApp.w_cap st =? 0 then [] else [WriterApp.w_cap st + cf_head].

Lemma wv_zsum_perm : forall l l' : list Z, Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof. intros l l' H. induction H; cbn [fold_right]; lia. Qed.

Lemma wv_live_ablocks : forall ly S, map snd (ablocks B ly S) = PresetRoom.rs_live (YGcfRoom.room_of_cf S).
Proof. intros ly S. unfold ablocks, YGcfRoom.room_of_cf. cbn [PresetRoom.rs_live]. rewrite map_map. reflexivity. Qed.

(* the all-granted events of a run move the buffer's request as the run moves the capacity *)
Lemma wv_hlive_run : forall P st L R, Permutation L (wv_bl st ++ R) ->
  Permutation (PresetReqAt.hlive_from L (prhWriter_evs [] st P)) (wv_bl (prhWriter_putN [] st P) ++ R).
Proof.
induction P as [|b P IH]; intros st L R H; [exact H|].
cbn [prhWriter_evs prhWriter_putN hd tl].
destruct (prhWriter_grows st b) eqn:Hg.
- destruct (Z.eqb_spec (WriterApp.w_cnt st) (WriterApp.w_fail st)) as [Ec|Ec]; cbn [orb negb app].
  + (* the allocation set to fail: the writer fails, no event, the capacity kept *)
    assert (Hf : WriterApp.w_failed (prhWriter_put1 true st b) <> 0)
      by (unfold prhWriter_put1; rewrite Hg, (proj2 (Z.eqb_eq _ _) Ec); cbn; lia).
    assert (Hc : WriterApp.w_cap (prhWriter_put1 true st b) = WriterApp.w_cap st)
      by (unfold prhWriter_put1; rewrite Hg, (proj2 (Z.eqb_eq _ _) Ec); reflexivity).
    rewrite (prhWriter_evs_failed P [] _ Hf), (prhW_putN_failed P [] _ Hf), PresetReqAt.hlive_from_nil.
    unfold wv_bl in H |- *. rewrite Hc. exact H.
  + (* a granted grow: one event, the buffer's request replaced by the new capacity's *)
    rewrite PresetReqAt.hlive_from_cons. apply IH.
    assert (E1 : prhWriter_put1 true st b =
      WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b))
        ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
        (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)]))
      by (unfold prhWriter_put1; rewrite Hg, (proj2 (Z.eqb_neq _ _) Ec); reflexivity).
    rewrite E1. unfold wv_bl at 1. cbn [WriterApp.w_cap].
    rewrite (proj2 (Z.eqb_neq (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)) 0)
      (prhW_newcap_nz _ _)).
    unfold prhWriter_ev. unfold wv_bl in H.
    destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [E0|E0]; cbn [PresetReqAt.hstep app] in H |- *.
    * apply perm_skip. exact H.
    * apply perm_skip. apply PresetReqAt.rm1_perm_cons. exact H.
- destruct (prhW_nogrow_f st b Hg) as (_ & Hc & _).
  apply IH. unfold wv_bl in H |- *. rewrite Hc. exact H.
Qed.

(* the blocks arms of prhWriter_blk move the live requests the same way *)
Lemma wv_blk_live : forall ly S Lam peak buf st ly' S' Lam' peak' buf' st' R,
  0 <= WriterApp.w_cap st ->
  prhWriter_blk B ly S Lam peak buf st ly' S' Lam' peak' buf' st' ->
  Permutation (map snd (ablocks B ly S)) (wv_bl st ++ R) ->
  Permutation (map snd (ablocks B ly' S')) (wv_bl st' ++ R).
Proof.
intros ly S Lam peak buf st ly' S' Lam' peak' buf' st' R Hc0
  [(Hc & _ & _ & _ & HP) | (Hlt & l1 & l2 & b1 & b2 & Harm & _ & _ & HP)] H.
- unfold wv_bl in H |- *. rewrite Hc. exact (Permutation_trans (Permutation_map snd HP) H).
- apply (Permutation_trans (Permutation_map snd HP)). cbn [map snd].
  unfold wv_bl in H |- *. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st') 0)) by lia. cbn [app]. apply perm_skip.
  destruct Harm as [(Hz & _ & _ & -> & ->) | (Hnz & _ & Hb)].
  + rewrite Hz, Z.eqb_refl in H. cbn [app] in H |- *. exact H.
  + rewrite (proj2 (Z.eqb_neq _ 0) Hnz) in H. cbn [app] in H. rewrite Hb, map_app in H. cbn [map snd] in H.
    rewrite map_app. apply (PresetReqAt.perm_cons_cancel (WriterApp.w_cap st + cf_head)).
    exact (Permutation_trans (Permutation_middle (map snd b1) (map snd b2) _) H).
Qed.

(* the per-event room of a later stretch E2 of a list, at the state where the stretch starts *)
Lemma wv_live_sub : forall S S1 E1 E2 E3,
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S1))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E1) ->
  prh_live_evs S (E1 ++ E2 ++ E3) -> prh_live_evs S1 E2.
Proof.
intros S S1 E1 E2 E3 HP HL j e He.
assert (Hj : (j < length E2)%nat) by (apply nth_error_Some; rewrite He; discriminate).
assert (He' : nth_error (E1 ++ E2 ++ E3) (length E1 + j) = Some e).
{ rewrite nth_error_app2 by lia. replace (length E1 + j - length E1)%nat with j by lia.
  rewrite nth_error_app1 by exact Hj. exact He. }
specialize (HL _ _ He'). unfold prh_live_at in HL |- *.
rewrite firstn_app_2, firstn_app in HL.
replace (j - length E2)%nat with 0%nat in HL by lia. cbn [firstn] in HL. rewrite app_nil_r in HL.
rewrite PresetReqAt.hlive_from_app in HL.
rewrite (wv_zsum_perm _ _ (PresetReqAtNoMiss.hlive_from_perm (firstn j E2) _ _ HP)).
exact HL.
Qed.

(* THE LIVE ROOM AT A JOIN: a callee's prh_live_evs at the state after the pieces P (any outcomes ok) from the
   caller's over P ++ P2 ++ P3 and the blocks arms from the caller's entry *)
Lemma wv_live_next : forall ly S Lam peak buf st lyc Sc Lamc peakc bufc ok P P2 P3,
  0 <= WriterApp.w_cap st ->
  (WriterApp.w_cap st <> 0 -> In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S)) ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lamc peakc bufc (prhWriter_putN ok st P) ->
  prh_live_evs S (prhWriter_evs [] st (P ++ P2 ++ P3)) ->
  prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok st P) P2).
Proof.
intros ly S Lam peak buf st lyc Sc Lamc peakc bufc ok P P2 P3 Hc0 Hin HBLK HL.
destruct (prhW_putN_ok_or_failed P ok st) as [Est|Ef].
2: { rewrite (prhWriter_evs_failed P2 [] _ Ef). intros j e He. destruct j; discriminate He. }
rewrite Est in HBLK |- *.
assert (HR : exists R, Permutation (map snd (ablocks B ly S)) (wv_bl st ++ R)).
{ unfold wv_bl. destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [E0|E0].
  - exists (map snd (ablocks B ly S)). apply Permutation_refl.
  - exists (PresetReqAt.rm1 (WriterApp.w_cap st + cf_head) (map snd (ablocks B ly S))). cbn [app].
    apply PresetReqAt.rm1_in.
    change (WriterApp.w_cap st + cf_head) with (snd (buf - cf_head, WriterApp.w_cap st + cf_head)).
    apply in_map. exact (Hin E0). }
destruct HR as (R & HR).
pose proof (wv_hlive_run P st _ R HR) as H1.
pose proof (wv_blk_live _ _ _ _ _ _ _ _ _ _ _ _ R Hc0 HBLK HR) as H2.
rewrite !prhWriter_evs_app0 in HL.
refine (wv_live_sub S Sc _ _ _ _ HL).
rewrite <- (wv_live_ablocks lyc Sc), <- (wv_live_ablocks ly S).
exact (Permutation_trans H2 (Permutation_sym H1)).
Qed.

(* THE CONSUMER WINDOW AT A JOIN (the batch kit's PRH_Base.prh_cons_from at every writer text's entry): a callee's window at the
   exact advance after the pieces PP from the caller's over PP ++ P2 ++ P3 *)
Lemma wv_cons_next : forall rp_sm rp_x rp_os rp_i st PP P2 P3 ok,
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (PP ++ P2 ++ P3))) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st PP))%nat
    (length (prhWriter_evs [] (prhWriter_putN ok st PP) P2)).
Proof.
intros rp_sm rp_x rp_os rp_i st PP P2 P3 ok HC.
destruct (prhW_putN_ok_or_failed PP ok st) as [Est|Ef].
- assert (HL : length (prhWriter_evs ok st PP) = length (prhWriter_evs [] st PP)).
  { pose proof (prhW_evs_len PP ok st) as L1. pose proof (prhW_evs_len PP [] st) as L2.
    assert (Hk : prhWriter_k ok st PP = prhWriter_k [] st PP) by (unfold prhWriter_k; rewrite Est; reflexivity).
    rewrite Est in L1. lia. }
  rewrite HL, Est.
  rewrite !prhWriter_evs_app0, !length_app in HC.
  eapply PRH_Base.prh_cons_from_sub; [|exact HC]. lia.
- rewrite (prhWriter_evs_failed P2 [] (prhWriter_putN ok st PP) Ef). cbn [length].
  intros j e Hj. lia.
Qed.

(* ---- a grown buffer is a block the entry did not have (two copies of a nonempty block would break the allocator's
   pairwise disjointness) ---- *)
Lemma wv_two_in_split : forall (x : Z * Z) (l : list (Z * Z)),
  (2 <= count_occ wv_zz_dec l x)%nat -> exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
intros x l. induction l as [|a l IH]; cbn [count_occ]; [lia|].
destruct (wv_zz_dec a x) as [->|Hne]; intros Hc.
- assert (Hin : In x l) by (apply (count_occ_In wv_zz_dec); lia).
  apply in_split in Hin as (m1 & m2 & ->). exists [], m1, m2. reflexivity.
- destruct (IH Hc) as (l1 & l2 & l3 & ->). exists (a :: l1), l2, l3. reflexivity.
Qed.

Lemma wv_fresh_block : forall ly2 S2 Hp2 W2 mem2 md2 x l,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) (x :: l) -> 0 < req_size (snd x) -> ~ In x l.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 x l HAR Hperm Hrq Hin.
assert (Hx2 : In x (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (Hc : (2 <= count_occ wv_zz_dec (ablocks B ly2 S2) x)%nat).
{ rewrite (proj1 (Permutation_count_occ wv_zz_dec _ _) Hperm x).
  cbn [count_occ]. destruct (wv_zz_dec x x) as [_|Hne]; [|exfalso; exact (Hne eq_refl)].
  pose proof (proj1 (count_occ_In wv_zz_dec l x) Hin). lia. }
destruct (wv_two_in_split x _ Hc) as (m1 & m2 & m3 & Hsp).
destruct x as [p nn]. cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p nn HAR Hx2) as (_ & _ & _ & _ & _ & Hpw).
cbn [snd] in Hrq.
pose proof (pairwise_In2 zdisjoint _ (p, req_size nn) (p, req_size nn)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m1) (map (fun b : Z * Z => (fst b, req_size (snd b))) m2)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m3) Hpw) as Hd.
rewrite Hsp, !map_app in Hd. cbn [map] in Hd. rewrite ?map_app in Hd. cbn [map] in Hd. specialize (Hd eq_refl).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* along the writer's run a ledger block other than the entry buffer stays a ledger block other than the current
   buffer (the current ledger's keys are distinct) *)
Lemma wv_lam_keep : forall ly S Lam peak buf st lyc Sc Lam1 peak1 buf1 st1,
  NoDup (map fst Lam1) ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lam1 peak1 buf1 st1 ->
  forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1 /\ a <> buf1.
Proof.
intros ly S Lam peak buf st lyc Sc Lam1 peak1 buf1 st1 Hnd
  [(Ec & Eb & EL & Ep & Hp) | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hp)] a k Hin Hab.
- rewrite EL, Eb. split; assumption.
- assert (Hin' : In (a, k) (l1 ++ l2)).
  { destruct Hc as [(Z0 & E1 & E2 & _ & _) | (NZ & E & _)].
    - rewrite E1, E2. exact Hin.
    - rewrite E in Hin. apply in_app_or in Hin. destruct Hin as [H|[H|H]].
      + apply in_or_app. left. exact H.
      + injection H as E1 _. exfalso. exact (Hab (eq_sym E1)).
      + apply in_or_app. right. exact H. }
  rewrite EL in Hnd |- *. split; [right; exact Hin'|].
  intros Ea. subst a. cbn [map] in Hnd. inversion Hnd as [|? ? Hni _]. apply Hni.
  apply (in_map fst) in Hin'. cbn [fst] in Hin'.
  first [ exact Hin' | apply list_elem_of_In; exact Hin' | apply elem_of_list_In; exact Hin' ].
Qed.

(* the current buffer's footprint is the entry's or a block the run made: a callee's FP fits the caller's *)
Lemma wv_fp_sub : forall STKc sp0 ly S lyc Sc Hpc Wc memc mdc o Lam peak buf st Lam1 peak1 buf1 st1,
  ARx lyc Sc Hpc Wc memc mdc -> 0 <= WriterApp.w_cap st ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lam1 peak1 buf1 st1 ->
  fp_sub_xW B STKc sp0 (prhWriter_cfp o buf (WriterApp.w_cap st)) (prhWriter_cfp o buf1 (WriterApp.w_cap st1))
    ly S [] lyc Sc.
Proof.
intros STKc sp0 ly S lyc Sc Hpc Wc memc mdc o Lam peak buf st Lam1 peak1 buf1 st1 HAR Hc0 Hblk a Ha.
unfold prhWriter_cfp in Ha. apply inFP_cons in Ha. destruct Ha as [Hs | Hb].
- left. unfold prhWriter_cfp. apply inFP_cons. left. exact Hs.
- destruct Hblk as [(Ec & Eb & _ & _ & _) | (Lt & l1 & l2 & b1 & b2 & Hc & _ & _ & Hp)].
  + left. unfold prhWriter_cfp. apply inFP_cons. right. rewrite <- Ec, <- Eb. exact Hb.
  + right. left. unfold prhWriter_fp in Hb.
    rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0)) in Hb by lia.
    unfold ablocks_fp in Hb. cbn [map] in Hb.
    destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
    exists (buf1 - cf_head), (WriterApp.w_cap st1 + cf_head). split; [|split; [|lia]].
    * eapply Permutation_in; [apply Permutation_sym; exact Hp | left; reflexivity].
    * assert (Hrq : 0 < req_size (snd (buf1 - cf_head, WriterApp.w_cap st1 + cf_head))).
      { cbn [snd]. pose proof cf_head_nonneg as Hh0. unfold req_size.
        destruct (Z.eqb_spec (WriterApp.w_cap st1 + cf_head) 0); lia. }
      pose proof (wv_fresh_block lyc Sc Hpc Wc memc mdc _ _ HAR Hp Hrq) as Hfr.
      destruct Hc as [(Z0 & E1 & E2 & E3 & E4) | (NZ & EL & EA)].
      -- rewrite <- E4. intros Hin. apply Hfr. rewrite E3. exact Hin.
      -- rewrite EA. intros Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
         ++ apply Hfr. apply in_or_app. left. exact Hin.
         ++ injection Hin as _ E. lia.
         ++ apply Hfr. apply in_or_app. right. exact Hin.
Qed.

(* ---- THE TREE ALONG THE RUN: v's shadow and the tree's blocks at any state the caller journal reaches from the
   entry (the harness-block shadow law at the current state, the stack-shadow law, a frame's shadow kept by the
   journal, a block's bytes kept by the journal and its tail granule by AR_laws_x field 15) ---- *)
Lemma wv_block_shadow_range : forall rd p n, block_shadow rd SHADOW_OFF p n -> range_addressable rd SHADOW_OFF p n.
Proof.
intros rd p n (Hp8 & Hn & Hc) x Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as Dn7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as Mn7.
assert (Hi : shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF p + (x / 8 - p / 8)).
{ unfold shadow_of_addr. ring. }
assert (Hb : 0 <= x / 8 - p / 8 < (n + 7) / 8) by lia.
rewrite Hi. exists (if (x / 8 - p / 8) <? n / 8 then 0 else n mod 8). split; [exact (Hc _ Hb)|].
destruct (Z.ltb_spec (x / 8 - p / 8) (n / 8)) as [Hlt | Hge]; [left; reflexivity|].
destruct (Z.eq_dec (n mod 8) 0) as [E0 | En0]; [left; exact E0|]. right. lia.
Qed.

Lemma wv_hblock_shadow : forall ly S Hp W mem md a k,
  ARx ly S Hp W mem md -> prh_hblock (PA := PA) B ly S Hp W mem a k -> 0 < k ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a k /\ shadow_hull_vis (aview SEGS (w_H W) mem) a k.
Proof.
intros ly S Hp W mem md a k HAR (Hk & Hin & HinH & _ & _) Hk0.
pose proof (@cf_head_nonneg cp) as Hch.
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hin HinH) as [Hbs Hhull].
unfold req_size in *. destruct (Z.eqb_spec (k + cf_head) 0) as [E0 | _]; [lia|].
replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia. replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact (wv_block_shadow_range _ _ _ Hbs) | apply Hhull; lia].
Qed.

Lemma wv_ra_sub : forall rd x n x' n', range_addressable rd SHADOW_OFF x n -> x <= x' -> x' + n' <= x + n ->
  range_addressable rd SHADOW_OFF x' n'.
Proof. intros rd x n x' n' H H1 H2 y Hy. apply H. lia. Qed.

Lemma wv_fs_mod8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes in *.
destruct (Z_le_gt_dec 0 cid) as [Hc|Hc].
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z_mod_mult.
- exfalso. rewrite Z.shiftl_div_pow2 in H by lia.
  assert (H2 : 2 <= 2 ^ (- cid)).
  { change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia. }
  assert (H3 : 64 / 2 ^ (- cid) <= 32) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* v's 56 bytes stay addressable: the kit's three locations *)
Lemma wv_ra_cur : forall {most own : Z} {R : world SEGS -> world SEGS -> Prop} ly S Hp W mem md Lam buf v regs STKv d o
    cap
    lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1,
  ARx ly S Hp W mem md -> astk_ok STKv ly (spZ regs) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R (STKv + d) (spZ regs + d) (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 fail1 ran1 most own ->
  (forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1) ->
  YM05.alloc_ceiling <= o ->
  (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56.
Proof.
intros most own R ly S Hp W mem md Lam buf v regs STKv d o cap lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1
  HAR Hstk HRA HLOC HJ HLED1 HLK Ho Hbufb.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof cf_head_nonneg as Hh0.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frm HJ) as F4.
destruct HLOC as [(Hv1 & Hv2) | [(x & y & Hin & Hxb & Hxv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
- (* the real stack: its shadow is zero in every ARx state *)
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  intros z Hz. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. apply (alx_zshadow_byte SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc z HARc). lia.
- (* a harness block of the ledger, still one at the current state *)
  pose proof (HLK x y Hin Hxb) as Hin1.
  pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED1) as HF1.
  destruct (wv_hblock_shadow lyc Sc Hpc Wc memc mdc x y HARc (HF1 _ Hin1) ltac:(lia)) as [Hr _].
  exact (wv_ra_sub _ x y v 56 Hr Hxv Hvy).
- (* a live fake frame of the entry: the journal keeps its shadow bytes *)
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (Hf32 & Hfapp & _).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (Hf4096 & Hfc & _).
  set (fa := frame_addr ly cid pos) in *. set (fs := fs_frame_bytes cid) in *.
  assert (Hfs8 : fs mod 8 = 0) by (apply wv_fs_mod8; lia).
  intros z Hz. destruct (HRA z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. apply (F4 cid pos); [exact Hfr | right; unfold in_zr, shadow_of_addr, shadow_addr | ].
  + pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa. pose proof (Z.div_mod z 8 ltac:(lia)) as Dz.
    pose proof (Z.div_mod fs 8 ltac:(lia)) as Dfs.
    pose proof (Z.mod_pos_bound z 8 ltac:(lia)). pose proof (Z.mod_pos_bound fa 8 ltac:(lia)).
    assert (Hfa8 : fa mod 8 = 0).
    { pose proof Hf32 as Hq. apply Z.mod_divide in Hq; [|lia]. destruct Hq as [q Hq]. rewrite Hq.
      replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
    subst fa fs. cbn [fst snd] in *. lia.
  + intros Hf. unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. unfold shadow_of_addr in Hf.
    destruct Hf as [Hs1 | Hb].
    * assert (Hzd : z / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; unfold in_app, kLowShadowBeg,
        kHighMemBeg, ASAN_CEIL in Hfapp; change (8 * 2 ^ 44) with (2 ^ 47); lia).
      unfold SHADOW_OFF in *. lia.
    * unfold prhWriter_fp in Hb. destruct (Z.eqb_spec cap 0) as [_|Hc]; [exact (inFP_nil _ Hb)|].
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR (Hbufb Hc)) as (_ & _ & _ & Happ & _).
      destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
      assert (Hzd : z / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; unfold in_app, kLowShadowBeg,
        kHighMemBeg, ASAN_CEIL in Hfapp; change (8 * 2 ^ 44) with (2 ^ 47); lia).
      assert (Hz0 : 0 <= z / 8) by (apply Z.div_pos; lia).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the tree's blocks stay C-visible: their shadow by the harness-block law at the current state, their bytes by the
   journal (a live block outside FP), their tail granule by field 15 *)
Lemma wv_tvis_cur : forall {most own : Z} {R : world SEGS -> world SEGS -> Prop} ly S Hp W mem md Lam buf D STK sp0 o
    cap lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1,
  ARx ly S Hp W mem md -> prhWriter_tree_vis W mem D ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK sp0 (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 fail1 ran1 most own ->
  (forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1) ->
  YM05.alloc_ceiling <= o ->
  (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  prhWriter_tree_vis Wc memc D.
Proof.
intros most own R ly S Hp W mem md Lam buf D STK sp0 o cap lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1
  HAR HT HD HLB HJ HLED1 HLK Ho Hbufb a k HinD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof cf_head_nonneg as Hh0.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_blk HJ) as F2.
destruct (HD a k HinD) as (HinL & Hab).
destruct (HT a k HinD) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (HLK a k HinL Hab) as Hin1.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED1) as HF1.
pose proof (HF1 _ Hin1) as Hhb1. cbn [fst snd] in Hhb1. pose proof Hhb1 as (_ & Hbl1 & _).
pose proof (HLB a k HinL) as Hbl0.
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbl0) as (_ & _ & Hce0 & _ & _ & Hpw0).
assert (Hvis : forall z, a <= z < (a + k + 7) / 8 * 8 -> aview SEGS (w_H Wc) memc z <> None).
{ intros z Hz.
  destruct (Z_lt_le_dec z (a - cf_head + req_size (k + cf_head))) as [Hl2|Hl2].
  - assert (E : aview SEGS (w_H Wc) memc z = aview SEGS (w_H W) mem z).
    { replace z with (a - cf_head + (z - (a - cf_head))) by lia.
      apply (F2 _ _ _ Hbl0 Hbl1); [lia|].
      intros Hf. unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hs | Hb]; [lia|].
      unfold prhWriter_fp in Hb. destruct (Z.eqb_spec cap 0) as [_|Hc]; [exact (inFP_nil _ Hb)|].
      unfold ablocks_fp in Hb. cbn [map] in Hb.
      destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
      destruct (wv_pairwise_in2 zdisjoint _ (a - cf_head, req_size (k + cf_head))
          (buf - cf_head, req_size (cap + cf_head)) Hpw0
          (in_map (fun b => (fst b, req_size (snd b))) _ _ Hbl0)
          (in_map (fun b => (fst b, req_size (snd b))) _ _ (Hbufb Hc))
          ltac:(intros Eq; injection Eq as Eq1 _; lia)) as [Hd|Hd];
        unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia. }
    rewrite E. exact (T7 z Hz).
  - apply (alx_blocks_tail SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ z HARc Hbl1).
    assert (Hm : (a + k + 7) / 8 <= (a - cf_head + req_size (k + cf_head) + 7) / 8) by (apply Z.div_le_mono; lia).
    set (q1 := (a + k + 7) / 8) in *. set (q2 := (a - cf_head + req_size (k + cf_head) + 7) / 8) in *.
    clearbody q1 q2.
    split; [exact Hl2 | lia]. }
split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
destruct (Z_le_gt_dec k 0) as [Hk0 | Hk0].
- split; [intros z Hz; lia|]. split; [intros Hk; lia | exact Hvis].
- destruct (wv_hblock_shadow lyc Sc Hpc Wc memc mdc a k HARc Hhb1 ltac:(lia)) as [Hr Hh].
  split; [exact Hr|]. split; [intros _; exact Hh | exact Hvis].
Qed.

(* ---- THE MODEL-RUN POSITION (PRH_FnWriter d89d3c67b78c / PRH_Base ef7c8ca98529 at the cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record)). Every
   writer text takes its run events as an ENTRY premise (prh_run_at over prhWriter_evs [] st P) and posts the EXACT
   advance rp_i + length (prhWriter_evs ok st P); put posts it per arm (S7a_WriterRet's prhWriter_put_pos). The three
   lemmas below are the ONE place this walk composes positions: the first put's event from an entry list
   (wv_ev_first, S7a's prhWriter_ev_at with nothing put yet), the first put's exact advance (wv_ret_pos_one, S7a's
   prhWriter_ret_pos_step from the empty run), and a multi-put callee's post after an opened run (wv_ret_pos_app:
   the event count adds up, S7a's prhW_evs_len). ---- *)
Lemma wv_ev_first : forall rp_sm rp_x rp_os rp_i st bs R,
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (bs :: R)) ->
  prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
  nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs).
Proof.
intros rp_sm rp_x rp_os rp_i st bs R HE Hg Hc. rewrite <- (Nat.add_0_r rp_i).
exact (prhWriter_ev_at rp_sm rp_x rp_os rp_i _ st [] bs R [] HE eq_refl Hg Hc).
Qed.

Lemma wv_ret_pos_one : forall {most own : Z} rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Hp (W : world SEGS) mem Lam peak ran o buf st bs
    ly2 S2 Hp2 W2 regs2 mem2 md2,
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_i rp_hist st bs o W2 mem2 S2 ->
  prhWriter_retg B ly S Lam peak ran most own o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
intros most own rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Hp W mem Lam peak ran o buf st bs ly2 S2 Hp2 W2 regs2 mem2 md2
  HOUT HLED HPP HRET.
assert (HcntW : 0 <= WriterApp.w_cnt st)
  by (pose proof HLED as Hbd; apply prh_ledger_bounds in Hbd; destruct Hbd as (_ & _ & Hc & _); lia).
assert (HOK0 : prh_oks [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st []) (prhWriter_reqs [] st [])
  most ran ran).
{ rewrite prhW_k_nil. unfold prh_oks. split; [intros i Hi; exfalso; lia|].
  split; [left; reflexivity|]. intros i Hi; exfalso; lia. }
assert (G0 : prh_granted [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st []))
  by (rewrite prhW_k_nil; intros i Hi; exfalso; lia).
assert (HBLK0 : prhWriter_blk B ly S Lam peak buf st ly S Lam peak buf (prhWriter_putN [] st [])).
{ unfold prhWriter_blk. left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. apply Permutation_refl. }
exact (prhWriter_ret_pos_step B rp_sm rp_x rp_os rp_H0 rp_i rp_i rp_hist ly S Lam peak ran most own o buf st [] bs
  [] ran buf Lam peak ly S Hp W mem ly2 S2 Hp2 W2 regs2 mem2 md2 HcntW (eq_sym (Nat.add_0_r rp_i))
  HOK0 G0 HOUT HLED HBLK0 HPP HRET).
Qed.

Lemma wv_ret_pos_app : forall {most own : Z} rp_sm rp_x rp_os rp_H0 rp_i rp_c ly S Lam peak ran o buf st PP P2
    ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 (W1 : world SEGS) mem1 ly2 S2 Hp2 W2 regs2 mem2 md2,
  0 <= WriterApp.w_cnt st ->
  rp_c = (rp_i + length (prhWriter_evs ok1 st PP))%nat ->
  prh_oks ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st PP) (prhWriter_reqs ok1 st PP)
    most ran ran1 ->
  prh_granted ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st PP) ->
  prhWriter_out W1 mem1 Lam1 o buf1 (prhWriter_putN ok1 st PP) ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st PP))
    (WriterApp.w_fail (prhWriter_putN ok1 st PP)) ran1 most own ->
  prhWriter_blk B ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 (prhWriter_putN ok1 st PP) ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_c ly1 S1 Lam1 peak1 ran1 most own o buf1 (prhWriter_putN ok1 st PP) P2
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st (PP ++ P2) ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
intros most own rp_sm rp_x rp_os rp_H0 rp_i rp_c ly S Lam peak ran o buf st PP P2 ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1
  ly2 S2 Hp2 W2 regs2 mem2 md2 Hc0 Hrc Hok1 G1 Hout1 Hled1 Hblk1 (ok2 & Hret2 & G2 & hist2 & Hpos2).
destruct (prhWriter_blk_of_ret_ok B ok2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hret2 G2)
  as (ran2 & buf2 & Lam2 & peak2 & Hok2 & Hout2 & Hled2 & Hblk2).
pose proof Hled1 as Hb1. apply prh_ledger_bounds in Hb1. destruct Hb1 as (_ & _ & Hr1 & Hf1 & _).
pose proof Hled1 as Hnd1. apply prh_ledger_nodup in Hnd1.
destruct (prhW_app_model st PP P2 ok1 ok2 most ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2) as (ok & Hput & Hoks & HGr).
pose proof (prhW_cap_after PP ok1 st) as Hcap.
exists ok. split; [|split; [exact (HGr G1 G2)|]].
{ apply (prhWriter_ret_ok_of_blk B ok ly S Lam peak ran most own o buf st (PP ++ P2) ly2 S2 Hp2 W2 regs2 mem2 md2
    ran2 buf2 Lam2 peak2);
    [exact Hoks | rewrite Hput; exact Hout2 | rewrite Hput; exact Hled2 | rewrite Hput | exact (HGr G1 G2)].
  eapply prhW_blk_trans; [exact Hnd1 | exact Hcap | exact Hblk1 | exact Hblk2]. }
exists hist2.
replace (rp_i + length (prhWriter_evs ok st (PP ++ P2)))%nat
  with (rp_c + length (prhWriter_evs ok2 (prhWriter_putN ok1 st PP) P2))%nat; [exact Hpos2|].
subst rp_c.
pose proof (prhW_evs_len (PP ++ P2) ok st) as LW.
pose proof (prhW_evs_len PP ok1 st) as L1.
pose proof (prhW_evs_len P2 ok2 (prhWriter_putN ok1 st PP)) as L2.
unfold prhWriter_k in LW, L1, L2. rewrite Hput in LW.
pose proof (prhW_calls_le PP ok1 st) as M1.
pose proof (prhW_calls_le P2 ok2 (prhWriter_putN ok1 st PP)) as M2.
destruct (Z.eq_dec (WriterApp.w_failed st) 0) as [F0|F0].
- destruct (Z.eq_dec (WriterApp.w_failed (prhWriter_putN ok1 st PP)) 0) as [F1|F1].
  + rewrite (proj2 (Z.eqb_eq _ _) F0) in LW, L1. rewrite (proj2 (Z.eqb_eq _ _) F1) in L1, L2.
    cbn [andb negb] in LW, L1, L2.
    revert LW L2. destruct (WriterApp.w_failed (prhWriter_putN ok2 (prhWriter_putN ok1 st PP) P2) =? 0);
      cbn [negb]; intros LW L2; lia.
  + rewrite (prhWriter_evs_failed P2 ok2 (prhWriter_putN ok1 st PP) F1). cbn [length].
    rewrite (prhW_putN_failed P2 ok2 (prhWriter_putN ok1 st PP) F1) in LW.
    rewrite (proj2 (Z.eqb_eq _ _) F0) in LW, L1. rewrite (proj2 (Z.eqb_neq _ _) F1) in LW, L1.
    cbn [andb negb] in LW, L1. lia.
- rewrite (prhWriter_evs_failed (PP ++ P2) ok st F0), (prhWriter_evs_failed PP ok1 st F0),
    (prhW_putN_failed PP ok1 st F0), (prhWriter_evs_failed P2 ok2 st F0).
  cbn [length]. lia.
Qed.
End h2.

Section cl.
Variable CTX0 : list (list Z).
(* the callee texts, each QUANTIFIED OVER THE FLOAT STATE (the internal file REFIT-WRITER.md, the float-threading design, point 4):
   a call made after a float-changing call (put_string, the self call) runs at that call's fx'.
   THE RUN HAS AT MOST 4 CALLS: each callee text, and write_value's own, takes `(length rp_os <= 4)%nat`. write_value
   makes no allocator call of its own (its fuzz_realloc calls are put's), and every call it makes passes its entry
   rp_os unchanged, so each lemma below takes the bound once at entry and passes it to the callee. The bound is
   used at put's fuzz_realloc call, for its hull at the run position (lib/A/PresetHullPay.v hull_budget_of_room_pos;
   the entry headroom at a realloc event, lib/A/PresetDrvHeadroomA.v drv_cf_headroom_at_call_A, takes the same bound). *)
Hypothesis PUT : forall fx0 : YK11.FPState, tput_specX (fx := fx0) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* the put_string tail (A 0x86de4, write_value + 4 * 86: the string leaf), the same shape at tput_string_specX *)
Hypothesis PUTSTR : forall fx0 : YK11.FPState,
  tput_string_specX (fx := fx0) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* ---- THE INNER CALLS (the loop's put / indent / put_string and the recursive write_value): the callee runs at
   write_value's own frame base sp - 176, so oc = - (d + 176) and its window e1 = - oc reaches the caller's window top
   (which holds the struct). The conclusion is the engine's after-call shape; the walk goes on from the return site.
   ONE lemma per callee, so a new premise of a callee's text threads through in one place. ---- *)
Hypothesis INDENT : forall fx0 : YK11.FPState, tindent_specX (fx := fx0) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, as PRW_put_string_a.v / _base.v take it;
   discharged at the instance by a8's preset_head_wide). It gives a high-memory user pointer at least
   kHighMemBeg + 16, which YGcfStr.amem_range8 asks (cstr_ok, the strlen rule). *)
Hypothesis HW : prh_head_wide.
(* callee text: the strlen wrapper at its entry (YGcallMxmn.v blob 8d37ad16ea59, family 1b: astrlen_realizes_xrom,
   the read-only premise arodata_okP and the YAk memnorm keep); its ONE use is the call rule aj_strlen_at_xrom in
   wv_leaf_num *)
Hypothesis STRLEN : forall fx0 : YK11.FPState,
  YGcallMxmn.astrlen_realizes_xrom (fx := fx0) SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).

(* the keep of one run: the run's start state has ONE write window, the own frame [sp - 176, sp) at atom 2 (every
   other region's window is empty), so a run that starts from a memory kept outside P keeps every byte outside P *)
Ltac wv_keep_run HFr0 K0 K1 m0 P Usp :=
  lazymatch type of HFr0 with
  | frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m0 a);
    [ refine (wv_keep_frame H E rs m0 m1 m2 P K0 HFr0 _);
      let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros a (r & Hr & Ha);
      lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end;
      repeat (destruct Hr as [<- | Hr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; unfold wv_wr; lia |]);
      destruct Hr
    | ]
  end.

(* the write premise of a run from a state whose only window is the own frame, the journal at sp0 = spZ regs + d *)
Ltac wv_awr_tac Usp d :=
  cbn [ss_mem]; repeat first
    [ apply awr_ok_nil
    | eapply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- d));
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?Usp; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].

(* the write set of the number leaf: the own frame and the strlen call's 2 * ESTACK window below it *)
Definition wv_wrS (sp a : Z) : Prop := sp - 176 - STK_RT_STR <= a < sp.

(* wv_keep_run over wv_wrS *)
Ltac wv_keep_runS HFr0 K0 K1 m0 P Usp :=
  lazymatch type of HFr0 with
  | frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m0 a);
    [ refine (wv_keep_frame H E rs m0 m1 m2 P K0 HFr0 _);
      let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros a (r & Hr & Ha);
      lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end;
      repeat (destruct Hr as [<- | Hr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; unfold wv_wrS; lia |]);
      destruct Hr
    | ]
  end.

Section c1. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).

Lemma wv_neg_mod16 : forall d, d mod 16 = 0 -> (- d) mod 16 = 0.
Proof.
intros d H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
apply Z.mod_divide; [lia|]. exists (- q). lia.
Qed.

Lemma wv_tail_put : forall {most own : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  176 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, spZ regs <= a < spZ regs + d -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> spZ regsc = spZ regs -> getr regsc 1 = getr regs 1 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st [bs]) ->
  src_rd W memc s bs ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fpostWmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W
       mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st [bs]))%nat rp_H0 hist' S')).
Proof.
intros most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEPW
  HAP Hspc Hrac Hgpc Htpc Hchc Hroc H10 H11 H12 Hcut Hch0 HOUTc HLEDc Hev Hsrc Hhome Hwmax Hhead Hcons Hlive HMN.
pose proof HPRE as (HPREx & Hro & Htop).
pose proof HPREx as (HARe & Hret & Hra4 & _ & _ & Hstk & _).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
eapply SRr'_mono.
- eapply (@YCbqGcallW.aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    W regsc memc (SIGMA AS_put)
    (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp mdc 0
    STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st)) (- d) (getr regs 1) ch
    (fun ly' S' Hp' W' regs' mem' md' =>
       tputP_Q B rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem'))
       (wv_jlift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ));
    [lia | apply wv_neg_mod16; exact Hd16 | lia | vm_compute; congruence | lia | lia | exact Hd16 | lia
    | exact Hgpc | exact Htpc | exact Hrac | exact Hret | unfold raZ in Hra4; exact Hra4
    | replace (spZ regs + d + - d) with (spZ regs) by lia; exact Hchc | | ].
  + intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + d) by lia.
    assert (Hfpre : fpre B ARx STK_put ly S Hp W regsc memc mdc ch).
    { split; [exact Hpre|]. split; [exact Hroc|].
      split; [rewrite Hspc; exact (proj1 Htop) | split; [unfold raZ; rewrite Hrac; exact (proj1 (proj2 Htop)) | exact (proj2 (proj2 Htop))]]. }
    exact (PUT fx rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regsc memc mdc ch o s (Z.of_nat (length bs)) d buf st
      bs Lam peak ran Hfpre Hroom Hrp Hos4 Hcons Hcl H10 H11 H12
      ltac:(rewrite Hspc; exact Hcut) ltac:(rewrite Hspc; exact Hch0) Hwin Ho1' Ho2'
      HOUTc HLEDc Hsrc eq_refl Hhome (wv_ev_first rp_sm rp_x rp_os rp_i st bs [] Hev) Hwmax Hhead Hlive).
  + intros a Ha. left. exact Ha.
- cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HXT & HP2 & HQ).
  exists ly2, S2, Hp2, regs2, mem2, md2, (0 + k1)%Z.
  split; [exact Hc2|].
  split; [exact HJ2|].
  split.
  { intros a Ha Hf. rewrite (HXT a ltac:(lia) Hf). exact (HKEEPW a Ha). }
  split; [exact (aregs_preserved_trans regs regsc regs2 HAP HP2)|].
  destruct HQ as (HQq & HQM).
  apply tputP_R_of in HQq. destruct HQq as (okp & HR).
  split; [|intros Hmn; exact (HQM (HMN Hmn))].
  split; [exact (tputP_room HR)|].
  split; [|exact (wv_ret_pos_one rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Hp W memc Lam peak ran o buf st bs
             ly2 S2 Hp2 W2 regs2 mem2 md2 HOUTc HLEDc (conj (tputP_pos_keep HR) (tputP_pos_grow HR))
             (ex_intro _ okp (conj (tputP_ret_ok HR) (tputP_granted HR))))].
  assert (HJc' : ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
      (STK_put + d) (spZ regs + d)
      (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
  { replace (spZ regs + d) with (spZ regs + d + - d + d) by lia. exact HJc. }
  apply (wv_nodeR_keep W W2 memc mem2 Lam v t D HNODE).
  + intros x Hx. exact (proj1 (wv_foot_keep ly S Hp W regs memc mdc STKv (STK_put + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (ajx_ar HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
  + intros x Hx. exact (proj2 (wv_foot_keep ly S Hp W regs memc mdc STKv (STK_put + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (ajx_ar HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
Qed.

(* ---- FROM THE STATE AT THE TAIL put TO THE KIT'S WHOLE POST: between the entry and the tail call write_value writes
   only its own frame, so the writer struct, the ledger, the read-only view, the caller's chain and the tree are
   still the entry's at the call; what the leaf must supply is the source word (a literal, or a number's text) ---- *)
Lemma wv_put_close : forall {most own : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  184 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> getr regsc 1 = getr regs 1 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st [bs]) ->
  src_rd W memc s bs ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fpostWmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W
       mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st [bs]))%nat rp_H0 hist' S')).
Proof.
intros most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEP
  HAP Hrac H10 H11 H12 Hcut Hch0 Hev Hsrc Hhome Hwmax Hhead Hcons Hlive HMN.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ wv_wr (spZ regs) a)
  by (intros a Ha; unfold wv_wr; lia).
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a)
  by (intros a Ha; unfold wv_wr; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ wv_wr (spZ regs) a)
  by (intros a Ha; split; [lia | unfold wv_wr; lia]).
(* the callee-saved registers of the state at the call *)
assert (Hsp : spZ regsc = spZ regs)
  by (unfold spZ; f_equal; exact (HAP 2 ltac:(unfold acallee_saved; lia))).
assert (Hgpc : getr regsc 3 = w64 (as_gp B))
  by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regsc 4 = w64 (as_tp B))
  by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hs0c : s0Z regsc = s0Z regs)
  by (unfold s0Z; f_equal; exact (HAP 8 ltac:(unfold acallee_saved; lia))).
(* the tree, the struct, the ledger, the read-only view and the chain at the call's memory *)
assert (HFOOT : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ wv_wr (spZ regs) x)
  by (eapply (wv_foot_wr ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf);
      [lia | exact HPREx | exact HLED | exact HLOC | exact HD]).
assert (HNODEc : pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D).
{ apply (wv_nodeR_keep W W mem memc Lam v t D HNODE).
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & A2 & _). split; assumption.
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & _ & A3). apply HKEEP; assumption. }
assert (HOUTc : prhWriter_out W memc Lam o buf st)
  by (eapply (wv_out_keep ly S Hp W W mem memc md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran o buf st
        (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HOUT | exact HKEEP | exact HLOW | exact HOFF]).
assert (HLEDc : prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own)
  by (eapply (wv_led_keep ly S Hp W md mem memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran
        (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HKEEP | exact HLOW8]).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc))
  by (apply (wv_arodata_keep W W mem memc (wv_wr (spZ regs))); [exact HRO | exact HKEEP | exact HLOW]).
assert (HCHc : achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch).
{ rewrite Hs0c. apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hchain);
    [lia | lia |]. intros a Ha. apply HKEEP; [lia | unfold wv_wr; lia]. }
exact (wv_tail_put rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf
  st s bs memc mdc regsc ltac:(lia) HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODEc HLOC HD Hoff HJ
  ltac:(intros a Ha; apply HKEEP; [lia | unfold wv_wr; lia])
  HAP Hsp Hrac Hgpc Htpc HCHc HROc H10 H11 H12 Hcut Hch0 HOUTc HLEDc Hev Hsrc Hhome Hwmax Hhead Hcons Hlive HMN).
Qed.

(* ---- THE TAIL put FROM A MID STATE (the closing bracket of a container): the state at the call is reached from the
   entry through write_value's own stretches and calls (the caller journal and the window keep from the entry), the
   writer has run the pieces P0 (opened: outcomes ok1, ledger Lam1 / peak1 / ran1, buffer buf1 at the call); the
   tail put's own run [bs] composes with it (prhWriter_ret_app) into the kit's post over P0 ++ [bs] ---- *)
Lemma wv_tail_gen : forall {most own : Z} rp_sm rp_x rp_os rp_i rp_H0
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf (st : WriterApp.wst) (P0 : list (list Z)) s (bs : list Z)
    lyc Sc Hpc Wc memc mdc kc regsc ok1 ran1 buf1 Lam1 peak1 rp_i1 rp_hist1,
  176 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
     aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a) ->
  room_live_cf Sc -> rp_i1 = (rp_i + length (prhWriter_evs ok1 st P0))%nat ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 Sc ->
  (length rp_os <= 4)%nat ->
  prh_oks ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P0) (prhWriter_reqs ok1 st P0)
    most ran ran1 ->
  prh_granted ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P0) ->
  prhWriter_out Wc memc Lam1 o buf1 (prhWriter_putN ok1 st P0) ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st P0))
    (WriterApp.w_fail (prhWriter_putN ok1 st P0)) ran1 most own ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lam1 peak1 buf1 (prhWriter_putN ok1 st P0) ->
  aregs_preserved regs regsc -> spZ regsc = spZ regs -> getr regsc 1 = getr regs 1 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview SEGS (w_H Wc) memc) (spZ regs) (s0Z regsc) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H Wc) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H Wc) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (P0 ++ [bs])) ->
  src_rd Wc memc s bs ->
  prhWriter_src_home B lyc Sc Lam1 buf1 (WriterApp.w_cap (prhWriter_putN ok1 st P0)) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok1 st P0))) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i1 (length (prhWriter_evs [] (prhWriter_putN ok1 st P0) [bs])) ->
  prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok1 st P0) [bs]) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fpostWR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W
       mem md
       (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st (P0 ++ [bs]) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P0 ++ [bs])) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (P0 ++ [bs])))%nat rp_H0 hist' S') /\
          (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem'))).
Proof.
intros most own rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf st P0 s bs
  lyc Sc Hpc Wc memc mdc kc regsc ok1 ran1 buf1 Lam1 peak1 rp_i1 rp_hist1
  HSTK HSTKp HPRE Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKW Hroom Hrpeq Hrp Hos4 Hoks1 G1 HOUT1 HLED1 HBLK1
  HAP Hspc Hrac Hgpc Htpc Hchc Hroc H10 H11 H12 Hcut Hch0 Hev Hsrc Hhome Hwmax Hhead Hcons Hlive.
pose proof HPRE as (HPREx & Hro & Htop).
pose proof HPREx as (HARe & Hret & Hra4 & _ & _ & Hstk & _).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (Hc0e : 0 <= WriterApp.w_cnt st)
  by exact (wv_led_cnt _ _ _ _ _ _ _ _ _ _ HLED).
pose proof (ajxR_ar HJ) as HARc.
eapply SRr'_mono.
- eapply (@YCbqGcallW.aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    Wc regsc memc (SIGMA AS_put)
    (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] lyc Sc Hpc mdc kc
    STK_put d (prhWriter_cfp o buf1 (WriterApp.w_cap (prhWriter_putN ok1 st P0))) (- d) (getr regs 1) ch
    (fun ly' S' Hp' W' regs' mem' md' =>
       tputP_Q B rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 most own lyc Sc o buf1 (prhWriter_putN ok1 st P0) bs Lam1 peak1
         ran1 ly' S' Hp' W' regs' mem' md' /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem')) HJ);
    [lia | apply wv_neg_mod16; exact Hd16 | lia | vm_compute; congruence | lia | lia | exact Hd16 | lia
    | exact Hgpc | exact Htpc | exact Hrac | exact Hret | unfold raZ in Hra4; exact Hra4
    | replace (spZ regs + d + - d) with (spZ regs) by lia; exact Hchc | | ].
  + intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + d) by lia.
    assert (Hfpre : fpre B ARx STK_put lyc Sc Hpc Wc regsc memc mdc ch).
    { split; [exact Hpre|]. split; [exact Hroc|].
      pose proof (ajxR_ly HJ) as Hly.
      assert (Eshi : ly_stk_hi lyc = ly_stk_hi ly)
        by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _); exact Eshi).
      split; [rewrite Hspc, Eshi; exact (proj1 Htop) | split; [unfold raZ; rewrite Hrac; exact (proj1 (proj2 Htop)) | exact (proj2 (proj2 Htop))]]. }
    pose proof HOUT1 as HOUT1'.
    exact (PUT fx rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 most own lyc Sc Hpc Wc regsc memc mdc ch o s (Z.of_nat (length bs)) d buf1
      (prhWriter_putN ok1 st P0) bs Lam1 peak1 ran1 Hfpre Hroom Hrp Hos4 Hcons Hcl H10 H11 H12
      ltac:(rewrite Hspc; exact Hcut) ltac:(rewrite Hspc; exact Hch0) Hwin Ho1' Ho2'
      HOUT1' HLED1 Hsrc eq_refl Hhome
      (fun Hg Hcf => prhWriter_ev_at rp_sm rp_x rp_os rp_i rp_i1 st P0 bs [] ok1 Hev Hrpeq Hg Hcf)
      Hwmax Hhead Hlive).
  + apply (wv_fp_sub (STKv + d) (spZ regs + d) ly S lyc Sc Hpc Wc memc mdc o Lam peak buf st Lam1 peak1 buf1
      (prhWriter_putN ok1 st P0) HARc (proj1 Hcap0) HBLK1).
- cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HXT & HP2 & HQ).
  exists ly2, S2, Hp2, regs2, mem2, md2, (kc + k1)%Z.
  split; [exact Hc2|].
  split; [exact HJ2|].
  assert (HKW2 : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hf. rewrite <- (HKW a Ha Hf). apply HXT; [lia|].
    intros Hf1. apply Hf. unfold prhWriter_cfp in Hf1 |- *. apply inFP_cons in Hf1. apply inFP_cons.
    destruct Hf1 as [Hs | Hb]; [left; exact Hs|]. exfalso.
    unfold prhWriter_fp in Hb. destruct (Z.eqb_spec (WriterApp.w_cap (prhWriter_putN ok1 st P0)) 0) as [_|Hc1];
      [exact (inFP_nil a Hb)|].
    destruct HOUT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin1 & _)]); [lia|].
    pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED1) as HF1.
    destruct (HF1 _ Hin1) as (_ & Hbl1 & _). cbn [fst snd] in Hbl1.
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hbl1) as (_ & _ & Hce & _).
    destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
    pose proof Hstk as (_ & _ & Hceil & Hslo & _). lia. }
  split; [exact HKW2|].
  split; [exact (aregs_preserved_trans regs regsc regs2 HAP HP2)|].
  destruct HQ as (HQq & HQM).
  apply tputP_R_of in HQq. destruct HQq as (okp & HR).
  split; [|exact HQM].
  split; [exact (tputP_room HR)|]. split.
  + apply (wv_nodeR_keep W W2 mem mem2 Lam v t D HNODE).
    * intros x Hx. exact (proj1 (wv_foot_keep ly S Hp W regs mem md STKv (STKv + d) d o buf
        (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D
        ly2 S2 Hp2 W2 mem2 md2 (kc + k1) ltac:(lia) Hd0 HARe Hstk HLED HLOC HD Hoff (proj1 Hcap0) Hbufin
        HJ2 HKW2 x Hx)).
    * intros x Hx. exact (proj2 (wv_foot_keep ly S Hp W regs mem md STKv (STKv + d) d o buf
        (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D
        ly2 S2 Hp2 W2 mem2 md2 (kc + k1) ltac:(lia) Hd0 HARe Hstk HLED HLOC HD Hoff (proj1 Hcap0) Hbufin
        HJ2 HKW2 x Hx)).
  + exact (prhWriter_ret_pos_step B rp_sm rp_x rp_os rp_H0 rp_i rp_i1 rp_hist1 ly S Lam peak ran most own o buf st P0 bs
      ok1 ran1 buf1 Lam1 peak1 lyc Sc Hpc Wc memc ly2 S2 Hp2 W2 regs2 mem2 md2 Hc0e Hrpeq Hoks1 G1 HOUT1 HLED1 HBLK1
      (conj (tputP_pos_keep HR) (tputP_pos_grow HR)) (ex_intro _ okp (conj (tputP_ret_ok HR) (tputP_granted HR)))).
Qed.

(* s0 is callee-saved *)
Lemma wv_s0_pres : forall regs regs', aregs_preserved regs regs' -> s0Z regs' = s0Z regs.
Proof. intros regs regs' H. unfold s0Z. exact (f_equal bv_unsigned (H 8 ltac:(unfold acallee_saved; lia))). Qed.

Lemma wv_tail_put_string : forall {most own : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  176 <= STKv -> STK_put_string <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, spZ regs <= a < spZ regs + d -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> spZ regsc = spZ regs -> getr regsc 1 = getr regs 1 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  s0Z regsc = o \/ s0Z regsc < YM05.alloc_ceiling ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  cstr_ok W memc s bs ->
  kept_at B Lam s (Z.of_nat (length bs) + 1) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (WriterApp.w_cap st = 0 \/ s + Z.of_nat (length bs) + 1 <= buf \/ buf + WriterApp.w_cap st <= s) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  prh_live_evs S (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (fpostWFmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp
       W mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st (WriterSpec.spieces bs) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S')).
Proof.
intros most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEPW
  HAP Hspc Hrac Hgpc Htpc Hchc Hroc H10 H11 Hcut Hch0 Hs0c HOUTc HLEDc Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hcons Hlive
  HMN.
pose proof HPRE as (HPREx & Hro & Htop).
pose proof HPREx as (HARe & Hret & Hra4 & _ & _ & Hstk & _).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
eapply SRr'_mono.
- eapply (@YCbqGcallW.aj_call_xWFR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    W regsc memc
    (SIGMA AS_put_string)
    (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp mdc 0
    STK_put_string d (prhWriter_cfp o buf (WriterApp.w_cap st)) (- d) (getr regs 1) ch
    (fun ly' S' Hp' W' regs' mem' md' =>
       tpusP_Q B rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem'))
       (wv_jlift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ));
    [lia | apply wv_neg_mod16; exact Hd16 | lia | vm_compute; congruence | lia | lia | exact Hd16 | lia
    | exact Hgpc | exact Htpc | exact Hrac | exact Hret | unfold raZ in Hra4; exact Hra4
    | replace (spZ regs + d + - d) with (spZ regs) by lia; exact Hchc | | ].
  + intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + d) by lia.
    assert (Hfpre : fpre B ARx STK_put_string ly S Hp W regsc memc mdc ch).
    { split; [exact Hpre|]. split; [exact Hroc|].
      split; [rewrite Hspc; exact (proj1 Htop) | split; [unfold raZ; rewrite Hrac; exact (proj1 (proj2 Htop)) | exact (proj2 (proj2 Htop))]]. }
    exact (PUTSTR fx rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regsc memc mdc ch o s d buf st bs Lam peak ran
      Hfpre Hroom Hrp Hcl Hos4 Hcons H10 H11 ltac:(rewrite Hspc; exact Hcut) ltac:(rewrite Hspc; exact Hch0)
      Hs0c Hwin Ho1' Ho2' HOUTc HLEDc Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive).
  + intros a Ha. left. exact Ha.
- cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HFZ & HFK & HJ2 & HJc & HXT & HP2
    & HQ).
  exists fx', ly2, S2, Hp2, regs2, mem2, md2, (0 + k1)%Z.
  split; [exact Hc2|]. split; [exact HFZ|]. split; [exact HFK|].
  split; [exact HJ2|].
  split.
  { intros a Ha Hf. rewrite (HXT a ltac:(lia) Hf). exact (HKEEPW a Ha). }
  split; [exact (aregs_preserved_trans regs regsc regs2 HAP HP2)|].
  destruct HQ as (HQq & HQM).
  apply tpusP_R_of in HQq. destruct HQq as (okp & histp & HR).
  split; [|intros Hmn; exact (HQM (HMN Hmn))].
  split; [exact (tpusP_room HR)|].
  split; [|exact (ex_intro _ okp (conj (tpusP_ret_ok HR) (conj (tpusP_granted HR) (ex_intro _ histp (tpusP_pos HR)))))].
  assert (HJc' : ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
      (STK_put_string + d) (spZ regs + d)
      (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
  { replace (spZ regs + d) with (spZ regs + d + - d + d) by lia. exact HJc. }
  apply (wv_nodeR_keep W W2 memc mem2 Lam v t D HNODE).
  + intros x Hx. exact (proj1 (wv_foot_keep ly S Hp W regs memc mdc STKv (STK_put_string + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (ajx_ar HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
  + intros x Hx. exact (proj2 (wv_foot_keep ly S Hp W regs memc mdc STKv (STK_put_string + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (ajx_ar HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
Qed.


Lemma wv_call_put : forall {gm go : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o s n buf (st : WriterApp.wst) (bs : list Z) Lam peak ran oc,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0 mem0
    md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_put - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 n ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gm go ->
  src_rd W memc s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B lyc Sc Lam buf (WriterApp.w_cap st) s n ->
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + n + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_live_evs Sc (prhWriter_evs [] st [bs]) ->
  fp_sub_xW B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0
         mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_put + - oc)
         (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\ prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_i rp_hist st bs o W2 mem2 S2 /\
       prhWriter_retg B lyc Sc Lam peak ran gm go o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros gm go rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw
  ra1 nfp1 o s n buf st bs Lam peak ran oc
  HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab HFRM Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos4 Hcl H10 H11 H12 Ho1 Ho2 Hout Hled Hsrc
  Hlen Hhome Hevp Hwmax Hhead Hcons Hlive Hfp.
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply SRr'_mono.
{ eapply (@YCbqGcallW.aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    W regsc memc (SIGMA AS_put)
    STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_put (- oc)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1
    (fun ly' S' Hp' W' regs' mem' md' =>
       tputP_Q B rp_sm rp_x rp_os rp_i rp_H0 rp_hist gm go lyc Sc o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem')));
    [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | vm_compute; congruence | exact HSTK | lia
    | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hra4
    | rewrite Hs0; exact Hch | | ].
  - intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
    assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx))
      by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact HFRM]]).
    exact (PUT fx rp_sm rp_x rp_os rp_i rp_H0 rp_hist gm go lyc Sc Hpc W regsc memc mdc ch1 o s n (- oc) buf st bs Lam peak
      ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hos4 Hcons Hcl H10 H11 H12
      ltac:(left; lia) ltac:(intros _; exists ra1; split; [exact Hra1 | exists nfp1; split; [exact Hnfp1 | exact Hnfpc]])
      Hwin Ho1' Ho2' Hout Hled Hsrc Hlen Hhome Hevp Hwmax Hhead Hlive).
  - exact Hfp. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HXT & HP2 & HQq & HQM).
apply tputP_R_of in HQq. destruct HQq as (okp & HR).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HXT|]. split; [exact HP2|].
split; [|exact HQM]. split; [exact (tputP_room HR)|].
split; [exact (conj (tputP_pos_keep HR) (tputP_pos_grow HR)) |
  exact (ex_intro _ okp (conj (tputP_ret_ok HR) (tputP_granted HR)))].
Qed.

Lemma wv_call_indent : forall {gm go : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o pretty depth buf (st : WriterApp.wst) Lam peak ran oc,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0 mem0
    md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_indent - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 pretty -> getr regsc 12 = w64 depth ->
  0 <= pretty < 2 ^ 64 -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gm go ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wind (negb (pretty =? 0)) depth))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth))) ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  fp_sub_xW B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_indent)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0
         mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_indent + - oc)
         (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gm go o buf st (WriterValue.wind (negb (pretty =? 0)) depth)
            ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wind (negb (pretty =? 0)) depth)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wind (negb (pretty =? 0)%Z) depth)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros gm go rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw
  ra1 nfp1 o pretty depth buf st Lam peak ran oc
  HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab HFRM Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos4 Hcl H10 H11 H12 Hpr Hdep Ho1 Ho2 Hout
  Hled Hev Hwmax Hhead Hcons Hlive Hfp.
assert (HPF : 0 <= pi_frame F_indent) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (@YCbqGcallW.aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
  W regsc memc (SIGMA AS_indent)
  STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_indent (- oc)
  (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1);
  [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | vm_compute; congruence | exact HSTK | lia
  | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hra4
  | rewrite Hs0; exact Hch | | ].
- intros Hpre Hwin.
  assert (Ho1' : spZ regsc <= o) by lia.
  assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
  assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx))
    by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact HFRM]]).
  exact (INDENT fx rp_sm rp_x rp_os rp_i rp_H0 rp_hist gm go lyc Sc Hpc W regsc memc mdc ch1 o pretty depth (- oc) buf st
    Lam peak ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hos4 Hcons Hcl H10 H11 H12 Hpr Hdep
    ltac:(lia) (ex_intro _ ra1 (conj Hra1 (ex_intro _ nfp1 (conj Hnfp1 Hnfpc))))
    Hwin Ho1' Ho2' Hout Hled Hev Hwmax Hhead Hlive).
- exact Hfp.
Qed.

(* the loop's put_string call (an object's key, A 0x86f5c) *)
Lemma wv_call_put_string : forall {gm go : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o s buf (st : WriterApp.wst) (bs : list Z) Lam peak ran oc,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0 mem0
    md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_put_string - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gm go ->
  cstr_ok W memc s bs ->
  kept_at B Lam s (Z.of_nat (length bs) + 1) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (WriterApp.w_cap st = 0 \/ s + Z.of_nat (length bs) + 1 <= buf \/ buf + WriterApp.w_cap st <= s) ->
  Z.of_nat (length (frames Sc)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  fp_sub_xW B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       YK0o.frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0
         mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_put_string + - oc)
         (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gm go o buf st (WriterSpec.spieces bs) ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros gm go rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw
  ra1 nfp1 o s buf st bs Lam peak ran oc
  HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab HFRM Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos4 Hcl H10 H11 Ho1 Ho2 Hout Hled Hstr
  Hkept Hev Hapart Hfr0 Hwmax Hhead Hcons Hlive Hfp.
assert (HPF : 0 <= pi_frame F_put_string) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (@YCbqGcallW.aj_call_xWFR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
  W regsc memc
  (SIGMA AS_put_string) STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_put_string (- oc)
  (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1);
  [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | vm_compute; congruence | exact HSTK | lia
  | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hra4
  | rewrite Hs0; exact Hch | | ].
- intros Hpre Hwin.
  assert (Ho1' : spZ regsc <= o) by lia.
  assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
  assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx))
    by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact HFRM]]).
  exact (PUTSTR fx rp_sm rp_x rp_os rp_i rp_H0 rp_hist gm go lyc Sc Hpc W regsc memc mdc ch1 o s (- oc) buf st bs Lam peak
    ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hcl Hos4 Hcons H10 H11
    ltac:(left; lia) ltac:(intros _; exists ra1; split; [exact Hra1 | exists nfp1; split; [exact Hnfp1 | exact Hnfpc]])
    (or_introl Hs0) Hwin Ho1' Ho2' Hout Hled Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive).
- exact Hfp.
Qed.

(* THE RECURSIVE CALL (A 0x86f8c) at depth n - 1: the induction hypothesis is the callee's text *)
Lemma wv_call_self : forall {gm go : Z} (n' : nat) rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o v2 pretty dep buf (st : WriterApp.wst) (t2 : PjTree.jv) D2
    Lam peak ran oc,
  twrite_value_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0 n' ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0 mem0
    md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_write_value n' - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 v2 -> getr regsc 12 = w64 pretty -> getr regsc 13 = w64 dep ->
  0 <= pretty < 2 ^ 64 -> 0 <= dep < 2 ^ 31 -> dep + Z.of_nat (PjTree.depth t2) <= 2 ^ 31 - 1 ->
  (PjTree.depth t2 <= n')%nat ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gm go ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v2 t2 D2 ->
  ((sp0 + oc <= v2 /\ v2 + 56 <= ly_stk_hi lyc) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v2 /\ v2 + 56 <= x + y) \/ prhWriter_in_frame lyc Sc v2) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v2 56 ->
  prhWriter_tree_vis W memc D2 ->
  (forall a k0, In (a, k0) D2 -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v2 D2 x) ->
  Z.of_nat (length (frames Sc)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep))) ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) ->
  fp_sub_xW B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_write_value)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       YK0o.frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0
         mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
         (STK_write_value n' + - oc) (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\ pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) v2 t2 D2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gm go o buf st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)
            ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces t2 (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros gm go n' rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc
  raw ra1 nfp1 o v2 pretty dep buf st t2 D2 Lam peak ran oc
  IH HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab HFRM Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos4 Hcl H10 H11 H12 H13 Hpr Hdep Hdep2
  Hdn Ho1 Ho2 Hout Hled Hev Hnode Hloc Hra56 Hvis HD Hoff Hfr0 Hwmax Hhead Hcons Hlive Hfp.
assert (HPF : 0 <= pi_frame F_write_value) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (@YCbqGcallW.aj_call_xWFR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS pa_segs_low
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
  W regsc memc
  (SIGMA AS_write_value) STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k (STK_write_value n') (- oc)
  (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1);
  [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | unfold STK_write_value; vm_compute; congruence
  | exact HSTK | lia | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw
  | exact Hra4 | rewrite Hs0; exact Hch | | ].
- intros Hpre Hwin.
  assert (Ho1' : spZ regsc <= o) by lia.
  assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
  assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx))
    by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact HFRM]]).
  assert (Hloc' : (spZ regsc <= v2 /\ v2 + 56 <= ly_stk_hi lyc) \/
     (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v2 /\ v2 + 56 <= x + y) \/ prhWriter_in_frame lyc Sc v2)
    by (rewrite Hsp; exact Hloc).
  exact (IH rp_sm rp_x rp_os rp_i rp_H0 rp_hist gm go lyc Sc Hpc W regsc memc mdc ch1 o v2 pretty dep (- oc) buf st t2
    D2 Lam peak ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hos4 Hcons Hcl H10 H11 H12 H13 Hpr Hdep Hdep2 Hdn
    ltac:(left; lia) ltac:(intros _; exists ra1; split; [exact Hra1 | exists nfp1; split; [exact Hnfp1 | exact Hnfpc]])
    (or_introl Hs0) Hwin Ho1' Ho2' Hout Hled Hev Hnode Hloc' Hra56 Hvis HD Hoff Hfr0 Hwmax Hhead Hlive).
- exact Hfp.
Qed.
(* ---- THE THREE LITERAL LEAVES: null (case 121), false (125), true (102). Each seats the entry state at its tag,
   takes the switch's jump through wv_jr_step, runs the case to the tail `put` (AF + 4 * 236) and closes the kit's whole
   post with wv_put_close. MEASURED (cb, this base): at tag 0 the run stops at the jr AF + 4 * 35, the case offset is
   AF + 4 * 121, and the stop before the tail call has a0 = the entry a0 (= o), a1 = .rodata + wv_addhi_off 122
   ("null"), a2 = 4, with ra / sp / s0 .. s11 back at their entry atoms. ---- *)

Lemma wv_leaf_lit : forall {most own : Z} t, (t = PjTree.JNull \/ t = PjTree.JFalse \/ t = PjTree.JTrue) ->
  forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) D Lam peak ran STKv,
  184 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep))) ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_write_value) regs mem md)
    (fpostWFmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp
       W mem md
       (twvP_Q B rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran)).
Proof.
intros most own t Ht rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch o v pretty dep d buf st D Lam peak ran STKv
  HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl H10 H11 H12 H13 Hcut Hch0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HD Hoff
  Hwmax Hhead Hcons Hlive.
(* no float instruction runs: the m-form post at the entry float state fx is the float m-form, by fpre's frm_zero *)
eapply SRr'_mono; cycle 1.
{ intros W' c' _ HP. exact (wv_postWF_of_W fx fx _ _ _ _ _ _ _ _ _ _ _ W' c'
    (proj2 (proj2 (proj2 (proj2 HPRE)))) (wv_fk_refl fx) HP). }
(* the leaf crosses no free before its tail call: it runs at SRr up to put's entry *)
apply wv_srr_pre.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
(* The kit's location premise, its ONE use *)
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
(* the journal, widened to the caller window, and the memory invariant of the m-form post *)
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (PLAWI : srr_inv_laws SEGS (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m))
  by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
assert (HPM : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem) by (cbv beta; exact (fun h => h)).
pose proof HNODE as HNODE0.
(* the literal leaf at tag tg (jump-table index kn), the literal formed by the PAddHi at slot, of bytes bs: from the
   entry to the tail `put` and the kit's post *)
let run tg kn slot bs := idtac;
  destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody);
  destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
    (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap));
  destruct (HJT kn ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro);
  change (4 * Z.of_nat kn) with (4 * tg) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro;
  assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 (WV_JTW (Z.to_nat tg)))
    by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
        intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
        split; [exact R1 | split; [exact R2 | exact R3]]);
  assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * tg)
    by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 v 56 ltac:(lia) ltac:(lia)
          ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]);
  (* the seated entry state at tag tg *)
  destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
    Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
    Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
    HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK];
  set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) in *;
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env);
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) k)
    by (intros k Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk);
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
  assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) E)
    by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | reflexivity]);
  assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
    by (intros; reflexivity);
  unfold cfg_at; rewrite Hent; change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value));
  (* entry -> the switch's jr *)
  paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS HJ SHOK HPM WV_Bspan;
  [ eapply (wv_awr E tg _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ];
  wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  (* the switch's indirect jump, and the reseat at the case offset *)
  prreg HS (11%bv : bv 5) R11;
  assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat tg)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6));
  assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia);
  destruct (wv_jr_target E (Z.to_nat tg) E38 EJ HTr) as (Ht & Hr & He);
  eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case kn) HS);
  [ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ];
  let mat' := fresh "mat" in let ms1 := fresh "ms" in let Hms1 := fresh "Hms" in let HS1 := fresh "HS1" in
  intros mat' ms1 Hms1 HS1; subst ms1;
  pose proof (wv_pi_at E _ (AF_wv_case kn) _ HS1) as HS2; clear HS1;
  assert (HJ2 := HJ);
  eapply (ajournal_x_materialize (SK := SK)) with (X := mat') in HJ2;
  [| first [exact LAWS | exact pa_segs_low | idtac] ..];
  clear HJ;
  (* the case to the tail put *)
  paj_run_to_tok_x_inv (@paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan
    (AF_write_value + 4 * 236);
  [ wv_awr_tac Usp d | ];
  wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  (* the tail jump itself (A 0x8703c `j put`): one more run step stops at put's entry *)
  paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
  [ wv_awr_tac Usp d | ];
  wv_keep_run HFr K2 K3 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  (* the registers at put's entry *)
  prreg HS2 (10%bv : bv 5) Ra0; prreg HS2 (11%bv : bv 5) Ra1; prreg HS2 (12%bv : bv 5) Ra2;
  prreg HS2 (1%bv : bv 5) Rra;
  lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
    assert (HAP : aregs_preserved regs (ms_regs msx))
      by (eapply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs _); [exact HS2 | exact HAE | vm_compute; reflexivity]);
    assert (Rrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rra; exact E1);
    assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Ra0, E10; exact H10);
    assert (HAT : wv_addhi_atom slot = A_OBJ 2) by (vm_compute; reflexivity);
    assert (H11c : getr (ms_regs msx) 11 = w64 (WV_STR slot))
      by (rewrite Ra1; unfold WV_STR; rewrite HAT; rewrite HEI by (unfold A_OBJ, A_TEXT, A_LIM; lia);
          let off := eval vm_compute in (wv_addhi_off slot) in change (wv_addhi_off slot) with off; reflexivity);
    assert (H12c : getr (ms_regs msx) 12 = w64 (Z.of_nat (length bs))) by (rewrite Ra2; reflexivity);
    pose proof (ajx_ar HJ2) as HARc;
    assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem msx)))
      by (apply (wv_arodata_keep W W mem (ms_mem msx) (wv_wr (spZ regs))); [exact HRO | exact K3 | exact HLOW]);
    destruct (HLIT slot bs ly S Hp W (ms_mem msx) _
      ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right])) HARc HROc)
      as (Hsrc & Hkept & Himg);
    pose proof (wv_lit_home ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf
      (WriterApp.w_cap st) (WV_STR slot) (Z.of_nat (length bs)) HAR HLED Hbufin (proj1 Hcap0) ltac:(vm_compute; reflexivity)
      Hkept ltac:(intros a Ha; replace a with (WV_STR slot + (a - WV_STR slot)) by lia; apply Himg; lia)) as Hhome;
    assert (Hch0c : spZ regs + 16 <= o ->
        exists ra, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 8) = Some ra /\
          exists nfp, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
      by (intros Hge; apply (wv_reca_keep (aview SEGS (w_H W) mem)); [| exact (Hch0 Hge)];
          intros a Ha; apply K3; [lia | unfold wv_wr; lia]);
    pmkst HS2; apply SRr_ret;
    exact (wv_put_close rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v _ D Lam peak ran buf
      st (WV_STR slot) bs (ms_mem msx) _ (ms_regs msx) HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE0
      HLOC HD Hoff HJ2 K3 HAP Rrac H10c H11c H12c Hcut Hch0c Hev Hsrc Hhome Hwmax Hhead Hcons Hlive HPM)
  end
in
destruct Ht as [-> | [-> | ->]];
[ run 0 0%nat 122%nat [110; 117; 108; 108]
| run 1 1%nat 126%nat [102; 97; 108; 115; 101]
| run 2 2%nat 103%nat [116; 114; 117; 101] ].
Qed.

(* ---- THE STRING LEAF (case 61) and THE NUMBER LEAF (case 105): the string / number text lives in a ledger block
   (pj_nodeR's pj_cstrR: In (str, k) Lam), whose user pointer the code loads from v + 16 and tests against 0 (the
   0 arm is refuted by the ledger: the block's base is at least 4096). The string tail-calls put_string (slot 86);
   the number calls the strlen wrapper (slot 116) and tail-calls put (slot 236). ---- *)

(* a ledger block's user range: 4096 or above, below alloc_ceiling *)
Lemma wv_lam_low : forall {most own : Z} ly S Hp W mem md Lam peak cnt fail ran a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  4096 <= a /\ 0 <= k /\ a + k <= YM05.alloc_ceiling.
Proof.
intros most own ly S Hp W mem md Lam peak cnt fail ran a k HAR HLED Hin.
pose proof cf_head_nonneg as Hh0.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). cbn [fst snd] in Hk0, Hbl.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl)
  as (_ & H4096 & Hpc & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.

(* the shadow hull of a sub-range (YGcfHeadSh.v's shadow_hull_vis_sub_cf, the same proof; that file is not Required
   here) *)
Lemma wv_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia))
  as D4.
lia.
Qed.

(* a byte list survives a change that keeps its bytes' view *)
Lemma wv_garr8_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
refine (wv_vm_keep H H' m m' (a + Z.of_nat j) 1%nat _ _ Hv).
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (Hk j Hj).
Qed.

(* THE TREE'S STRING IS A C STRING THE RUNTIME MAY READ: a ledger block (str, k) holding s and its NUL, with
   tree_vis_cf's facts for (str, k) (its granule end `(str + k + 7) / 8 * 8 <= alloc_ceiling` among them), is
   cstr_ok: the cut's cstr_ok asks `str + len + 1 <= alloc_ceiling` (PRH_Base.v ef7c8ca98529 :1603), below the block's
   end. amem_range8's high start: the block base and str are both 16-aligned (alx_blocks, prh_hblock), so
   8 <= cf_head gives cf_head >= 16. *)
Lemma wv_cstr_blk : forall {most own : Z} ly S Hp W0 mem0 md0 Lam peak cnt fail ran (W : world SEGS) m str k s,
  ARx ly S Hp W0 mem0 md0 -> prh_ledger B ly S Hp W0 mem0 Lam peak cnt fail ran most own ->
  In (str, k) Lam -> Z.of_nat (length s) + 1 <= k -> Z.of_nat (length s) + 1 < 2 ^ 32 ->
  Forall (fun c => 0 < c < 256) s -> garr8 SEGS (mrestrict (w_H W) m) str (s ++ [0]) ->
  (str + k + 7) / 8 * 8 <= YM05.alloc_ceiling ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF str k ->
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W) m) str k) ->
  (forall x, str <= x < (str + k + 7) / 8 * 8 -> aview SEGS (w_H W) m x <> None) ->
  cstr_ok W m str s.
Proof.
intros most own ly S Hp W0 mem0 md0 Lam peak cnt fail ran W m str k s HAR HLED Hin Hlen Hlen32 Hrng Hg Hgap HRA HHULL HVIS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hgk : str + k <= YM05.alloc_ceiling)
  by (pose proof (Z.div_mod (str + k + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (str + k + 7) 8 ltac:(lia)); lia).
pose proof cf_head_nonneg as Hh0. pose proof HW as HW8. unfold prh_head_wide in HW8.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (str, k) Hin) as (Hk0 & Hbl & _ & Ha16 & _). cbn [fst snd] in Hk0, Hbl, Ha16.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W0 mem0 md0 (str - cf_head) (k + cf_head) HAR Hbl)
  as (H16 & H4096 & Hpc & Happ & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
unfold cstr_ok, cstr. set (n := Z.of_nat (length s)) in *.
split; [split; [exact Hg | rewrite Forall_forall in Hrng |- *; intros c Hc; specialize (Hrng c Hc); lia] |].
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold YGcfStr.amem_range8. rewrite C3, C4, C5.
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. rewrite C3 in Happ.
  destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left; lia | right].
  apply Z.mod_divide in H16 as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ha16 as [q2 Hq2]; [|lia].
  split; lia. }
split; [eapply range_addressable_sub; [exact HRA | lia | lia] |].
split; [apply (wv_hull_sub _ str k str (n + 1) (HHULL ltac:(lia))); lia |].
intros x Hx. apply HVIS.
assert (Hn0 : 0 <= n) by (subst n; lia). clearbody n.
pose proof (Z.div_mod (str + n) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (str + n) 8 ltac:(lia)) as D1b.
assert (D3 : (str + n) / 8 + 1 <= (str + k + 7) / 8).
{ replace ((str + n) / 8 + 1) with ((str + n + 1 * 8) / 8) by (rewrite Z.div_add by lia; reflexivity).
  apply Z.div_le_mono; lia. }
clear - Hx D1 D1b D3 Hn0 Hlen. lia.
Qed.

(* two distinct ledger blocks are apart (the sep half of alx_blocks), so a tree block other than the buffer misses it *)
Lemma wv_blk_apart : forall {most own : Z} ly S Hp W mem md Lam peak cnt fail ran a k buf cap n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> a <> buf -> (cap <> 0 -> In (buf, cap) Lam) -> 0 <= n -> n <= k ->
  cap = 0 \/ a + n <= buf \/ buf + cap <= a.
Proof.
intros most own ly S Hp W mem md Lam peak cnt fail ran a k buf cap n HAR HLED Hin Hab Hbuf Hn Hnk.
destruct (Z.eq_dec cap 0) as [->|Hc0]; [left; reflexivity|]. right.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). pose proof (HF (buf, cap) (Hbuf Hc0)) as (Hc00 & Hblb & _).
cbn [fst snd] in Hk0, Hbl, Hc00, Hblb.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl)
  as (_ & _ & _ & _ & _ & Hpw).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
assert (Hrqb : cap + cf_head <= req_size (cap + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); lia).
pose proof cf_head_nonneg as Hh0.
destruct (wv_pairwise_in2 zdisjoint _ (a - cf_head, req_size (k + cf_head))
    (buf - cf_head, req_size (cap + cf_head)) Hpw
    (in_map (fun b => (fst b, req_size (snd b))) _ _ Hbl)
    (in_map (fun b => (fst b, req_size (snd b))) _ _ Hblb)
    ltac:(intros E; injection E as E1 _; lia)) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* ---- FROM THE STATE AT THE TAIL put_string TO THE KIT'S WHOLE POST (wv_put_close's twin): the leaf supplies the string's
   cstr_ok / kept_at / apartness at the call memory, the frames count and the room ---- *)
Lemma wv_put_string_close : forall {most own : Z} rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  184 <= STKv -> STK_put_string <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> getr regsc 1 = getr regs 1 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling ->
  cstr_ok W memc s bs ->
  kept_at B Lam s (Z.of_nat (length bs) + 1) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (WriterApp.w_cap st = 0 \/ s + Z.of_nat (length bs) + 1 <= buf \/ buf + WriterApp.w_cap st <= s) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  prh_live_evs S (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (fpostWFmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp
       W mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st (WriterSpec.spieces bs) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S')).
Proof.
intros most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEP
  HAP Hrac H10 H11 Hcut Hch0 HS0e Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hcons Hlive HMN.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ wv_wr (spZ regs) a)
  by (intros a Ha; unfold wv_wr; lia).
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a)
  by (intros a Ha; unfold wv_wr; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ wv_wr (spZ regs) a)
  by (intros a Ha; split; [lia | unfold wv_wr; lia]).
assert (Hsp : spZ regsc = spZ regs)
  by (unfold spZ; f_equal; exact (HAP 2 ltac:(unfold acallee_saved; lia))).
assert (Hgpc : getr regsc 3 = w64 (as_gp B))
  by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regsc 4 = w64 (as_tp B))
  by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hs0c : s0Z regsc = s0Z regs)
  by (unfold s0Z; f_equal; exact (HAP 8 ltac:(unfold acallee_saved; lia))).
assert (HFOOT : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ wv_wr (spZ regs) x)
  by (eapply (wv_foot_wr ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf);
      [lia | exact HPREx | exact HLED | exact HLOC | exact HD]).
assert (HNODEc : pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D).
{ apply (wv_nodeR_keep W W mem memc Lam v t D HNODE).
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & A2 & _). split; assumption.
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & _ & A3). apply HKEEP; assumption. }
assert (HOUTc : prhWriter_out W memc Lam o buf st)
  by (eapply (wv_out_keep ly S Hp W W mem memc md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran o buf st
        (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HOUT | exact HKEEP | exact HLOW | exact HOFF]).
assert (HLEDc : prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own)
  by (eapply (wv_led_keep ly S Hp W md mem memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran
        (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HKEEP | exact HLOW8]).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc))
  by (apply (wv_arodata_keep W W mem memc (wv_wr (spZ regs))); [exact HRO | exact HKEEP | exact HLOW]).
assert (HCHc : achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch).
{ rewrite Hs0c. apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hchain);
    [lia | lia |]. intros a Ha. apply HKEEP; [lia | unfold wv_wr; lia]. }
exact (wv_tail_put_string rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran
  buf st s bs memc mdc regsc ltac:(lia) HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODEc HLOC HD Hoff HJ
  ltac:(intros a Ha; apply HKEEP; [lia | unfold wv_wr; lia])
  HAP Hsp Hrac Hgpc Htpc HCHc HROc H10 H11 Hcut Hch0 ltac:(rewrite (wv_s0_pres _ _ HAP); exact HS0e)
  HOUTc HLEDc Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hcons Hlive HMN).
Qed.

Lemma wv_leaf_str : forall {most own : Z} s,
  forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) D Lam peak ran STKv,
  184 <= STKv -> STK_put_string <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v (PjTree.JStr s) D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep))) ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_write_value) regs mem md)
    (fpostWFmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp
       W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
          room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v (PjTree.JStr s) D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st
            (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)%Z) dep)))%nat
            rp_H0 hist' S')).
Proof.
intros most own s rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch o v pretty dep d buf st D Lam peak ran STKv
  HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl H10 H11 H12 H13 Hcut Hch0 HS0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HTV HD Hoff Hfr0
  Hwmax Hhead Hcons Hlive.
(* the leaf crosses no free before its tail call: it runs at SRr up to put_string's entry *)
apply wv_srr_pre.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (HPF : 0 <= pi_frame F_put_string) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (PLAWI : srr_inv_laws SEGS (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m))
  by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
assert (HPM : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem) by (cbv beta; exact (fun h => h)).
pose proof HNODE as HNODE0.
destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
  (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap)).
destruct Hbody as (_ & _ & _ & _ & k & Hcs & ->).
pose proof Hcs as (Hlam & Hlen & Hlen32 & Hrng & Hgs). unfold prh_lin in Hlam.
destruct (wv_lam_low ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran str k HAR HLED Hlam)
  as (Hs4096 & Hk0 & Hsk).
pose proof (proj1 (proj2 (proj2 (HTV str k (or_introl eq_refl))))) as Hgap1.
destruct (HJT 4%nat ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro).
change (4 * Z.of_nat 4) with (4 * 4) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro.
assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * 4) 4 (WV_JTW (Z.to_nat 4)))
  by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
      intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
      split; [exact R1 | split; [exact R2 | exact R3]]).
assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * 4 + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * 4)
  by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * 4) 4 v 56 ltac:(lia) ltac:(lia)
        ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]).
destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep 4 str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
  Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
  Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
  HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat 4))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 4)))) k)
  by (intros k0 Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 4)))) E)
  by (split; [intros k0 Hk; apply EL; unfold A_TEXT; lia | reflexivity]).
assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by (intros; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value)).
(* entry -> the switch's jr *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS HJ SHOK HPM WV_Bspan;
[ eapply (wv_awr E 4 _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ].
wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
prreg HS (11%bv : bv 5) R11.
assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat 4)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
destruct (wv_jr_target E (Z.to_nat 4) E38 EJ HTr) as (Ht & Hr & He).
eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case 4) HS);
[ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ].
intros mat1 ms1 Hms1 HS1. subst ms1.
pose proof (wv_pi_at E _ (AF_wv_case 4) _ HS1) as HS2. clear HS1.
assert (HJ2 := HJ).
eapply (ajournal_x_materialize (SK := SK)) with (X := mat1) in HJ2;
[| first [exact LAWS | exact pa_segs_low | idtac] ..].
clear HJ.
(* the case: the shadow check of v + 16, the load of str, and the stop at `bnez a1` (MEASURED: the run stops at
   write_value + 4 * 68 with a1 = SOff 34 0, the str atom) *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
psrr_branch_tok (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) BR HS2 SHOK WV_Bspan.
2:{ (* str = 0: refuted, a ledger block's user pointer is at least 4096 *)
  exfalso.
  rewrite ?branch_ne_U, ?branch_eq_U, (U_atom E 34 str E34 Rstr), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hs0 : (str =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hs0' : (0 =? str) = false) by (apply Z.eqb_neq; lia).
  rewrite ?Hs0, ?Hs0' in Hc. cbn in Hc. discriminate Hc. }
(* str <> 0: the epilogue, then the tail `j put_string` (write_value + 4 * 86) and put_string's entry *)
paj_run_to_tok_x_inv (@paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan
  (AF_write_value + 4 * 86);
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K2 K3 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K3 K4 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
prreg HS2 (10%bv : bv 5) Ra0. prreg HS2 (11%bv : bv 5) Ra1. prreg HS2 (1%bv : bv 5) Rra.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HAP : aregs_preserved regs (ms_regs msx))
    by (eapply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs _); [exact HS2 | exact HAE | vm_compute; reflexivity]);
  assert (Rrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rra; exact E1);
  assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Ra0, E10; exact H10);
  assert (H11c : getr (ms_regs msx) 11 = w64 str) by (rewrite Ra1, E34; reflexivity);
  (* the string at the call memory: the tree's block (str, k), kept below alloc_ceiling *)
  assert (HTVc : prhWriter_tree_vis W (ms_mem msx) [(str, k)])
    by (exact (wv_tree_vis_keep W W mem (ms_mem msx) [(str, k)] (wv_wr (spZ regs)) HTV K4 HLOW));
  destruct (HTVc str k (or_introl eq_refl)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7);
  assert (Hgsc : garr8 SEGS (mrestrict (w_H W) (ms_mem msx)) str (s ++ [0]))
    by (apply (wv_garr8_keep (w_H W) (w_H W) mem (ms_mem msx) str (s ++ [0])); [|exact Hgs];
        intros j Hj; rewrite length_app in Hj; cbn [length] in Hj; apply K4; [lia | unfold wv_wr; lia]);
  pose proof (wv_cstr_blk ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran W (ms_mem msx)
    str k s HAR HLED Hlam Hlen Hlen32 Hrng Hgsc Hgap1 T5 T6 T7) as Hcstr;
  assert (Hkept : kept_at B Lam str (Z.of_nat (length s) + 1)) by (left; exists str, k; split; [exact Hlam | lia]);
  pose proof (wv_blk_apart ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran str k buf
    (WriterApp.w_cap st) (Z.of_nat (length s) + 1) HAR HLED Hlam (proj2 (HD str k (or_introl eq_refl))) Hbufin
    ltac:(lia) Hlen) as Hapart; rewrite Z.add_assoc in Hapart;
  assert (Hch0c : spZ regs + 16 <= o ->
      exists ra, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 8) = Some ra /\
        exists nfp, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
    by (intros Hge; apply (wv_reca_keep (aview SEGS (w_H W) mem)); [| exact (Hch0 Hge)];
        intros a Ha; apply K4; [lia | unfold wv_wr; lia]);
  pmkst HS2; apply SRr_ret;
  exact (wv_put_string_close rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v _ _ Lam peak
    ran buf st str s (ms_mem msx) _ (ms_regs msx) HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE0
    HLOC HD Hoff HJ2 K4 HAP Rrac H10c H11c Hcut Hch0c HS0 Hcstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hcons Hlive HPM)
end.
Qed.

(* ---- the number leaf's helpers: the strlen call's byte premises (FuzzStrdup.v's sd_garr8_aview / sd_first_byte /
   sd_src_ok, the same proofs), a put source from a C string, and the close after a call that wrote below the own
   frame ---- *)
Lemma wv_garr8_aview : forall (W : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.

Lemma wv_first_byte : forall (W : world SEGS) m p cs, cstr W m p cs ->
  first_byte SEGS W m p (Z.of_nat (length cs) + 1) 0 (Z.of_nat (length cs)).
Proof.
intros W m p cs [Hg Hnz]. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cs 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (wv_garr8_aview W m p (cs ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _.
  rewrite (wv_garr8_aview W m p (cs ++ [0]) (length cs) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma wv_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (wv_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* a C string the runtime may read is a put source *)
Lemma wv_src_of_cstr : forall (W : world SEGS) m p l, cstr_ok W m p l -> src_rd W m p l.
Proof.
intros W m p l ((Hg & _) & H4096 & Hb & H32 & Ham & HRA & HH & _).
split; [exact (proj1 (proj1 (garr8_app SEGS _ p l [0]) Hg)) |].
split; [exact H4096 |]. split; [lia |].
split; [unfold YGcfStr.amem_range8 in Ham; unfold amem_range; lia |].
split; [eapply range_addressable_sub; [exact HRA | lia | lia] |].
intros Hl. apply (wv_hull_sub _ p (Z.of_nat (length l) + 1) p (Z.of_nat (length l)) HH); lia.
Qed.

(* THE TREE'S FOOTPRINT IS AT OR ABOVE THE ENTRY sp OR BELOW alloc_ceiling: the kit's three node locations and the
   ledger blocks of D *)
Lemma wv_foot_low : forall {most own : Z} ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v D,
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  forall x, pj_footR v D x -> spZ regs <= x \/ x < YM05.alloc_ceiling.
Proof.
intros most own ly S Hp W regs mem md ch STKv Lam peak cnt fail ran buf v D HPRE HLED HLOC HD x Hx.
pose proof HPRE as (HAR & _).
destruct Hx as [Hhdr | ([a k0] & HbD & Hb)].
- destruct HLOC as [(Hv1 & Hv2) | [(y0 & z0 & Hin & Hyb & Hyv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
  + left. lia.
  + right. destruct (wv_lam_low ly S Hp W mem md Lam peak cnt fail ran y0 z0 HAR HLED Hin) as (_ & _ & H). lia.
  + right. destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hfb).
    rewrite Forall_forall in Hfb. pose proof (Hfb (cid, pos) Hfr) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
- right. unfold pj_holdsR in Hb. cbn [fst snd] in Hb. destruct (HD a k0 HbD) as (Hin & _).
  destruct (wv_lam_low ly S Hp W mem md Lam peak cnt fail ran a k0 HAR HLED Hin) as (_ & _ & H). lia.
Qed.

(* ---- wv_put_close FOR A WIDER WRITE SET [lo, spZ regs) (the number leaf: its strlen call also writes the 2 * ESTACK
   below the own frame). Every keep is wv_put_close's over that set; lo above alloc_ceiling + 8 keeps the ledger, the
   struct, the read-only view and the tree (at or above the entry sp, or below alloc_ceiling: wv_foot_low). ---- *)
Lemma wv_put_close_x : forall {most own : Z} lo rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  176 <= STKv -> STK_put <= STKv -> YM05.alloc_ceiling + 8 <= lo ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < spZ regs) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> getr regsc 1 = getr regs 1 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st [bs]) ->
  src_rd W memc s bs ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fpostWmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W
       mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st [bs]))%nat rp_H0 hist' S')).
Proof.
intros most own lo rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf st s bs
  memc mdc regsc HSTK HSTKp Hlo HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEP
  HAP Hrac H10 H11 H12 Hcut Hch0 Hev Hsrc Hhome Hwmax Hhead Hcons Hlive HMN.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ (lo <= a < spZ regs)) by (intros a Ha; lia).
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (lo <= a < spZ regs)) by (intros a Ha; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < spZ regs)) by (intros a Ha; split; lia).
assert (Hsp : spZ regsc = spZ regs)
  by (unfold spZ; f_equal; exact (HAP 2 ltac:(unfold acallee_saved; lia))).
assert (Hgpc : getr regsc 3 = w64 (as_gp B))
  by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regsc 4 = w64 (as_tp B))
  by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hs0c : s0Z regsc = s0Z regs)
  by (unfold s0Z; f_equal; exact (HAP 8 ltac:(unfold acallee_saved; lia))).
assert (HFOOT : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ (lo <= x < spZ regs)).
{ intros x Hx.
  destruct (wv_foot_wr ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf v D
    HSTK HPREx HLED HLOC HD x Hx) as (A1 & A2 & _).
  pose proof (wv_foot_low ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf
    v D HPREx HLED HLOC HD x Hx) as A3.
  split; [exact A1|]. split; [exact A2|]. lia. }
assert (HNODEc : pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D).
{ apply (wv_nodeR_keep W W mem memc Lam v t D HNODE).
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & A2 & _). split; assumption.
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & _ & A3). apply HKEEP; assumption. }
assert (HOUTc : prhWriter_out W memc Lam o buf st)
  by (eapply (wv_out_keep ly S Hp W W mem memc md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran o buf st
        (fun a => lo <= a < spZ regs)); [exact HAR | exact HLED | exact HOUT | exact HKEEP | exact HLOW | exact HOFF]).
assert (HLEDc : prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own)
  by (eapply (wv_led_keep ly S Hp W md mem memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran
        (fun a => lo <= a < spZ regs)); [exact HAR | exact HLED | exact HKEEP | exact HLOW8]).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc))
  by (apply (wv_arodata_keep W W mem memc (fun a => lo <= a < spZ regs)); [exact HRO | exact HKEEP | exact HLOW]).
assert (HCHc : achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch).
{ rewrite Hs0c. apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hchain);
    [lia | lia |]. intros a Ha. apply HKEEP; lia. }
exact (wv_tail_put rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran buf
  st s bs memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODEc HLOC HD Hoff HJ
  ltac:(intros a Ha; apply HKEEP; lia)
  HAP Hsp Hrac Hgpc Htpc HCHc HROc H10 H11 H12 Hcut Hch0 HOUTc HLEDc Hev Hsrc Hhome Hwmax Hhead Hcons Hlive HMN).
Qed.



Lemma wv_leaf_num : forall {most own : Z} txt bits,
  forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) D Lam peak ran STKv,
  184 + STK_RT_STR <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prh_run_at rp_sm rp_x rp_os rp_i
    (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v (PjTree.JNum txt bits) D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep))) + 1
    <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep))) ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_write_value) regs mem md)
    (fpostWFmR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp
       W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
          room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v (PjTree.JNum txt bits) D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st
            (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)%Z) dep)))%nat
            rp_H0 hist' S')).
Proof.
intros most own txt bits rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch o v pretty dep d buf st D Lam peak ran
  STKv HSTK HSTKp HPRE Hroom Hrp Hos4 Hcl H10 H11 H12 H13 Hcut Hch0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HTV HD Hoff
  Hwmax Hhead Hcons Hlive.
(* no float instruction runs: the m-form post at the entry float state fx is the float m-form, by fpre's frm_zero *)
eapply SRr'_mono; cycle 1.
{ intros W' c' _ HP. exact (wv_postWF_of_W fx fx _ _ _ _ _ _ _ _ _ _ _ W' c'
    (proj2 (proj2 (proj2 (proj2 HPRE)))) (wv_fk_refl fx) HP). }
(* the leaf crosses no free before its tail call (strlen frees nothing): it runs at SRr up to put's entry *)
apply wv_srr_pre.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTR : STK_RT_STR = 2 * ESTACK) by reflexivity.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
assert (HLOWS : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wrS (spZ regs) a) by (intros a Ha; unfold wv_wrS; lia).
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (PLAWI : srr_inv_laws SEGS (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m))
  by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
assert (HPM : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem) by (cbv beta; exact (fun h => h)).
pose proof HNODE as HNODE0.
destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
  (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap)).
destruct Hbody as (_ & _ & _ & _ & _ & k & Hcs & ->).
pose proof Hcs as (Hlam & Hlen & Hlen32 & Hrng & Hgs). unfold prh_lin in Hlam.
destruct (wv_lam_low ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran str k HAR HLED Hlam)
  as (Hs4096 & Hk0 & Hsk).
pose proof (proj1 (proj2 (proj2 (HTV str k (or_introl eq_refl))))) as Hgap1.
destruct (HJT 3%nat ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro).
change (4 * Z.of_nat 3) with (4 * 3) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro.
assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * 3) 4 (WV_JTW (Z.to_nat 3)))
  by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
      intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
      split; [exact R1 | split; [exact R2 | exact R3]]).
assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * 3 + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * 3)
  by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * 3) 4 v 56 ltac:(lia) ltac:(lia)
        ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]).
destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep 3 str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
  Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
  Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
  HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat 3))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 3)))) k)
  by (intros k0 Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 3)))) E)
  by (split; [intros k0 Hk; apply EL; unfold A_TEXT; lia | reflexivity]).
assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by (intros; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value)).
(* entry -> the switch's jr *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS HJ SHOK HPM WV_Bspan;
[ eapply (wv_awr E 3 _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ].
wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
prreg HS (11%bv : bv 5) R11.
assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat 3)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
destruct (wv_jr_target E (Z.to_nat 3) E38 EJ HTr) as (Ht & Hr & He).
eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case 3) HS);
[ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ].
intros mat1 ms1 Hms1 HS1. subst ms1.
pose proof (wv_pi_at E _ (AF_wv_case 3) _ HS1) as HS2. clear HS1.
assert (HJ2 := HJ).
eapply (ajournal_x_materialize (SK := SK)) with (X := mat1) in HJ2;
[| first [exact LAWS | exact pa_segs_low | idtac] ..].
clear HJ.
(* the case: the shadow check of v + 16, `ld s1, 16(v)` and the stop at `bnez s1` *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
psrr_branch_tok (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) BR HS2 SHOK WV_Bspan.
2:{ (* the text pointer = 0: refuted, a ledger block's user pointer is at least 4096 *)
  exfalso.
  rewrite ?branch_ne_U, ?branch_eq_U, (U_atom E 34 str E34 Rstr), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hs0 : (str =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hs0' : (0 =? str) = false) by (apply Z.eqb_neq; lia).
  rewrite ?Hs0, ?Hs0' in Hc. cbn in Hc. discriminate Hc. }
(* the text pointer <> 0: a0 = s1, the strlen call (write_value + 4 * 116) *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K2 K3 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
pmkst HS2.
prreg HS2 (10%bv : bv 5) Ra0. prreg HS2 (2%bv : bv 5) Rsp1. prreg HS2 (1%bv : bv 5) Rra1.
prreg HS2 (3%bv : bv 5) Rgp1. prreg HS2 (4%bv : bv 5) Rtp1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HspT : spZ rT = spZ regs - 176)
    by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
  (* the text at the call memory: the tree's block (str, k), kept below alloc_ceiling *)
  assert (HTVT : prhWriter_tree_vis W mT [(str, k)])
    by (exact (wv_tree_vis_keep W W mem mT [(str, k)] (wv_wr (spZ regs)) HTV K3 HLOW));
  destruct (HTVT str k (or_introl eq_refl)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7);
  assert (HgsT : garr8 SEGS (mrestrict (w_H W) mT) str (txt ++ [0]))
    by (apply (wv_garr8_keep (w_H W) (w_H W) mem mT str (txt ++ [0])); [|exact Hgs];
        intros j Hj; rewrite length_app in Hj; cbn [length] in Hj; apply K3; [lia | unfold wv_wr; lia]);
  pose proof (wv_cstr_blk ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran W mT
    str k txt HAR HLED Hlam Hlen Hlen32 Hrng HgsT Hgap1 T5 T6 T7) as HcsT;
  assert (HROT : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mT))
    by (apply (wv_arodata_keep W W mem mT (wv_wr (spZ regs))); [exact HRO | exact K3 | exact HLOW])
end.
pose proof HcsT as (HcT & _ & _ & _ & HamT & HraT & HhT & HtT).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (YGcallMxmn.aj_strlen_at_xrom (SK := SK) SEGS B (@prh_pst prh_img_A) ARx pa_relro_lo pa_relro_hi LAWS
    pa_segs_low (SIGMA AS___wrap_strlen) (STRLEN fx) W rT mT (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp dT 0 str (Z.of_nat (length txt))
    (- (d + 176)) _ HJ2) end.
  - rewrite Ra0, E34. reflexivity.
  - lia.
  - lia.
  - exact Hlen32.
  - lia.
  - rewrite HspT. lia.
  - apply wv_neg_mod16. rewrite Z.add_mod, Hd16 by lia. reflexivity.
  - lia.
  - lia.
  - rewrite Rgp1, E3. exact Hgp.
  - rewrite Rtp1, E4. exact Htp.
  - exact Rra1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact (wv_first_byte W _ str txt HcT).
  - replace (Z.of_nat (length txt) + 1) with (Z.of_nat (length (txt ++ [0])))
      by (rewrite length_app; cbn [length]; lia).
    apply (wv_src_ok W _ _ str (txt ++ [0]) (proj1 HcT)).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HspT. lia.
  - intros a Ha. lia.
  - exact HamT.
  - exact HraT.
  - exact HhT.
  - exact HtT.
  - exact HROT. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ3 & HP2 & Hlen2 & Hfr2 & Hpres2 & Hmn2).
pose proof (ajx_pres HJ3) as Hpres3.
jafter_call_keep_pi HS2 39%nat regs2 (mrestrict (w_H W) mem2) HP2 [1]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; lia.
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply Hpres3. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 39 (map (getr regs2) CLOB)) as E1' eqn:HE1 in HSX.
assert (HIM1 : img_env VAL A_LIM E1') by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 39)%nat -> ew E1' n = ew E n) by (intros n0 Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (E1a0 : ew E1' 43 = w64 (Z.of_nat (length txt))) by (rewrite HE1, <- Hlen2; reflexivity).
assert (HAE1 : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 3)))) E1')
  by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1' 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp).
assert (SHOK1 : sh_ok SEGS WV_Bx [] E1' (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
assert (HPM1 : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem2)
  by (cbv beta; intros h; exact (Hmn2 (HPM h))).
assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wrS (spZ regs) a ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. unfold wv_wrS in Hn. rewrite (Hfr2 a Ha ltac:(lia)). apply K3; [exact Ha | unfold wv_wr; lia]. }
(* after the call: a2 = len, a0 = s0, a1 = s1, the epilogue, and the tail `j put` (write_value + 4 * 236) *)
paj_run_to_tok_x_inv (@paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HSX HJ3 SHOK1 HPM1 WV_Bspan
  (AF_write_value + 4 * 236);
[ wv_awr_tac Usp1 d | ].
wv_keep_runS HFr KX K4 mem (wv_wrS (spZ regs)) Usp1. clear HF HFr HG.
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HSX HJ3 SHOK1 HPM1 WV_Bspan;
[ wv_awr_tac Usp1 d | ].
wv_keep_runS HFr K4 K5 mem (wv_wrS (spZ regs)) Usp1. clear HF HFr HG.
prreg HSX (10%bv : bv 5) Rb0. prreg HSX (11%bv : bv 5) Rb1. prreg HSX (12%bv : bv 5) Rb2.
prreg HSX (1%bv : bv 5) Rbra.
lazymatch type of HSX with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HAP : aregs_preserved regs (ms_regs msx))
    by (eapply (aregs_preserved_of_st_ok SEGS (w_H W) E1' _ _ regs _); [exact HSX | exact HAE1 | vm_compute; reflexivity]);
  assert (Rrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rbra, OLD1, E1 by (cbv; lia); reflexivity);
  assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Rb0, OLD1, E10 by (cbv; lia); exact H10);
  assert (H11c : getr (ms_regs msx) 11 = w64 str) by (rewrite Rb1, OLD1, E34 by (cbv; lia); reflexivity);
  assert (H12c : getr (ms_regs msx) 12 = w64 (Z.of_nat (length txt))) by (rewrite Rb2; exact E1a0);
  (* the text at the put's memory *)
  assert (HTVc : prhWriter_tree_vis W (ms_mem msx) [(str, k)])
    by (exact (wv_tree_vis_keep W W mem (ms_mem msx) [(str, k)] (wv_wrS (spZ regs)) HTV K5 HLOWS));
  destruct (HTVc str k (or_introl eq_refl)) as (U1 & U2 & U3 & U4 & U5 & U6 & U7);
  assert (Hgsc : garr8 SEGS (mrestrict (w_H W) (ms_mem msx)) str (txt ++ [0]))
    by (apply (wv_garr8_keep (w_H W) (w_H W) mem (ms_mem msx) str (txt ++ [0])); [|exact Hgs];
        intros j Hj; rewrite length_app in Hj; cbn [length] in Hj; apply K5; [lia | unfold wv_wrS; lia]);
  pose proof (wv_src_of_cstr W (ms_mem msx) str txt
    (wv_cstr_blk ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran W (ms_mem msx)
       str k txt HAR HLED Hlam Hlen Hlen32 Hrng Hgsc Hgap1 U5 U6 U7)) as Hsrc;
  assert (Hhome : prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) str (Z.of_nat (length txt)))
    by (split; [left; left; exists str, k; split; [exact Hlam | lia]
               | exact (wv_blk_apart ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran str k
                   buf (WriterApp.w_cap st) (Z.of_nat (length txt)) HAR HLED Hlam
                   (proj2 (HD str k (or_introl eq_refl))) Hbufin ltac:(lia) ltac:(lia))]);
  assert (Hwmax' : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length txt) + 1 <= prhWriter_WMAX)
    by (cbn [WriterValue.wvpieces concat] in Hwmax; rewrite app_nil_r in Hwmax; exact Hwmax);
  assert (Hch0c : spZ regs + 16 <= o ->
      exists ra, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 8) = Some ra /\
        exists nfp, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
    by (intros Hge; apply (wv_reca_keep (aview SEGS (w_H W) mem)); [| exact (Hch0 Hge)];
        intros a Ha; apply K5; [lia | unfold wv_wrS; lia]);
  pmkst HSX; apply SRr_ret;
  exact (wv_put_close_x (spZ regs - 176 - STK_RT_STR) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch
    STKv d o v _ _ Lam peak ran buf st str txt (ms_mem msx) _ (ms_regs msx) ltac:(lia) HSTKp ltac:(lia) HPRE Hroom
    Hrp Hos4 Hcl HWIN Ho1 Ho2 HLED HOUT HNODE0 HLOC HD Hoff HJ3 K5 HAP Rrac H10c H11c H12c Hcut Hch0c Hev Hsrc Hhome Hwmax'
    Hhead Hcons Hlive HPM1)
end.
Qed.


End c1.

(* ======== THE CONTAINER (case 36: an array, tag 5, or an object, tag 6) ======== *)
(* The batch kit (a working branch 44123abafeb7, kept by the cut 7cdbb61b5fa0) dropped src_rd's / cstr_ok's `+ 8` (PRH_Base.v ef7c8ca98529 :1603,
   :1660 at the cut), so the interim text's named argument wv_gap (SRC-CEIL) is DELETED: the string / number leaves and each
   object key take the ceiling bound of their block from tree_vis_cf's granule end (wv_cstr_blk).
   S0 is the kit's premise (`s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling` in twrite_value_specX and tput_string_specX):
   the closing bracket's tail put needs a chain from the entry s0 at the tail memory (s0 below the ceiling: achain's
   first arm; s0 = o: wv_chain1g on form (a)'s words); wv_s0 is its name here. The inner calls' chain from o is the kit's
   case 1 (form (a)): case 1 by keeping [o - 16, o) (wv_reca_keep), case 2 by the saved ra at o - 16 = R + 168 and the
   caller word at sp (wv_chain1g). *)
Definition wv_s0 (regs : bvmap 5 word) (o : Z) : Prop := s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling.

Section tx. Context {fx : YK11.FPState}.
(* THE TEXT: the batch kit's twrite_value_specX (PRH_FnWriter.v d89d3c67b78c) verbatim, at the ENTRY float state fx (this
   Section's), so the self call takes it at the caller's current float state *)
Definition twrite_value_specI (n : nat) : Prop :=
  twrite_value_specX (fx := fx) (PI := prh_img_A) (PA := PA) B ARx SK CTX0 n.
End tx.

(* the container's entry data: the kit's arguments, named; y_fx the ENTRY float state (the final post is the text's float
   form at it, the internal file REFIT-WRITER.md's float-threading design point 1), y_most / y_own the ledger's #102 cells *)
Record wvx := mkWVX {
  y_d : Z; y_STK : Z; y_ly : alayout; y_S : astate; y_Hp : list Z; y_W : world SEGS; y_regs : bvmap 5 word;
  y_mem : word -> option byte; y_md : Model; y_o : Z; y_v : Z; y_pretty : Z; y_dep : Z; y_buf : Z;
  y_st : WriterApp.wst; y_t : PjTree.jv; y_D : list (Z * Z); y_Lam : list (Z * Z); y_peak : Z; y_ran : Z;
  y_rpsm : list Z -> Z * Z; y_rpx : list Z; y_rpos : list (option nat * option nat * option nat); y_rpi : nat;
  y_rpH0 : list Z; y_rphist : list YG00.chunk; y_fx : YK11.FPState; y_most : Z; y_own : Z }.
Definition y_sp (X : wvx) : Z := spZ (y_regs X).
Definition y_p (X : wvx) : bool := negb (y_pretty X =? 0).
Definition y_FP (X : wvx) : list (Z * Z) := prhWriter_cfp (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)).
(* the number of items, the tag, the pieces of the opening bracket and the first i items *)
Definition wv_nitems (t : PjTree.jv) : nat :=
  match t with PjTree.JArr l => length l | PjTree.JObj l => length l | _ => 0 end.
Definition wv_tagc (t : PjTree.jv) : Z := match t with PjTree.JObj _ => 6 | _ => 5 end.
Definition wv_done (X : wvx) (i : nat) : list (list Z) :=
  match y_t X with
  | PjTree.JArr l => [91] :: wv_arr_go (y_p X) (y_dep X) 0 (firstn i l)
  | PjTree.JObj l => [123] :: wv_obj_go (y_p X) (y_dep X) 0 (firstn i l)
  | _ => []
  end.
(* the separator literal's slot (": " when pretty, ":" otherwise) *)
Definition wv_sep_slot (X : wvx) : nat := if y_pretty X =? 0 then 130%nat else 59%nat.

Section cont.
(* the runner's memory invariant, ABSTRACT in every segment (WalkS4's measurement); wv_specI instantiates it once *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

(* the container's final post: the kit's float post fpostWF AT THE ENTRY FLOAT STATE y_fx X at the text's inner Q, with Pm at
   the final memory *)
Definition wv_Qin (X : wvx) :=
  fun ly' S' Hp' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
    room_live_cf S' /\
    pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X) /\
    exists ok, prhWriter_ret_ok B ok (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_ran X) (y_most X) (y_own X) (y_o X) (y_buf X) (y_st X)
      (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X)) ly' S' Hp' W' regs' mem' md' /\
    prh_granted ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X))
      (prhWriter_k ok (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))) /\
    exists hist', PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X)
      (y_rpi X + length (prhWriter_evs ok (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))))%nat
      (y_rpH0 X) hist' S'.
(* every container run crosses its puts' reallocs: its final post's journal is at wle' (restated in place) *)
Definition wv_Qfin (X : wvx) : world SEGS -> config -> Prop :=
  fun W' c' =>
    fpostWFR (fx := y_fx X) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) (y_STK X) (y_d X) (y_FP X) (y_regs X) (y_ly X)
      (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X)
      (wv_Qin X) W' c' /\ Pm (ms_mem (cfg_ms c')).

Section jd. Context {fx : YK11.FPState}.
(* the text's premises at the container's entry (t an array or an object), with Pm at entry; the batch kit's prh_cons_from
   sits in the slot of the deleted wv_gap and prh_live_evs in the slot of the old LIVE_write_value sum; the text's
   run-length bound `length rp_os <= 4` is the last conjunct (wv_pre_os4 reads it) *)
Definition wv_pre (X : wvx) (ch : list (Z * Z * Z)) : Prop :=
  fpre B ARx (y_STK X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X) ch /\
  room_live_cf (y_S X) /\
  PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X) (y_rpH0 X) (y_rphist X) (y_S X) /\
  prh_univ_closure B CTX0 /\
  getr (y_regs X) 10 = w64 (y_o X) /\ getr (y_regs X) 11 = w64 (y_v X) /\
  getr (y_regs X) 12 = w64 (y_pretty X) /\ getr (y_regs X) 13 = w64 (y_dep X) /\
  0 <= y_pretty X < 2 ^ 64 /\ 0 <= y_dep X < 2 ^ 31 /\ y_dep X + Z.of_nat (PjTree.depth (y_t X)) <= 2 ^ 31 - 1 /\
  (y_sp X + 16 <= y_o X \/ y_o X = y_sp X + 8) /\
  fwin (y_ly X) (y_W X) (y_regs X) (y_mem X) (y_d X) /\ y_sp X <= y_o X /\ y_o X + 32 <= y_sp X + y_d X /\
  prhWriter_out (y_W X) (y_mem X) (y_Lam X) (y_o X) (y_buf X) (y_st X) /\
  prh_ledger B (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_Lam X) (y_peak X)
    (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (y_ran X) (y_most X) (y_own X) /\
  pj_nodeR SEGS (mrestrict (w_H (y_W X)) (y_mem X)) (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X) /\
  ((y_sp X <= y_v X /\ y_v X + 56 <= ly_stk_hi (y_ly X)) \/
   (exists x z, In (x, z) (y_Lam X) /\ x <> y_buf X /\ x <= y_v X /\ y_v X + 56 <= x + z) \/
   prhWriter_in_frame (y_ly X) (y_S X) (y_v X)) /\
  range_addressable (aview SEGS (w_H (y_W X)) (y_mem X)) SHADOW_OFF (y_v X) 56 /\
  prhWriter_tree_vis (y_W X) (y_mem X) (y_D X) /\
  (forall a k, In (a, k) (y_D X) -> In (a, k) (y_Lam X) /\ a <> y_buf X) /\
  (forall x, y_o X <= x < y_o X + 32 -> ~ pj_footR (y_v X) (y_D X) x) /\
  Z.of_nat (length (frames (y_S X))) < fs_frames 0 /\
  Z.of_nat (length (WriterApp.w_text (y_st X))) +
    Z.of_nat (length (concat (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X)))) + 1 <= prhWriter_WMAX /\
  prhWriter_WMAX + cf_head < cf_malloc_max /\
  prh_live_evs (y_S X) (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))) /\
  Pm (y_mem X) /\
  PRH_Base.prh_cons_from (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (length (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X)))) /\
  wv_s0 (y_regs X) (y_o X) /\
  (y_sp X + 16 <= y_o X ->
     exists ra, rdword (aview SEGS (w_H (y_W X)) (y_mem X)) (y_o X - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H (y_W X)) (y_mem X)) (y_o X - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) /\
  prh_run_at (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))) /\
  (* the entry float state is the record's *)
  y_fx X = fx /\
  (* the run has at most 4 calls: the inner put / indent / put_string / write_value calls take it *)
  (length (y_rpos X) <= 4)%nat.

Lemma wv_pre_os4 : forall X ch, wv_pre X ch -> (length (y_rpos X) <= 4)%nat.
Proof. intros X ch H. unfold wv_pre in H. do 33 (destruct H as [_ H]). exact H. Qed.

(* what every join of the container carries about the current state (lyc Sc Hpc Wc memc mdc kc) after the pieces P:
   the journal from the entry (own list empty), the caller window kept off FP, Pm, the writer after P (opened, the
   model-run position at the EXACT advance y_rpi X + length (prhWriter_evs ok (y_st X) P) at its end), the room, the
   read-only view, and the CURRENT float state's relation to the entry's (frm_zero, fs0-fs11 kept from y_fx X). The
   tree, v's shadow and the tree's visibility at memc follow from the journal (wv_foot_keep, wv_ra_cur, wv_tvis_cur). *)
Definition wv_common (X : wvx) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS) (memc : word -> option byte)
  mdc kc : Prop :=
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (y_STK X + y_d X)
    (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc /\
  (forall a, y_sp X <= a < y_sp X + y_d X -> ~ inFP (y_FP X) a ->
     aview SEGS (w_H Wc) memc a = aview SEGS (w_H (y_W X)) (y_mem X) a) /\
  Pm memc /\
  (exists ok ranc bufc Lamc peakc,
     prh_oks ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P)
       (prhWriter_reqs ok (y_st X) P) (y_most X) (y_ran X) ranc /\
     prh_granted ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) /\
     prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) /\
     prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
       (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) /\
     prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
       (prhWriter_putN ok (y_st X) P) /\
     exists rp_hist', PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X)
       (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat (y_rpH0 X) rp_hist' Sc) /\
  room_live_cf Sc /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
  (* the CURRENT float state fx: rounding mode 0, fs0-fs11 those of the entry (the float-threading design point 2) *)
  YK0o.frm_zero (@YK11.fp_csr fx) /\ fregs_kept_x (y_fx X) fx.

(* THE LOOP HEAD (A 0x86ef0, write_value + 4 * 153): item i is next (i < n), P = the opening bracket and the first i
   items' pieces; the registers and the own frame's words (R = the entry sp - 176) as the engine measured them *)
Definition wv_head (X : wvx) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word)
  (memc : word -> option byte) mdc kc : Prop :=
  let R := y_sp X - 176 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  wv_common X P lyc Sc Hpc Wc memc mdc kc /\
  (i < wv_nitems (y_t X))%nat /\ P = wv_done X i /\
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\ getr regsc 18 = w64 (SHADOW_OFF + (v + 40) / 8) /\
  getr regsc 19 = w64 (y_pretty X) /\ getr regsc 20 = w64 (v + 40) /\ getr regsc 21 = w64 (Z.of_nat i) /\
  getr regsc 22 = w64 (8 * Z.of_nat i) /\ getr regsc 23 = w64 (v + 24) /\ getr regsc 24 = w64 (y_dep X + 1) /\
  getr regsc 25 = w64 (56 * Z.of_nat i) /\ getr regsc 26 = w64 (SHADOW_OFF + (v + 24) / 8) /\
  getr regsc 27 = w64 (SHADOW_OFF + v / 8) /\
  rdword rd (R + 8) = Some 3 /\ rdword rd (R + 16) = Some (y_dep X) /\
  rdword rd (R + 24) = Some (SHADOW_OFF + (v + 32) / 8) /\
  rdword rd (R + 32) = Some (if y_pretty X =? 0 then 1 else 2) /\
  rdword rd (R + 40) = Some (WV_STR (wv_sep_slot X)) /\ rdword rd (R + 48) = Some (v + 32) /\
  rdword rd (R + 56) = Some (WV_STR 151) /\ rdword rd (R + 64) = Some SHADOW_OFF /\
  rdword rd (R + 72) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 80) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 1)).
End jd.

Section c2. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.
Let RUNTOI := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.

(* a tail call's m-form post at the CURRENT float state fx (the callee's own keep from the call memory memc, as
   wv_tail_gen concludes) gives the container's Pm form in the FLOAT form at the entry float state fx0, by PCALL: the
   callee kept fx, whose rounding mode is 0 and whose fs0-fs11 are fx0's *)
Lemma wv_post_P : forall (fx0 : YK11.FPState) (W : world SEGS) c STKv d FP regs ly S Hp (W0 : world SEGS) mem md memc
  (Qin : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  YK0o.frm_zero (@YK11.fp_csr fx) -> fregs_kept_x fx0 fx ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (fpostWR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d FP regs ly S Hp
    W0 mem md
    (fun ly' S' Hp' W' regs' mem' md' =>
       Qin ly' S' Hp' W' regs' mem' md' /\ (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem'))) ->
  Pm memc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (fun W' c' =>
    fpostWFR (fx := fx0) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) STKv d FP regs ly S Hp W0 mem md Qin W' c' /\
    Pm (ms_mem (cfg_ms c'))).
Proof.
intros fx0 W c STKv d FP regs ly S Hp W0 mem md memc Qin HZ HKF H HPm.
eapply SRr'_mono; [exact H|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HK2 & HP2 & HQ & HKm).
split; [exists fx, ly2, S2, Hp2, regs2, mem2, md2, k1; split; [exact Hc2|]; split; [exact HZ|]; split; [exact HKF|];
        split; [exact HJ2|]; split; [exact HK2|]; split; [exact HP2 | exact HQ]|].
subst c2. change (Pm mem2). exact (PCALL memc mem2 HKm HPm).
Qed.

(* ---- CONTRACT (the #102 float form; the proofs land below):
   wv_cont   : (at the Section's float state fx = y_fx X, wv_pre's y_fx conjunct) forall n' X ch,
               (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
               STK_write_value (S n') <= y_STK X -> wv_pre X ch ->
               (forall i P lyc Sc Hpc Wc regsc memc mdc kc, wv_head X i P lyc Sc Hpc Wc regsc memc mdc kc ->
                  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
                    (wv_Qfin X)) ->
               SRr' SEGS RZ_cf (y_W X) (cfg_at SEGS (SIGMA AS_write_value) (y_regs X) (y_mem X) (y_md X))
                 (wv_Qfin X).
   wv_loop   : forall n' X ch, (forall fx0, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
               (PjTree.depth (y_t X) <= S n')%nat -> wv_pre (fx := y_fx X) X ch ->
               forall fxc i P lyc Sc Hpc Wc regsc memc mdc kc, wv_head (fx := fxc) X i P lyc Sc Hpc Wc regsc memc mdc kc ->
               SRr' SEGS RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
                 (wv_Qfin X).
   ---- *)

(* ---- THE CONTAINER PREFIX (wv_cont): from the entry to the loop head, or to the empty container's closing
   bracket. Helpers (prefix wvp_). ---- *)

(* the stack the container's own steps need: its frame and the opening bracket's put below it *)
Lemma wvp_stk : forall n', 184 <= STK_write_value (S n') /\ STK_put + 176 <= STK_write_value (S n').
Proof.
intros n'. unfold STK_write_value.
assert (Hp : 0 <= STK_put) by (vm_compute; congruence).
assert (Hn : 2 <= Z.of_nat (S (S n'))) by lia.
lazymatch goal with |- context [Z.of_nat (S (S n')) * ?f + ?z] =>
  assert (Hf : 176 <= f) by (vm_compute; congruence);
  assert (Hz : STK_put <= z) by (vm_compute; congruence);
  set (ff := f) in *; set (zz := z) in *
end.
set (m := Z.of_nat (S (S n'))) in *. clearbody ff zz m. nia.
Qed.

(* a word the memory holds as val_mem is the word rdword reads (YGcallSnpCk.v's snp_rdword_of_val_mem, the same
   proof; that file is not Required here) *)
Lemma wvp_rdword_of_val_mem0 : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> rdword (aview SEGS H mem) a = Some (v mod 2 ^ 64).
Proof.
intros H mem a v Hv. set (u := v mod 2 ^ 64).
assert (Hu : 0 <= u < 2 ^ 64) by (unfold u; apply Z.mod_pos_bound; lia).
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte u 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold u, YO0f.le_byte, YG0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite !Z.mod_mod by lia. reflexivity. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hu.
Qed.

Lemma wvp_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  0 <= v < 2 ^ 64 -> val_mem SEGS (mrestrict H mem) a 8 v -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv0 Hv. rewrite (wvp_rdword_of_val_mem0 H mem a v Hv). f_equal. apply Z.mod_small. exact Hv0.
Qed.

(* a word chunk of a region of the engine's state, read off the memory (the region's base an atom b) *)
Lemma wvp_chunk_rdb : forall (H : word -> bool) E ss ms i (b : nat) lo hi wlo whi cs off e v base a,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some b) lo hi wlo whi cs) ->
  bv_unsigned (ew E b) = base -> a = base + off ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H (ms_mem ms)) a = Some v.
Proof.
intros H E ss ms i b lo hi wlo whi cs off e v base a HS Hi Hb Ha Hc He Hv.
pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
cbn [YP09.r_chunks YP09.r_base base_val] in Hcs.
subst a. apply wvp_rdword_of_val_mem; [exact Hv|].
pose proof (val_of_chunk_ok SEGS E _ _ off 8%N e v (proj1 (Forall_forall _ _) Hcs _ Hc) He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as X.
rewrite Hb in X. exact X.
Qed.

Lemma wvp_chunk_rdp : forall (H : word -> bool) E ss ms i (b : nat) lo hi wlo whi cs off e v base a,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some b) lo hi wlo whi cs) ->
  bv_unsigned (ew E b) = base -> a = base + off ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H (ms_mem ms)) a = Some v.
Proof.
intros H E ss ms i b lo hi wlo whi cs off e v base a HS Hi.
exact (wvp_chunk_rdb H E (abs_ss VAL ss) ms i b lo hi wlo whi cs off e v base a HS Hi).
Qed.

(* eight visible bytes form a word *)
Lemma wvp_rdword_some : forall (rd : Z -> option Z) a, (forall j, 0 <= j < 8 -> rd (a + j) <> None) ->
  exists w, rdword rd a = Some w.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
pose proof (H 1 ltac:(lia)) as E1. pose proof (H 2 ltac:(lia)) as E2. pose proof (H 3 ltac:(lia)) as E3.
pose proof (H 4 ltac:(lia)) as E4. pose proof (H 5 ltac:(lia)) as E5. pose proof (H 6 ltac:(lia)) as E6.
pose proof (H 7 ltac:(lia)) as E7.
destruct (rd a) as [b0|]; [|exfalso; exact (E0 eq_refl)].
destruct (rd (a + 1)) as [b1|]; [|exfalso; exact (E1 eq_refl)].
destruct (rd (a + 2)) as [b2|]; [|exfalso; exact (E2 eq_refl)].
destruct (rd (a + 3)) as [b3|]; [|exfalso; exact (E3 eq_refl)].
destruct (rd (a + 4)) as [b4|]; [|exfalso; exact (E4 eq_refl)].
destruct (rd (a + 5)) as [b5|]; [|exfalso; exact (E5 eq_refl)].
destruct (rd (a + 6)) as [b6|]; [|exfalso; exact (E6 eq_refl)].
destruct (rd (a + 7)) as [b7|]; [|exfalso; exact (E7 eq_refl)].
eexists. reflexivity.
Qed.

(* a byte at or above the ceiling and below the struct is outside the caller footprint (the buffer is a block, below
   the ceiling) *)
Lemma wvp_nfp : forall ly S Hp W mem md o buf cap a,
  ARx ly S Hp W mem md -> (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  YM05.alloc_ceiling <= a -> a < o -> ~ inFP (prhWriter_cfp o buf cap) a.
Proof.
intros ly S Hp W mem md o buf cap a HAR Hbb Ha Hao Hf.
unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hs | Hb]; [lia|].
unfold prhWriter_fp in Hb. destruct (Z.eqb_spec cap 0) as [_|Hc]; [exact (inFP_nil a Hb)|].
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR (Hbb Hc)) as (_ & _ & Hce & _).
unfold ablocks_fp in Hb. cbn [map] in Hb. destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
Qed.

(* a chain from v whose first record word below v is below the ceiling reads only [v - 16, v): it survives any change
   that keeps those bytes (the second record would start at that word, and bad_next stops the walk there) *)
Lemma wvp_achain_keep16 : forall ly ly' (rd rd' : Z -> option Z) sp v ch,
  achain ly rd sp v ch -> ly_top ly' = ly_top ly -> YM05.alloc_ceiling <= sp ->
  (sp + 16 <= v -> forall a, v - 16 <= a < v -> rd' a = rd a) ->
  (sp + 16 <= v -> forall nfp, rdword rd (v - 16) = Some nfp -> nfp < YM05.alloc_ceiling) ->
  achain ly' rd' sp v ch.
Proof.
intros ly ly' rd rd' sp v ch Hc Etop Hsp Hk Hn.
unfold achain in *. rewrite Etop.
destruct Hc as [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H|].
right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
destruct ch as [|[[fp ra] nfp] rest]; cbn [fpchain] in H4 |- *.
- destruct H4 as (r & Hr & Hr4). exists r. split; [|exact Hr4].
  rewrite (wv_rdword_ext rd rd') by (intros j Hj; apply Hk; [exact H1 | lia]). exact Hr.
- destruct H4 as (-> & Hal & Hra & Hnfp & H4096 & Hrest). split; [reflexivity|]. split; [exact Hal|].
  split; [rewrite (wv_rdword_ext rd rd') by (intros j Hj; apply Hk; [exact H1 | lia]); exact Hra|].
  split; [rewrite (wv_rdword_ext rd rd') by (intros j Hj; apply Hk; [exact H1 | lia]); exact Hnfp|].
  split; [exact H4096|].
  pose proof (Hn H1 nfp Hnfp) as Hlt.
  assert (Hb : bad_next v (ly_top ly) nfp = true)
    by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
  rewrite Hb in Hrest |- *. exact Hrest.
Qed.

(* the engine's terms at the head, read as values *)
Lemma wvp_den_off : forall E k c x, ew E k = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff k c) = w64 (x + c).
Proof. intros E k c x Hk Hx Hxc. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hx. reflexivity. Qed.

Lemma wvp_den_sh : forall E k c x, ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0)) = w64 (SHADOW_OFF + (x + c) / 8).
Proof.
intros E k c x Hk H32 Hx Hxc. pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
cbn [sv_denot]. rewrite Hk, H32.
rewrite (unsigned_lit_small x) by exact Hx. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite Z.add_0_r.
rewrite zalu64_sound. rewrite zalu64_sound. unfold zalu64, w64. rewrite Z_to_bv64_canon. f_equal.
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite (YP0m.zcanon_small (x + c)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D : 0 <= (x + c) / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (8 * 2 ^ 44) with (2 ^ 47); lia]]. }
rewrite !(YP0m.zcanon_small ((x + c) / 8)) by lia.
rewrite (YP0m.zcanon_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
lia.
Qed.

Lemma wvp_den_pr : forall E p, ew E 12 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 1)) = w64 (if p =? 0 then 1 else 2).
Proof.
intros E p H12 Hp. cbn [sv_denot]. rewrite H12, unsigned_lit_small by exact Hp. rewrite Z.add_0_r.
rewrite zalu64_sound. rewrite zalu64_sound. unfold zalu64, w64. rewrite Z_to_bv64_canon.
cbn [zalu_raw]. rewrite (YP0m.zcanon_small 0) by lia. rewrite (YP0m.zcanon_small p) by lia.
destruct (Z.eqb_spec p 0) as [->|Hp0].
- reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 p)) by lia. reflexivity.
Qed.

Lemma wvp_den_addw : forall E dp, ew E 13 = Z_to_bv 64 dp -> 0 <= dp -> dp + 1 < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SOff 13 0) (SLit 1)) = w64 (dp + 1).
Proof.
intros E dp H13 H0 H1. cbn [sv_denot]. rewrite H13, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite zalu32_sound. unfold zalu32, w64. rewrite Z_to_bv64_canon.
cbn [zalu_raw]. unfold zu32, M32.
rewrite (Z.mod_small dp (2 ^ 32)) by lia. rewrite (Z.mod_small 1 (2 ^ 32)) by lia.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

(* v's shadow entry from v's 56 bytes addressable at the current memory (wv_entry's sh_ok) *)
Lemma wvp_shok : forall (H : word -> bool) mem E v,
  range_addressable (aview SEGS H mem) SHADOW_OFF v 56 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 11 = Z_to_bv 64 v -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  sh_ok SEGS WV_Bx wv_SH E (mrestrict H mem).
Proof.
intros H mem E v Hra E32 E11 Hv0 Hv1 Hband. pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
unfold sh_ok, wv_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS H mem E WV_Bx 11 v 56 v 0 56 Hra).
- unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

End c2.

(* a register of a state at a stop, as the denotation of the engine's term (no normalisation) *)
Ltac wvp_reg HS r :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
      rewrite (st_ok_pi_restrict_reg H E ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      rewrite (st_ok_restrict_reg segs H E ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e
  end.

(* a frame word of the head state (region 0, base atom 2) *)
Ltac wvp_rd HS Usp off :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ _ => eapply (wvp_chunk_rdp _ _ _ _ 0%nat 2%nat _ _ _ _ _ off)
  | st_ok _ _ _ _ => eapply (wvp_chunk_rdb _ _ _ _ 0%nat 2%nat _ _ _ _ _ off)
  end;
  [ exact HS | reflexivity | exact Usp | lia | cbn [In]; repeat (first [left; reflexivity | right]) | | ].

Section c2b. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.
Let RUNTOI := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.
(* the runners after a crossing call: the journal at wle' (YC1fPx's R runners, YSRrG's branch) *)
Let RUNIR := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOIR := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let BRR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).


(* the opening bracket's `jal put` (write_value + 4 * 45) returns to write_value + 4 * 46: below the ceiling (a CLOSED lemma: the slot lookup must
   not run inside the big proof) *)
Lemma wvp_ret46_ceil : bv_unsigned (Z_to_bv 64 (BASE + (AF_write_value + 4 * 46))) < YM05.alloc_ceiling.
Proof.
assert (HA : 0 <= AF_write_value + 4 * 46 < 2 ^ 40) by (split; vm_compute; congruence).
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  (AF_write_value + 4 * 46) HA ltac:(vm_compute; reflexivity)) as H.
rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia). exact H.
Qed.

Lemma wv_cont : forall (n' : nat) (X : wvx) ch,
  (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
  STK_write_value (S n') <= y_STK X -> wv_pre X ch ->
  (forall i P lyc Sc Hpc Wc regsc memc mdc kc, wv_head X i P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
       (wv_Qfin X)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (y_W X) (cfg_at SEGS (SIGMA AS_write_value) (y_regs X) (y_mem X) (y_md X))
    (wv_Qfin X).
Proof.
intros n' X ch Ht HSTKn HPRE0 HLOOP.
pose proof (wvp_stk n') as (HS184 & HSput).
destruct X as [d STKv ly S Hp W regs mem md o v pretty dep buf st t D Lam peak ran rpsm rpx rpos rpi rpH0 rphist
  fx0 most own].
unfold wv_pre, y_sp, y_p, y_FP in *.
cbn [y_d y_STK y_ly y_S y_Hp y_W y_regs y_mem y_md y_o y_v y_pretty y_dep y_buf y_st y_t y_D y_Lam y_peak y_ran
  y_rpsm y_rpx y_rpos y_rpi y_rpH0 y_rphist y_fx y_most y_own] in *.
destruct HPRE0 as (HPRE & Hroom & Hrp & Hcl & H10 & H11 & H12 & H13 & Hpr & Hdep & Hdep2 & Hcut & HWIN & Ho1 & Ho2 &
  HOUT & HLED & HNODE & HLOC & HRA & HTV & HD & Hoff & Hfr0 & Hwmax & Hhead & Hlive & HPm & Hcons & Hs0 & Hrecs & Hev & HFX &
  Hos4).
subst fx0.
assert (HSTK : 184 <= STKv) by lia. assert (HSTKp : STK_put + 176 <= STKv) by lia.
pose proof HPRE as (HPREx & HRO & HTOP1 & HTOP2 & HFRM).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
pose proof cf_head_nonneg as Hh0.
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (Hbufb : WriterApp.w_cap st <> 0 -> In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S)).
{ intros Hc. destruct (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
assert (Hclosed : ~ YI16.sink_open_fp (prhWriter_cfp o buf (WriterApp.w_cap st))).
{ apply wv_cfp_closed; [lia|]. intros Hc.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR (Hbufb Hc)) as (_ & H4096 & _). lia. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ wv_wr (spZ regs) a)
  by (intros a Ha; split; [lia | unfold wv_wr; lia]).
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (HFOOT : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ wv_wr (spZ regs) x)
  by (eapply (wv_foot_wr ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf);
      [lia | exact HPREx | exact HLED | exact HLOC | exact HD]).
(* the .rodata literals the prefix forms are image bytes (HLIT at the entry state) *)
assert (HIMG : forall (k : nat) (bs : list Z), In (k, bs) wv_lits -> (0 < length bs)%nat ->
    0 <= WV_STR k /\ WV_STR k < kLowMemEnd).
{ intros k bs Hin Hl. destruct (HLIT k bs ly S Hp W mem md Hin HAR HRO) as (_ & _ & Hi).
  pose proof (pa_segs_low _ (Hi 0 ltac:(lia))) as X. rewrite Z.add_0_r in X. exact X. }
(* the prefix crosses no free before the opening bracket's put: it runs at SRr up to that call *)
apply wv_srr_pre.
let head ssep bso :=
  idtac;
  pmkst HS3;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] => replace c with WVH_PC by (vm_compute; reflexivity) end;
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst (ms_regs ?msH) _ _ _) ?mdH) _ =>
  lazymatch type of HJc with _ ?kH =>
    apply (HLOOP 0%nat [bso] ly2 S2 Hp2 W2 (ms_regs msH) (ms_mem msH) mdH kH);
    unfold wv_head; cbv zeta;
    unfold wv_common, wv_done, wv_sep_slot, y_sp, y_FP, y_p;
    cbn [y_d y_STK y_ly y_S y_Hp y_W y_regs y_mem y_md y_o y_v y_pretty y_dep y_buf y_st y_t y_D y_Lam y_peak y_ran
      y_rpsm y_rpx y_rpos y_rpi y_rpH0 y_rphist y_fx y_most y_own wv_nitems];
    pose proof (ajxR_ar HJc) as HARH;
    assert (Hdep1 : dep + 1 < 2 ^ 31)
      by (first [cbn [PjTree.depth] in Hdep2; lia | simpl in Hdep2; lia]);
    split;
    [ split; [exact HJc |];
      split; [ intros a Ha Hf; rewrite (K5 a ltac:(lia) ltac:(unfold wv_wr; lia)), (HXT a ltac:(lia) Hf);
               apply K2; [lia | unfold wv_wr; lia] |];
      split; [exact HPM2 |];
      split;
      [ exists ok1, ran1, buf1, Lam1, peak1; split; [exact HOKS1 |]; split; [exact G1 |]; split;
        [ eapply (wv_out_keep ly2 S2 Hp2 W2 W2 mem2 (ms_mem msH) md2 Lam1 peak1 _ _ ran1 o buf1 _ (wv_wr (spZ regs)));
          [exact HAR2 | exact HLED1 | exact HOUT1 | exact K5 | exact HLOW | exact HOFF] |];
        split;
        [ eapply (wv_led_keep ly2 S2 Hp2 W2 md2 mem2 (ms_mem msH) Lam1 peak1 _ _ ran1 (wv_wr (spZ regs)));
          [exact HAR2 | exact HLED1 | exact K5 | exact HLOW8]
        | split; [exact HBLK1 | exists rphist1; exact Hrp1] ] |];
      split; [exact Hroom2 |];
      split; [exact (wv_arodata_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hclosed HRO) |];
      split; [exact HFRM | exact (wv_fk_refl fx)]
    | ];
    split; [lia |];
    split; [reflexivity |];
    (* the registers *)
    split; [ wvp_reg HS3 (2%bv : bv 5);
             rewrite (wvp_den_off EH 2 (-176) (spZ regs));
             [unfold w64; f_equal; lia | rewrite OLD3 by (cbv; lia); exact E2 | lia | lia] |];
    split; [ wvp_reg HS3 (3%bv : bv 5); cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E3, Hgp;
             rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
    split; [ wvp_reg HS3 (4%bv : bv 5); cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E4, Htp;
             rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
    split; [ wvp_reg HS3 (8%bv : bv 5); cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E10, H10;
             rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
    split; [ wvp_reg HS3 (9%bv : bv 5); rewrite (wvp_den_off EH 11 0 v);
             [rewrite Z.add_0_r; reflexivity | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia] |];
    split; [ wvp_reg HS3 (18%bv : bv 5);
             exact (wvp_den_sh EH 11 40 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                      ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia)) |];
    split; [ wvp_reg HS3 (19%bv : bv 5); rewrite (wvp_den_off EH 12 0 pretty);
             [rewrite Z.add_0_r; reflexivity | exact E3_12 | lia | lia] |];
    split; [ wvp_reg HS3 (20%bv : bv 5); rewrite (wvp_den_off EH 11 40 v);
             [reflexivity | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia] |];
    split; [ wvp_reg HS3 (21%bv : bv 5); reflexivity |];
    split; [ wvp_reg HS3 (22%bv : bv 5); reflexivity |];
    split; [ wvp_reg HS3 (23%bv : bv 5); rewrite (wvp_den_off EH 11 24 v);
             [reflexivity | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia] |];
    split; [ wvp_reg HS3 (24%bv : bv 5);
             exact (wvp_den_addw EH dep ltac:(rewrite OLD3 by (cbv; lia); exact E13) ltac:(lia) ltac:(lia)) |];
    split; [ wvp_reg HS3 (25%bv : bv 5); reflexivity |];
    split; [ wvp_reg HS3 (26%bv : bv 5);
             exact (wvp_den_sh EH 11 24 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                      ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia)) |];
    split; [ wvp_reg HS3 (27%bv : bv 5);
             rewrite (wvp_den_sh EH 11 0 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                      ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia));
             rewrite Z.add_0_r; reflexivity |];
    (* the own frame's words *)
    split; [ wvp_rd HS3 Usp3 (-168); [reflexivity | lia] |];
    split; [ wvp_rd HS3 Usp3 (-160);
             [ cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E13, Z.add_0_r, unsigned_lit_small by lia; reflexivity
             | lia ] |];
    split; [ wvp_rd HS3 Usp3 (-152);
             [ exact (wvp_den_sh EH 11 32 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                        ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia))
             | pose proof (wv_shadow_low (v + 32) ltac:(lia)); lia ] |];
    split; [ wvp_rd HS3 Usp3 (-144);
             [ exact (wvp_den_pr EH pretty E3_12 Hpr) | destruct (pretty =? 0); lia ] |];
    split; [ let Hss := fresh "Hss" in
             assert (Hss : (if pretty =? 0 then 130%nat else 59%nat) = ssep)
               by (first [ rewrite (proj2 (Z.eqb_eq pretty 0) Hc0); reflexivity
                         | rewrite (proj2 (Z.eqb_neq pretty 0) Hc0); reflexivity ]);
             rewrite Hss;
             wvp_rd HS3 Usp3 (-136);
             [ unfold WV_STR;
               let HAT := fresh "HAT" in assert (HAT : wv_addhi_atom ssep = A_OBJ 2) by (vm_compute; reflexivity);
               rewrite HAT; cbn [sv_denot]; rewrite HEI3 by (unfold A_OBJ, A_TEXT, A_LIM; lia);
               let off := eval vm_compute in (wv_addhi_off ssep) in change (wv_addhi_off ssep) with off; reflexivity
             | pose proof (HIMG ssep _ ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right]))
                 ltac:(cbn; lia)); lia ] |];
    split; [ wvp_rd HS3 Usp3 (-128);
             [ exact (wvp_den_off EH 11 32 v ltac:(rewrite OLD3 by (cbv; lia); exact E11) ltac:(lia) ltac:(lia)) | lia ] |];
    split; [ wvp_rd HS3 Usp3 (-120);
             [ unfold WV_STR;
               let HAT := fresh "HAT" in assert (HAT : wv_addhi_atom 151 = A_OBJ 2) by (vm_compute; reflexivity);
               rewrite HAT; cbn [sv_denot]; rewrite HEI3 by (unfold A_OBJ, A_TEXT, A_LIM; lia);
               let off := eval vm_compute in (wv_addhi_off 151) in change (wv_addhi_off 151) with off; reflexivity
             | pose proof (HIMG 151%nat [44] ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right]))
                 ltac:(cbn; lia)); lia ] |];
    split; [ wvp_rd HS3 Usp3 (-112);
             [ cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia);
               rewrite Z.add_0_r; reflexivity
             | unfold SHADOW_OFF; lia ] |];
    let sreg off rn rb :=
      wvp_rd HS3 Usp3 off;
      [ cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite EL by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ rn rb eq_refl), Z.add_0_r; reflexivity
      | exact (bv_unsigned_in_range 64 _) ] in
    split; [ sreg (-104) 27%nat (27%bv : bv 5) |];
    split; [ sreg (-96) 26%nat (26%bv : bv 5) |];
    split; [ sreg (-88) 25%nat (25%bv : bv 5) |];
    split; [ sreg (-80) 24%nat (24%bv : bv 5) |];
    split; [ sreg (-72) 23%nat (23%bv : bv 5) |];
    split; [ sreg (-64) 22%nat (22%bv : bv 5) |];
    split; [ sreg (-56) 21%nat (21%bv : bv 5) |];
    split; [ sreg (-48) 20%nat (20%bv : bv 5) |];
    split; [ sreg (-40) 19%nat (19%bv : bv 5) |];
    split; [ sreg (-32) 18%nat (18%bv : bv 5) |];
    split; [ sreg (-24) 9%nat (9%bv : bv 5) |];
    split; [ sreg (-16) 8%nat (8%bv : bv 5) |];
    sreg (-8) 1%nat (1%bv : bv 5)
  end end
in
let run tg kn slo bso slc bsc tt :=
  idtac;
  destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
    (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap));
  destruct (HJT kn ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro);
  change (4 * Z.of_nat kn) with (4 * tg) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro;
  assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 (WV_JTW (Z.to_nat tg)))
    by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
        intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
        split; [exact R1 | split; [exact R2 | exact R3]]);
  assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * tg)
    by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 v 56 ltac:(lia) ltac:(lia)
          ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]);
  destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
    Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
    Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
    HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK];
  set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) in *;
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env);
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) k)
    by (intros k0 Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk);
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
  assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ;
        symmetry; apply Z_to_bv_bv_unsigned);
  assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
  assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
  assert (E11 : ew E 11 = Z_to_bv 64 v)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11);
  assert (E12 : ew E 12 = Z_to_bv 64 pretty)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12);
  assert (E13 : ew E 13 = Z_to_bv 64 dep)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13);
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0));
  assert (E37 : ew E 37 = Z_to_bv 64 nn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5));
  assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) E)
    by (split; [intros k0 Hk; apply EL; unfold A_TEXT; lia | reflexivity]);
  assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
    by (intros; reflexivity);
  unfold cfg_at; rewrite Hent; change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value));
  (* entry -> the switch's jr *)
  paj_run_tok_x_inv RUNI HS HJ SHOK HPm WV_Bspan;
  [ eapply (wv_awr E tg _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ];
  wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  prreg HS (11%bv : bv 5) R11;
  assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat tg)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6));
  assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia);
  destruct (wv_jr_target E (Z.to_nat tg) E38 EJ HTr) as (Ht & Hr & He);
  eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case kn) HS);
  [ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ];
  let mat1 := fresh "mat" in let ms1 := fresh "ms" in let Hms1 := fresh "Hms" in let HS1 := fresh "HS1" in
  intros mat1 ms1 Hms1 HS1; subst ms1;
  pose proof (wv_pi_at E _ (AF_wv_case kn) _ HS1) as HS2; clear HS1;
  assert (HJ2 := HJ);
  eapply (ajournal_x_materialize (SK := SK)) with (X := mat1) in HJ2;
  [| first [exact LAWS | exact pa_segs_low | idtac] ..];
  clear HJ;
  (* case 36 to the opening bracket's `jal put` (slot 45) *)
  paj_run_tok_x_inv RUNI HS2 HJ2 SHOK HPm WV_Bspan; [ wv_awr_tac Usp d | ];
  wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  pmkst HS2;
  prreg HS2 (10%bv : bv 5) Ra0; prreg HS2 (11%bv : bv 5) Ra1; prreg HS2 (12%bv : bv 5) Ra2;
  prreg HS2 (1%bv : bv 5) Rra1; prreg HS2 (2%bv : bv 5) Rsp1; prreg HS2 (3%bv : bv 5) Rgp1;
  prreg HS2 (4%bv : bv 5) Rtp1; prreg HS2 (8%bv : bv 5) Rs01;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    assert (HspT : spZ rT = spZ regs - 176)
      by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
    pose proof (ajx_ar HJ2) as HARc;
    assert (HOUTc : prhWriter_out W mT Lam o buf st)
      by (eapply (wv_out_keep ly S Hp W W mem mT md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran o buf st
            (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HOUT | exact K2 | exact HLOW | exact HOFF]);
    assert (HLEDc : prh_ledger B ly S Hp W mT Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own)
      by (eapply (wv_led_keep ly S Hp W md mem mT Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran
            (wv_wr (spZ regs))); [exact HAR | exact HLED | exact K2 | exact HLOW8]);
    assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mT))
      by (apply (wv_arodata_keep W W mem mT (wv_wr (spZ regs))); [exact HRO | exact K2 | exact HLOW]);
    destruct (HLIT slo bso ly S Hp W mT dT
      ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right])) HARc HROc)
      as (Hsrc & Hkept & Himg);
    pose proof (wv_lit_home ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran buf
      (WriterApp.w_cap st) (WV_STR slo) (Z.of_nat (length bso)) HAR HLED Hbufin (proj1 Hcap0) ltac:(vm_compute; reflexivity)
      Hkept ltac:(intros a Ha; replace a with (WV_STR slo + (a - WV_STR slo)) by lia; apply Himg; lia)) as Hhome;
    (* The kit's case-1 words (form (a)) at the call memory *)
    assert (HWD : exists ra1 nfp1, rdword (aview SEGS (w_H W) mT) (o - 8) = Some ra1 /\
        rdword (aview SEGS (w_H W) mT) (o - 16) = Some nfp1 /\ nfp1 < YM05.alloc_ceiling);
    [ destruct Hcut as [Hc1 | Hc2];
      [ destruct (wv_reca_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mT) o
          ltac:(intros a Ha; apply K2; [lia | unfold wv_wr; lia]) (Hrecs Hc1)) as (ra1 & Hr1 & nfp1 & Hn1 & Hnl);
        exists ra1, nfp1; split; [exact Hr1 | split; [exact Hn1 | exact Hnl]]
      | destruct (wvp_rdword_some (aview SEGS (w_H W) mT) (spZ regs)) as (w & Hw);
        [ intros j Hj; rewrite (K2 (spZ regs + j)) by (unfold wv_wr; lia);
          apply (aview_some_of_apresent SEGS); apply Hdpres; lia |];
        exists w, (bv_unsigned (getr regs 1));
        split; [replace (o - 8) with (spZ regs) by lia; exact Hw |];
        split; [| unfold raZ in HTOP2; exact HTOP2];
        eapply (wvp_chunk_rdb _ _ _ _ 1%nat 2%nat _ _ _ _ _ (-8));
        [ exact HS2 | reflexivity | exact Usp | lia | cbn [In]; repeat (first [left; reflexivity | right])
        | cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range ] ]
    | ];
    destruct HWD as (ra1 & nfp1 & Hwd8 & Hwd16 & Hwdc);
    assert (Hw1 : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bso) + 1 <= prhWriter_WMAX)
      by (pose proof (wv_wmax_next [] st [] [bso] (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) Hwmax) as X;
          cbn [prhWriter_putN concat app] in X; rewrite ?app_nil_r in X; exact X);
    pose proof (wv_live_next ly S Lam peak buf st ly S Lam peak buf [] [] [bso]
      (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) (proj1 Hcap0) Hbufb
      (or_introl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (Permutation_refl _)))))) Hlive) as Hl1;
    pose proof (wv_cons_next rpsm rpx rpos rpi st [] [bso] (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) []
      Hcons) as HcoA;
    change (length (prhWriter_evs [] st [])) with 0%nat in HcoA; rewrite Nat.add_0_r in HcoA;
    apply SRr_ret; cbv beta;
    eapply SRr'_bind;
    [ eapply (wv_call_put rpsm rpx rpos rpi rpH0 rphist (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st))
        ly S Hp W mem md [] ly S Hp W mT dT 0 rT _ ra1 nfp1 o (WV_STR slo) 1 buf st bso Lam peak ran (- (176 + d))
        (wv_jlift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2));
      [ rewrite HspT; lia
      | apply wv_neg_mod16; rewrite Zplus_mod, Hd16; reflexivity
      | lia
      | lia
      | rewrite Rgp1, E3; exact Hgp
      | rewrite Rtp1, E4; exact Htp
      | exact Rra1
      | apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]
      | rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ A_prog_listing PA) as (HB0 & HB1 & _); lia);
        pose proof (@pa_B_ok _ A_prog_listing PA); lia
      | lazymatch goal with |- bv_unsigned (Z_to_bv 64 (BASE + ?k)) < _ =>
          replace k with (AF_write_value + 4 * 46) by (vm_compute; reflexivity) end;
        exact wvp_ret46_ceil
      | exact HFRM
      | unfold s0Z; rewrite Rs01, E10, H10; apply unsigned_lit_small; lia
      | exact Hwd8 | exact Hwd16 | exact Hwdc
      | exact HROc
      | lia
      | exact Hroom | exact Hrp | exact Hos4 | exact Hcl
      | rewrite Ra0, E10; exact H10
      | rewrite Ra1; unfold WV_STR;
        let HAT := fresh "HAT" in
        assert (HAT : wv_addhi_atom slo = A_OBJ 2) by (vm_compute; reflexivity);
        rewrite HAT; rewrite HEI by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        let off := eval vm_compute in (wv_addhi_off slo) in change (wv_addhi_off slo) with off; reflexivity
      | rewrite Ra2; reflexivity
      | lia | lia
      | exact HOUTc | exact HLEDc | exact Hsrc | reflexivity | exact Hhome
      | exact (wv_ev_first rpsm rpx rpos rpi st bso (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) Hev)
      | exact Hw1 | exact Hhead | exact HcoA | exact Hl1
      | exact (wv_fp_sub (STKv + d) (spZ regs + d) ly S ly S Hp W mT dT o Lam peak buf st Lam peak buf st HARc
          (proj1 Hcap0) (or_introl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (Permutation_refl _)))))))
      ]
    | cbv beta;
      intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & HJ1 & HXT & HP2 &
        (Hroom2 & HPP1 & HRET1) & HMN2);
      pose proof (PCALL mT mem2 HMN2 HPm) as HPM2;
      pose proof (wv_ret_pos_one rpsm rpx rpos rpH0 rpi rphist ly S Hp W mT Lam peak ran o buf st bso
        ly2 S2 Hp2 W2 regs2 mem2 md2 HOUTc HLEDc HPP1 HRET1) as HRP1;
      clear HPP1 HRET1;
      destruct HRP1 as (ok1 & HRET1 & G1 & rphist1 & Hrp1);
      destruct (prhWriter_blk_of_ret_ok B ok1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRET1 G1)
        as (ran1 & buf1 & Lam1 & peak1 & HOKS1 & HOUT1 & HLED1 & HBLK1);
      pose proof (ajxR_ar HJc) as HAR2; pose proof (ajxR_ly HJc) as Hly2; pose proof (ajxR_pres HJc) as Hpres2;
      replace (spZ regs + d + - (176 + d) + - - (176 + d)) with (spZ regs + d) in HJ1 by lia;
      assert (HFK : forall x, pj_footR v D x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mT x)
        by (intros x Hx; exact (proj2 (wv_foot_keep ly S Hp W regs mT dT STKv (STK_put + - - (176 + d)) d o buf
              (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran v D ly2 S2 Hp2 W2 mem2 md2 k1
              ltac:(lia) Hd0 HARc Hstk HLEDc HLOC HD Hoff (proj1 Hcap0) Hbufin HJ1
              ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)));
      jafter_call_keep_pi HS2 39%nat regs2 (mrestrict (w_H W2) mem2) HP2 [1; 4]%nat HS3;
      lazymatch type of HS3 with ?T -> _ => assert (HRK : T) end;
      [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        [ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp;
          intros a Ha;
          [ apply (mbyte_of_aview SEGS); apply HXT;
            [lia | apply (wvp_nfp ly S Hp W mT dT o buf (WriterApp.w_cap st) a HARc Hbufb); lia]
          | intros _; apply (apresent_writable SEGS); apply Hpres2; lia ]
        | split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
          rewrite E11, unsigned_lit_small by lia; intros a Ha;
          [ apply (mbyte_of_aview SEGS); apply HFK; left; lia
          | exfalso; lia ] ]
      | ];
      specialize (HS3 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS3;
      remember (havoc E 39 (map (getr regs2) CLOB)) as EH eqn:HE3 in HS3;
      assert (HEI3 : img_env VAL A_LIM EH) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]);
      assert (OLD3 : forall n, (n < 39)%nat -> ew EH n = ew E n)
        by (intros n0 Hn; rewrite HE3; apply ew_havoc_old; exact Hn);
      assert (HAE3 : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) EH)
        by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE]);
      clear HE3;
      assert (Usp3 : bv_unsigned (ew EH 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp);
      assert (HLK1 : forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1)
        by (intros a k0 Ha Hab; exact (proj1 (wv_lam_keep ly S Lam peak buf st ly2 S2 Lam1 peak1 buf1 _
              (wv_led_nodup _ _ _ _ _ _ _ _ _ _ HLED1) HBLK1 a k0 Ha Hab)));
      assert (RA2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56)
        by (exact (wv_ra_cur ly S Hp W mem md Lam buf v regs STKv d o (WriterApp.w_cap st) ly2 S2 Hp2 W2 mem2 md2
              (0 + k1) Lam1 peak1 _ _ ran1 HAR Hstk HRA HLOC HJc HLED1 HLK1 ltac:(lia) Hbufb));
      assert (SHOK3 : sh_ok SEGS WV_Bx wv_SH EH (mrestrict (w_H W2) mem2))
        by (apply (wvp_shok (w_H W2) mem2 EH v RA2);
            [rewrite OLD3 by (cbv; lia); exact E32 | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia | exact Hband]);
      assert (K20 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by (intros; reflexivity);
      paj_run_tok_x_inv RUNIR HS3 HJc SHOK3 HPM2 WV_Bspan; [ wv_awr_tac Usp3 d | ];
      wv_keep_run HFr K20 K3 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
      assert (E3_37 : ew EH 37 = Z_to_bv 64 nn) by (rewrite OLD3 by (cbv; lia); exact E37);
      assert (E3_12 : ew EH 12 = Z_to_bv 64 pretty) by (rewrite OLD3 by (cbv; lia); exact E12);
      psrr_branch_tok RUNIR BRR HS3 SHOK3 WV_Bspan;
      [ (* n = 0: the empty container's closing bracket *)
        rewrite branch_eq_U, (U_atom EH 37 nn E3_37 Rnn), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
        apply Z.eqb_eq in Hc;
        destruct l as [|x0 l0]; [| exfalso; cbn [length] in Hnn; lia];
        paj_run_to_tok_x_inv RUNTOIR HS3 HJc SHOK3 HPM2 WV_Bspan (AF_write_value + 4 * 236); [ wv_awr_tac Usp3 d | ];
        wv_keep_run HFr K3 K4 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
        paj_run_tok_x_inv RUNIR HS3 HJc SHOK3 HPM2 WV_Bspan; [ wv_awr_tac Usp3 d | ];
        wv_keep_run HFr K4 K5 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
        prreg HS3 (10%bv : bv 5) Rc0; prreg HS3 (11%bv : bv 5) Rc1; prreg HS3 (12%bv : bv 5) Rc2;
        prreg HS3 (1%bv : bv 5) Rcra;
        lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?msx) =>
        lazymatch type of HNODE0 with pj_nodeR _ _ _ _ ?tc _ =>
          assert (HAPc : aregs_preserved regs (ms_regs msx))
            by (eapply (aregs_preserved_of_st_ok SEGS (w_H W2) EH _ _ regs _);
                [exact HS3 | exact HAE3 | vm_compute; reflexivity]);
          assert (Hspc : spZ (ms_regs msx) = spZ regs)
            by (unfold spZ; f_equal; exact (HAPc 2 ltac:(unfold acallee_saved; lia)));
          assert (Hgpc : getr (ms_regs msx) 3 = w64 (as_gp B))
            by (rewrite <- Hgp; exact (HAPc 3 ltac:(unfold acallee_saved; lia)));
          assert (Htpc : getr (ms_regs msx) 4 = w64 (as_tp B))
            by (rewrite <- Htp; exact (HAPc 4 ltac:(unfold acallee_saved; lia)));
          assert (Hs0c : s0Z (ms_regs msx) = s0Z regs)
            by (unfold s0Z; f_equal; exact (HAPc 8 ltac:(unfold acallee_saved; lia)));
          assert (Hrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rcra, OLD3 by (cbv; lia); exact E1);
          assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Rc0, OLD3, E10 by (cbv; lia); exact H10);
          assert (H11c : getr (ms_regs msx) 11 = w64 (WV_STR slc))
            by (rewrite Rc1; unfold WV_STR;
                let HAT := fresh "HAT" in assert (HAT : wv_addhi_atom slc = A_OBJ 2) by (vm_compute; reflexivity);
                rewrite HAT; rewrite HEI3 by (unfold A_OBJ, A_TEXT, A_LIM; lia);
                let off := eval vm_compute in (wv_addhi_off slc) in change (wv_addhi_off slc) with off; reflexivity);
          assert (H12c : getr (ms_regs msx) 12 = w64 (Z.of_nat (length bsc))) by (rewrite Rc2; reflexivity);
          assert (HKW2 : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
              aview SEGS (w_H W2) (ms_mem msx) a = aview SEGS (w_H W) mem a)
            by (intros a Ha Hf; rewrite (K5 a ltac:(lia) ltac:(unfold wv_wr; lia)), (HXT a ltac:(lia) Hf);
                apply K2; [lia | unfold wv_wr; lia]);
          pose proof (ajxR_ar HJc) as HARc2;
          assert (HOUT1c : prhWriter_out W2 (ms_mem msx) Lam1 o buf1 (prhWriter_putN ok1 st [bso]))
            by (eapply (wv_out_keep ly2 S2 Hp2 W2 W2 mem2 (ms_mem msx) md2 Lam1 peak1 _ _ ran1 o buf1 _
                  (wv_wr (spZ regs))); [exact HAR2 | exact HLED1 | exact HOUT1 | exact K5 | exact HLOW | exact HOFF]);
          assert (HLED1c : prh_ledger B ly2 S2 Hp2 W2 (ms_mem msx) Lam1 peak1
              (WriterApp.w_cnt (prhWriter_putN ok1 st [bso])) (WriterApp.w_fail (prhWriter_putN ok1 st [bso])) ran1 most own)
            by (eapply (wv_led_keep ly2 S2 Hp2 W2 md2 mem2 (ms_mem msx) Lam1 peak1 _ _ ran1 (wv_wr (spZ regs)));
                [exact HAR2 | exact HLED1 | exact K5 | exact HLOW8]);
          assert (HROc2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem msx)))
            by (exact (wv_arodata_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hclosed HRO));
          destruct (HLIT slc bsc ly2 S2 Hp2 W2 (ms_mem msx) _
            ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right])) HARc2 HROc2)
            as (Hsrc2 & Hkept2 & Himg2);
          assert (Hbuf1in : WriterApp.w_cap (prhWriter_putN ok1 st [bso]) <> 0 ->
              In (buf1, WriterApp.w_cap (prhWriter_putN ok1 st [bso])) Lam1)
            by (intros Hc1; destruct HOUT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin1 & _)]);
                [lia | exact Hin1]);
          pose proof HOUT1 as (_ & _ & Hcap1 & _);
          pose proof (wv_lit_home ly2 S2 Hp2 W2 (ms_mem msx) _ Lam1 peak1 _ _ ran1 buf1
            (WriterApp.w_cap (prhWriter_putN ok1 st [bso])) (WV_STR slc) (Z.of_nat (length bsc)) HARc2 HLED1c Hbuf1in
            (proj1 Hcap1) ltac:(vm_compute; reflexivity) Hkept2
            ltac:(intros a Ha; replace a with (WV_STR slc + (a - WV_STR slc)) by lia; apply Himg2; lia)) as Hhome2;
          pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _);
          assert (Hchc : achain ly2 (aview SEGS (w_H W2) (ms_mem msx)) (spZ regs) (s0Z (ms_regs msx)) ch);
          [ rewrite Hs0c;
            apply (wvp_achain_keep16 ly ly2 (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch Hchain
              ltac:(first [exact Etop2 | exact (eq_sym Etop2)]) ltac:(lia));
            [ intros Hge a Ha; destruct Hs0 as [Hso | Hsl]; [| lia];
              apply HKW2; [lia | apply (wvp_nfp ly S Hp W mem md o buf (WriterApp.w_cap st) a HAR Hbufb); lia]
            | intros Hge nfp Hn; destruct Hs0 as [Hso | Hsl]; [| lia];
              rewrite Hso in Hn, Hge; destruct (Hrecs Hge) as (ra0 & _ & nfp0 & Hn0 & Hl0);
              rewrite Hn in Hn0; injection Hn0 as ->; exact Hl0 ]
          | ];
          assert (Hch0c : spZ regs + 16 <= o ->
              exists ra, rdword (aview SEGS (w_H W2) (ms_mem msx)) (o - 8) = Some ra /\
                exists nfp, rdword (aview SEGS (w_H W2) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
            by (intros Hc1; apply (wv_reca_keep (aview SEGS (w_H W) mem) _ o);
                [ intros a Ha; apply HKW2; [lia | apply (wvp_nfp ly S Hp W mem md o buf (WriterApp.w_cap st) a HAR Hbufb); lia]
                | exact (Hrecs Hc1) ]);
          assert (Hw2 : Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok1 st [bso]))) + Z.of_nat (length bsc) + 1
              <= prhWriter_WMAX)
            by (exact (wv_wmax_next ok1 st [bso] [bsc] [] Hwmax));
          pose proof (wv_live_next ly S Lam peak buf st ly2 S2 Lam1 peak1 buf1 ok1 [bso] [bsc] [] (proj1 Hcap0) Hbufb
            HBLK1 Hlive) as Hl2;
          pose proof (wv_cons_next rpsm rpx rpos rpi st [bso] [bsc] [] ok1 Hcons) as HcoB;
          pmkst HS3;
          eapply SRr'_mono;
          [ exact (wv_post_P fx W2 _ STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md (ms_mem msx) _
              HFRM (wv_fk_refl fx)
              (wv_tail_gen rpsm rpx rpos rpi rpH0 ly S Hp W regs mem md ch STKv d o v tc D Lam peak ran buf st [bso]
                 (WV_STR slc) bsc ly2 S2 Hp2 W2 (ms_mem msx) _ (0 + k1) (ms_regs msx) ok1 ran1 buf1 Lam1 peak1
                 (rpi + length (prhWriter_evs ok1 st [bso]))%nat rphist1
                 ltac:(lia) ltac:(lia) HPRE Hcl HWIN Ho1 Ho2 HLED HOUT HNODE0 HLOC HD Hoff HJc HKW2 Hroom2 eq_refl Hrp1 Hos4
                 HOKS1 G1 HOUT1c HLED1c HBLK1 HAPc Hspc Hrac Hgpc Htpc Hchc HROc2 H10c H11c H12c Hcut Hch0c Hev Hsrc2
                 Hhome2 Hw2 Hhead HcoB Hl2)
              HPM2)
          | cbv beta; let W' := fresh "W'" in let c' := fresh "c'" in let HQ := fresh "HQ" in
            intros W' c' _ HQ; exact HQ ]
        end end
      | (* n <> 0: the separator by pretty, then the loop head *)
        rewrite branch_eq_U, (U_atom EH 37 nn E3_37 Rnn), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
        apply Z.eqb_neq in Hc;
        paj_run_to_tok_x_inv RUNTOIR HS3 HJc SHOK3 HPM2 WV_Bspan (AF_write_value + 4 * 153); [ wv_awr_tac Usp3 d | ];
        wv_keep_run HFr K3 K4 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
        psrr_branch_tok RUNIR BRR HS3 SHOK3 WV_Bspan;
        [ rewrite branch_eq_U, (U_atom EH 12 pretty E3_12 Hpr), U_SLit, (zcanon_id 0) in Hc0 by (unfold M64; lia);
          apply Z.eqb_eq in Hc0;
          paj_run_to_tok_x_inv RUNTOIR HS3 HJc SHOK3 HPM2 WV_Bspan (AF_write_value + 4 * 153); [ wv_awr_tac Usp3 d | ];
          wv_keep_run HFr K4 K5 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
          head 130%nat bso
        | rewrite branch_eq_U, (U_atom EH 12 pretty E3_12 Hpr), U_SLit, (zcanon_id 0) in Hc0 by (unfold M64; lia);
          apply Z.eqb_neq in Hc0;
          paj_run_to_tok_x_inv RUNTOIR HS3 HJc SHOK3 HPM2 WV_Bspan (AF_write_value + 4 * 153); [ wv_awr_tac Usp3 d | ];
          wv_keep_run HFr K4 K5 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
          head 59%nat bso ] ] ]
  end
in
destruct Ht as [[l ->] | [l ->]];
[ pose proof HNODE as HNODE0;
  destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody);
  destruct Hbody as (_ & _ & Hnn & _);
  run 5 5%nat 39%nat [91] 216%nat [93] (PjTree.JArr l)
| pose proof HNODE as HNODE0;
  destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody);
  destruct Hbody as (_ & Hnn & _);
  run 6 6%nat 42%nat [123] 219%nat [125] (PjTree.JObj l) ].
Qed.

End c2b.

(* lia with the powers this walk meets as numerals (with the euclidean-division flag off it treats 2 ^ k as an atom) *)
Local Ltac zl :=
  pose proof (eq_refl : 2 ^ 64 = 18446744073709551616); pose proof (eq_refl : 2 ^ 47 = 140737488355328);
  pose proof (eq_refl : 2 ^ 46 = 70368744177664); pose proof (eq_refl : 2 ^ 44 = 17592186044416);
  pose proof (eq_refl : 2 ^ 32 = 4294967296); pose proof (eq_refl : 2 ^ 31 = 2147483648); lia.
Local Ltac zs := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; zl.
Local Ltac wvl_er EL n r := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ n r eq_refl).
Local Ltac wvl_ex EL j := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j).

Section l0. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.
Let RUNTOI := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.


(* ======== THE ITEM LOOP (wv_loop; S7bWvLoop): from the loop head to the container's end ======== *)
(* ---- the loop's seated states: wv_ssH's registers, node, key slot and facts, with the own frame READ ONLY (the
   body from the head, slot 153, to the tail `j put`, slot 236, stores nothing: loads, arithmetic, branches and the
   calls only), at a pc of the body. A run from such a state keeps every byte (its frame_of has no window). ---- *)
Definition wvl_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 176 0 0 (YP09.r_chunks wvh_frame).
(* the key slot keys + 8 i (atom 39, its word the atom 40) is seated only where the object case reads it (kr) *)
Definition wvl_mem (tg : Z) (kr : bool) : smem := wvl_frame :: wvh_node tg :: (if kr then [wvh_key] else []).
Definition wvl_facts (kr : bool) : facts :=
  mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
             (9%nat, mkAF 4096 (2 ^ 47 - 56) 3) ] ++ (if kr then [(39%nat, mkAF 4096 (2 ^ 47 - 8) 3)] else []))
    [ mkAC BC_NE (SOff 38 0) (SLit 0) ]
    ([ (SAlu ALU_ADD (SOff 36 0) (SOff 25 0), SOff 41 0) ] ++
     (if kr then [(SAlu ALU_ADD (SOff 37 0) (SOff 22 0), SOff 39 0)] else [])).
Definition wvl_SH (kr : bool) : list shent := mkSHE 9 0 56 :: (if kr then [mkSHE 39 0 8] else []).
Definition wvl_ss (pc tg : Z) (kr : bool) : sstate := mkSS pc wvh_regs (wvl_mem tg kr) None (wvl_facts kr).
Definition WVL_PC (k : Z) : Z := AF_write_value + 4 * k.
(* the entry's s0, s1, s2 .. s11, ra (the saved slots 160, 152, 144 .. 72, 168: atoms 42 .. 54) *)
Definition wvl_sv13 (X : wvx) : list Z :=
  [bv_unsigned (getr (y_regs X) 8); bv_unsigned (getr (y_regs X) 9); bv_unsigned (getr (y_regs X) 18);
   bv_unsigned (getr (y_regs X) 19); bv_unsigned (getr (y_regs X) 20); bv_unsigned (getr (y_regs X) 21);
   bv_unsigned (getr (y_regs X) 22); bv_unsigned (getr (y_regs X) 23); bv_unsigned (getr (y_regs X) 24);
   bv_unsigned (getr (y_regs X) 25); bv_unsigned (getr (y_regs X) 26); bv_unsigned (getr (y_regs X) 27);
   bv_unsigned (getr (y_regs X) 1)].
Definition wvl_E (X : wvx) (i : nat) (regsc : bvmap 5 word) (kids keys nn kp : Z) : env :=
  wv_EH regsc (y_dep X) (WV_STR (wv_sep_slot X)) (WV_STR 151) kids keys nn (keys + 8 * Z.of_nat i) kp
    (kids + 56 * Z.of_nat i) (wvl_sv13 X).


(* the head's register and frame-word facts (wv_head's own conjuncts after the pieces) *)
Definition wvl_rf (X : wvx) (i : nat) (Wc : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) : Prop :=
  let R := y_sp X - 176 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\ getr regsc 18 = w64 (SHADOW_OFF + (v + 40) / 8) /\
  getr regsc 19 = w64 (y_pretty X) /\ getr regsc 20 = w64 (v + 40) /\ getr regsc 21 = w64 (Z.of_nat i) /\
  getr regsc 22 = w64 (8 * Z.of_nat i) /\ getr regsc 23 = w64 (v + 24) /\ getr regsc 24 = w64 (y_dep X + 1) /\
  getr regsc 25 = w64 (56 * Z.of_nat i) /\ getr regsc 26 = w64 (SHADOW_OFF + (v + 24) / 8) /\
  getr regsc 27 = w64 (SHADOW_OFF + v / 8) /\
  rdword rd (R + 8) = Some 3 /\ rdword rd (R + 16) = Some (y_dep X) /\
  rdword rd (R + 24) = Some (SHADOW_OFF + (v + 32) / 8) /\
  rdword rd (R + 32) = Some (if y_pretty X =? 0 then 1 else 2) /\
  rdword rd (R + 40) = Some (WV_STR (wv_sep_slot X)) /\ rdword rd (R + 48) = Some (v + 32) /\
  rdword rd (R + 56) = Some (WV_STR 151) /\ rdword rd (R + 64) = Some SHADOW_OFF /\
  rdword rd (R + 72) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 80) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 1)).

(* a join of the body: the common facts after the pieces P and the registers and frame words at item counter i *)
Definition wvl_st (X : wvx) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word)
  (memc : word -> option byte) mdc kc : Prop :=
  wv_common X P lyc Sc Hpc Wc memc mdc kc /\ wvl_rf X i Wc regsc memc.

Lemma wvl_head_st : forall X i P lyc Sc Hpc Wc regsc memc mdc kc,
  wv_head X i P lyc Sc Hpc Wc regsc memc mdc kc ->
  wvl_st X i P lyc Sc Hpc Wc regsc memc mdc kc /\ (i < wv_nitems (y_t X))%nat /\ P = wv_done X i.
Proof.
intros X i P lyc Sc Hpc Wc regsc memc mdc kc (Hc & Hi & HP & Hr).
split; [split; [exact Hc | exact Hr] | split; [exact Hi | exact HP]].
Qed.

Lemma wvl_st_head : forall X i P lyc Sc Hpc Wc regsc memc mdc kc,
  wvl_st X i P lyc Sc Hpc Wc regsc memc mdc kc -> (i < wv_nitems (y_t X))%nat -> P = wv_done X i ->
  wv_head X i P lyc Sc Hpc Wc regsc memc mdc kc.
Proof.
intros X i P lyc Sc Hpc Wc regsc memc mdc kc (Hc & Hr) Hi HP.
split; [exact Hc|]. split; [exact Hi|]. split; [exact HP | exact Hr].
Qed.

(* the float clause of a join (wv_common's last two conjuncts): the current float state's rounding mode is 0 and its
   fs0-fs11 are the entry's *)
Lemma wv_common_float : forall X P lyc Sc Hpc Wc memc mdc kc,
  wv_common X P lyc Sc Hpc Wc memc mdc kc -> YK0o.frm_zero (@YK11.fp_csr fx) /\ fregs_kept_x (y_fx X) fx.
Proof. intros X P lyc Sc Hpc Wc memc mdc kc (_ & _ & _ & _ & _ & _ & HZ & HF). exact (conj HZ HF). Qed.

(* the shadow address the head's registers hold, as the engine forms it *)
Lemma wvl_sh_denot : forall E (k : nat) c x,
  ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= x -> 0 <= c -> x + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SHADOW_OFF + (x + c) / 8).
Proof.
intros E k c x Hk H32 Hx Hc Hxc.
assert (Hd : 0 <= (x + c) / 8 < 17592186044416)
  by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_srl3, (U_atom_off E k x c Hk) by zl.
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; zl).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; zl). lia.
Qed.

(* the frame word at 32: (pretty != 0) + 1 *)
Lemma wvl_p1_denot : forall E p, ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)) =
    Z_to_bv 64 (if p =? 0 then 1 else 2).
Proof.
intros E p Hp Rp. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 19 p Hp Rp), !U_SLit. change (zcanon 0) with 0. change (zcanon 1) with 1.
destruct (Z.eqb_spec p 0) as [->|Hn].
- reflexivity.
- replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* the seated join at slot pc of the body (pa_entry_st_ok_full, as wv_entry at the entry) *)
Lemma wvl_seat : forall X i Wc regsc memc pc tg (kr : bool) kids keys nn kp,
  (tg = 5 \/ tg = 6) ->
  wvl_rf X i Wc regsc memc ->
  0 <= y_pretty X < 2 ^ 64 -> 0 <= y_dep X < 2 ^ 31 ->
  y_sp X mod 16 = 0 -> YM05.alloc_ceiling + 176 <= y_sp X <= 2 ^ 47 ->
  y_v X mod 8 = 0 -> 4096 <= y_v X -> y_v X + 56 <= 2 ^ 47 ->
  (y_v X + 56 <= y_sp X - 176 \/ y_sp X <= y_v X) ->
  (y_v X + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= y_v X) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (y_v X) 56 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 tg ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) 8 kids -> 0 <= kids -> kids + 56 * Z.of_nat i < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) 8 keys -> 0 <= keys -> keys + 8 * Z.of_nat i < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) 8 nn -> 0 < nn < 2 ^ 64 ->
  0 <= WV_STR (wv_sep_slot X) < 2 ^ 64 -> 0 <= WV_STR 151 < 2 ^ 64 ->
  (kr = true -> 0 <= kp < 2 ^ 64 /\ val_mem SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) 8 kp /\
     (keys + 8 * Z.of_nat i) mod 8 = 0 /\ 4096 <= keys + 8 * Z.of_nat i /\
     keys + 8 * Z.of_nat i + 8 <= YM05.alloc_ceiling /\
     (keys + 8 * Z.of_nat i + 8 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= keys + 8 * Z.of_nat i) /\
     range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 /\
     (keys + 8 * Z.of_nat i + 8 <= y_v X \/ y_v X + 56 <= keys + 8 * Z.of_nat i)) ->
  img_env VAL A_LIM (wvl_E X i regsc kids keys nn kp) /\ regs_ok (wvl_E X i regsc kids keys nn kp) wvh_regs regsc /\
  st_ok_pi SEGS VAL (wvl_E X i regsc kids keys nn kp) (wvl_ss pc tg kr)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx (wvl_SH kr) (wvl_E X i regsc kids keys nn kp) (mrestrict (w_H Wc) memc).
Proof.
intros X i Wc regsc memc pc tg kr kids keys nn kp Htg HRF Hpr Hdep Hsp16 Hsp Hv8 Hv4096 Hv47 Hvsp Hband Hra
  Vtg Vkids Rkids Rkids2 Vkeys Rkeys Rkeys2 Vnn Rnn Rsep Rcom Hkey.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
unfold wvl_rf in HRF. cbv beta zeta in HRF.
destruct HRF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168).
set (v := y_v X) in *. set (sp := y_sp X) in *.
set (E := wvl_E X i regsc kids keys nn kp).
set (ka := keys + 8 * Z.of_nat i) in *. set (ca := kids + 56 * Z.of_nat i) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wvl_E, wv_EH; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regsc (wvh_extra (y_dep X) (WV_STR (wv_sep_slot X))
    (WV_STR 151) kids keys nn ka kp ca (wvl_sv13 X))) k)
  by (intros k Hk; subst E; unfold wvl_E, wv_EH; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regsc 2) by wvl_er EL 2%nat (2%bv : bv 5).
assert (E9 : ew E 9 = getr regsc 9) by wvl_er EL 9%nat (9%bv : bv 5).
assert (E19 : ew E 19 = getr regsc 19) by wvl_er EL 19%nat (19%bv : bv 5).
assert (E22 : ew E 22 = getr regsc 22) by wvl_er EL 22%nat (22%bv : bv 5).
assert (E25 : ew E 25 = getr regsc 25) by wvl_er EL 25%nat (25%bv : bv 5).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by wvl_ex EL 0%nat.
assert (E33 : ew E 33 = Z_to_bv 64 (y_dep X)) by wvl_ex EL 1%nat.
assert (E34 : ew E 34 = Z_to_bv 64 (WV_STR (wv_sep_slot X))) by wvl_ex EL 2%nat.
assert (E35 : ew E 35 = Z_to_bv 64 (WV_STR 151)) by wvl_ex EL 3%nat.
assert (E36 : ew E 36 = Z_to_bv 64 kids) by wvl_ex EL 4%nat.
assert (E37 : ew E 37 = Z_to_bv 64 keys) by wvl_ex EL 5%nat.
assert (E38 : ew E 38 = Z_to_bv 64 nn) by wvl_ex EL 6%nat.
assert (E39 : ew E 39 = Z_to_bv 64 ka) by wvl_ex EL 7%nat.
assert (E40 : ew E 40 = Z_to_bv 64 kp) by wvl_ex EL 8%nat.
assert (E41 : ew E 41 = Z_to_bv 64 ca) by wvl_ex EL 9%nat.
assert (E42 : ew E 42 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 8))) by wvl_ex EL 10%nat.
assert (E43 : ew E 43 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 9))) by wvl_ex EL 11%nat.
assert (E44 : ew E 44 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 18))) by wvl_ex EL 12%nat.
assert (E45 : ew E 45 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 19))) by wvl_ex EL 13%nat.
assert (E46 : ew E 46 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 20))) by wvl_ex EL 14%nat.
assert (E47 : ew E 47 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 21))) by wvl_ex EL 15%nat.
assert (E48 : ew E 48 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 22))) by wvl_ex EL 16%nat.
assert (E49 : ew E 49 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 23))) by wvl_ex EL 17%nat.
assert (E50 : ew E 50 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 24))) by wvl_ex EL 18%nat.
assert (E51 : ew E 51 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 25))) by wvl_ex EL 19%nat.
assert (E52 : ew E 52 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 26))) by wvl_ex EL 20%nat.
assert (E53 : ew E 53 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 27))) by wvl_ex EL 21%nat.
assert (E54 : ew E 54 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 1))) by wvl_ex EL 22%nat.
assert (Usp : bv_unsigned (ew E 2) = sp - 176)
  by (rewrite E2, G2; unfold w64; apply unsigned_lit_small; zl).
assert (Uv : bv_unsigned (ew E 9) = v) by (rewrite E9, G9; unfold w64; apply unsigned_lit_small; zl).
assert (E9' : ew E 9 = Z_to_bv 64 v) by (rewrite E9, G9; reflexivity).
assert (Uka : bv_unsigned (ew E 39) = ka) by (rewrite E39; apply unsigned_lit_small; zl).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z)
  by (intros k z Hk Hz; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hz).
assert (Rbv : forall r : bv 5, 0 <= bv_unsigned (getr (y_regs X) r) < 2 ^ 64)
  by (intros r; apply u64_range).
(* the frame words, as chunk values *)
assert (FC : forall off e z, sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
    rdword (aview SEGS (w_H Wc) memc) (sp - 176 + off) = Some z ->
    YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp - 176) (YP09.mkChunk off (CVal 8 e))).
{ intros off e z He Hz Hw. apply (chunk_ok_val SEGS E _ (sp - 176) off 8 e z He); [zs | zs |].
  exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hw). }
assert (FA : forall off (n : nat) z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
    rdword (aview SEGS (w_H Wc) memc) (sp - 176 + off) = Some z ->
    YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp - 176) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n z Hn Hz Hw. apply (FC off (SOff n 0) z); [|exact Hz|exact Hw].
  cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Hregs : regs_ok E wvh_regs regsc).
{ apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let w := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with w end;
      first
      [ rewrite getr_zero; reflexivity
      | cbn [sv_denot]; rewrite Z.add_0_r, EL by (unfold A_TEXT; lia);
        rewrite ew_Ereg_lt by zl;
        match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regsc ?x)) =>
          let y := eval vm_compute in x in change x with y end;
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | rewrite (wvl_sh_denot E 9 40 v E9' E32) by zl; exact G18
      | rewrite (wvl_sh_denot E 9 24 v E9' E32) by zl; exact G26
      | rewrite (wvl_sh_denot E 9 0 v E9' E32) by zl; rewrite Z.add_0_r; exact G27
      | cbn [sv_denot]; rewrite Uv; first [exact G20 | exact G23] ]
    | ]).
  destruct Hr. }
assert (Hfacts_common :
  atoms_ok E [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
               (9%nat, mkAF 4096 (2 ^ 47 - 56) 3) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Uv, E32, unsigned_lit_small by (unfold SHADOW_OFF; zl).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. 
  assert (Hsp16' : (sp - 176) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  change (2 ^ 46) with 70368744177664. unfold SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; zl. }
assert (Hcond : conds_ok E [mkAC BC_NE (SOff 38 0) (SLit 0)]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, (U_atom E 38 nn E38 ltac:(zl)), U_lit by zl.
  destruct (Z.eqb_spec nn 0); [zl | reflexivity]. }
assert (Hal1 : sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 25 0)) = sv_denot E (SOff 41 0)).
{ rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 36 kids E36) by zl. rewrite (U_atom E 25 (56 * Z.of_nat i)) by first [rewrite E25, G25; reflexivity | zl].
  rewrite (U_atom E 41 ca E41) by zl. unfold ca. apply zcanon_id. unfold M64. zl. }
assert (Hal2 : sv_denot E (SAlu ALU_ADD (SOff 37 0) (SOff 22 0)) = sv_denot E (SOff 39 0)).
{ rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 37 keys E37) by zl. rewrite (U_atom E 22 (8 * Z.of_nat i)) by first [rewrite E22, G22; reflexivity | zl].
  rewrite (U_atom E 39 ka E39) by zl. unfold ka. apply zcanon_id. unfold M64. zl. }
assert (Hframe : region_ok SEGS E (mrestrict (w_H Wc) memc) wvl_frame).
{ unfold region_ok, wvl_frame, wvh_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Usp. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (FC 8 (SLit 3) 3); [reflexivity | zl | exact F8].
  - apply (FA 16 33%nat (y_dep X) E33); [zl | exact F16].
  - apply (FC 24 (wvh_sh 9 32) (SHADOW_OFF + (v + 32) / 8)); [apply wvl_sh_denot; [exact E9' | exact E32 | zl | zl | zl]
    | | exact F24].
    assert (0 <= (v + 32) / 8 < 17592186044416) by (split; [apply Z.div_pos; zl | apply Z.div_lt_upper_bound; zl]).
    unfold SHADOW_OFF. zl.
  - apply (FC 32 _ (if y_pretty X =? 0 then 1 else 2)); [| destruct (y_pretty X =? 0); zl | exact F32].
    apply wvl_p1_denot; [rewrite E19, G19; reflexivity | exact Hpr].
  - apply (FA 40 34%nat _ E34); [exact Rsep | exact F40].
  - apply (FC 48 (SOff 9 32) (v + 32)); [| zl | exact F48].
    rewrite denot_lit_U. f_equal. apply (U_atom_off E 9 v 32 E9'); zl.
  - apply (FA 56 35%nat _ E35); [exact Rcom | exact F56].
  - apply (FA 64 32%nat SHADOW_OFF E32); [unfold SHADOW_OFF; zl | exact F64].
  - apply (FA 72 53%nat _ E53); [apply Rbv | exact F72].
  - apply (FA 80 52%nat _ E52); [apply Rbv | exact F80].
  - apply (FA 88 51%nat _ E51); [apply Rbv | exact F88].
  - apply (FA 96 50%nat _ E50); [apply Rbv | exact F96].
  - apply (FA 104 49%nat _ E49); [apply Rbv | exact F104].
  - apply (FA 112 48%nat _ E48); [apply Rbv | exact F112].
  - apply (FA 120 47%nat _ E47); [apply Rbv | exact F120].
  - apply (FA 128 46%nat _ E46); [apply Rbv | exact F128].
  - apply (FA 136 45%nat _ E45); [apply Rbv | exact F136].
  - apply (FA 144 44%nat _ E44); [apply Rbv | exact F144].
  - apply (FA 152 43%nat _ E43); [apply Rbv | exact F152].
  - apply (FA 160 42%nat _ E42); [apply Rbv | exact F160].
  - apply (FA 168 54%nat _ E54); [apply Rbv | exact F168]. }
assert (Hnode : region_ok SEGS E (mrestrict (w_H Wc) memc) (wvh_node tg)).
{ unfold region_ok, wvh_node. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Uv. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ v 0 4 (SLit tg) tg); [reflexivity | zs | zs | rewrite Z.add_0_r; exact Vtg].
  - apply (chunk_ok_val SEGS E _ v 24 8 (SOff 36 0) kids);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zs | zs | exact Vkids].
  - apply (chunk_ok_val SEGS E _ v 32 8 (SOff 37 0) keys);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zs | zs | exact Vkeys].
  - apply (chunk_ok_val SEGS E _ v 40 8 (SOff 38 0) nn);
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zs | zs | exact Vnn]. }
assert (Hshv : shent_ok SEGS WV_Bx E (mrestrict (w_H Wc) memc) (mkSHE 9 0 56)).
{ apply (shent_ok_of_range SEGS (w_H Wc) memc E WV_Bx 9 v 56 v 0 56 Hra).
  - unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; zl). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E9', Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by zl. reflexivity.
  - zl.
  - zl.
  - intros a Ha. unfold SHADOW_OFF in *. zl. }
split; [exact HEI|]. split; [exact Hregs|].
destruct kr.
- (* the key slot seated: frame, node and key *)
  destruct (Hkey eq_refl) as (Rkp & Vkp & Hka8 & Hka4096 & Hkac & Hkaband & Hkara & Hkav).
  assert (Hkey_r : region_ok SEGS E (mrestrict (w_H Wc) memc) wvh_key).
  { unfold region_ok, wvh_key. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Uka. split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ ka 0 8 (SOff 40 0) kp);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zs | zs |
       rewrite Z.add_0_r; exact Vkp]. }
  split.
  + rewrite restrict_mkst_fx. unfold wvl_ss, wvl_mem.
    apply pa_entry_st_ok_full.
    * exact Hregs.
    * destruct Htg as [-> | ->]; vm_compute; reflexivity.
    * repeat apply Forall_cons; try apply Forall_nil; [exact Hframe | exact Hnode | exact Hkey_r].
    * apply pairwise_disjoint_of_extents. unfold extent_of_region, wvl_frame, wvh_node, wvh_key.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv, Uka.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; zl.
    * unfold wvl_facts.
      split.
      -- cbn [app atoms_ok]. cbn [atoms_ok] in Hfacts_common.
         destruct Hfacts_common as (A1 & A2 & A3 & _).
         split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [|exact I].
         unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Uka. change (2 ^ 3) with 8. zl.
      -- split; [exact Hcond|]. cbn [app alias_ok]. split; [exact Hal1|]. split; [exact Hal2 | exact I].
  + unfold sh_ok, wvl_SH. constructor; [exact Hshv | constructor; [|constructor]].
    apply (shent_ok_of_range SEGS (w_H Wc) memc E WV_Bx 39 ka 8 ka 0 8 Hkara).
    * unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; zl). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by zl. reflexivity.
    * zl.
    * zl.
    * intros a Ha. unfold SHADOW_OFF in *. zl.
- (* frame and node only *)
  split.
  + rewrite restrict_mkst_fx. unfold wvl_ss, wvl_mem. cbn [app].
    apply pa_entry_st_ok_full.
    * exact Hregs.
    * destruct Htg as [-> | ->]; vm_compute; reflexivity.
    * repeat apply Forall_cons; try apply Forall_nil; [exact Hframe | exact Hnode].
    * apply pairwise_disjoint_of_extents. unfold extent_of_region, wvl_frame, wvh_node.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; zl.
    * unfold wvl_facts. rewrite !app_nil_r.
      split; [exact Hfacts_common|]. split; [exact Hcond|]. cbn [alias_ok]. split; [exact Hal1 | exact I].
  + unfold sh_ok, wvl_SH. constructor; [exact Hshv | constructor].
Qed.

(* ---- the container's pieces at item i: the item's own pieces, the pieces after the first j items ---- *)
Lemma wvl_firstn_S : forall {A} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia.
- reflexivity.
- change (firstn (S (S i)) (x :: l)) with (x :: firstn (S i) l).
  change (firstn (S i) (x :: l)) with (x :: firstn i l). change (nth (S i) (x :: l) d) with (nth i l d).
  rewrite (IH i d) by lia. reflexivity.
Qed.

Lemma wvl_skipn_nth : forall {A} (l : list A) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia.
- reflexivity.
- change (skipn (S i) (x :: l)) with (skipn i l). change (skipn (S (S i)) (x :: l)) with (skipn (S i) l).
  change (nth (S i) (x :: l) d) with (nth i l d). apply IH. lia.
Qed.

Definition wvl_item (X : wvx) (i : nat) : list (list Z) :=
  match y_t X with
  | PjTree.JArr l => WriterValue.wcomma i ++ WriterValue.wind (y_p X) (y_dep X + 1) ++
                       WriterValue.wvpieces (nth i l PjTree.JNull) (y_p X) (y_dep X + 1)
  | PjTree.JObj l => WriterValue.wcomma i ++ WriterValue.wind (y_p X) (y_dep X + 1) ++
                       WriterSpec.spieces (fst (nth i l ([], PjTree.JNull))) ++ [WriterValue.wsep (y_p X)] ++
                       WriterValue.wvpieces (snd (nth i l ([], PjTree.JNull))) (y_p X) (y_dep X + 1)
  | _ => []
  end.
Definition wvl_rest (X : wvx) (j : nat) : list (list Z) :=
  match y_t X with
  | PjTree.JArr l => wv_arr_go (y_p X) (y_dep X) j (skipn j l) ++ WriterValue.wind (y_p X) (y_dep X) ++ [[93]]
  | PjTree.JObj l => wv_obj_go (y_p X) (y_dep X) j (skipn j l) ++ WriterValue.wind (y_p X) (y_dep X) ++ [[125]]
  | _ => []
  end.

Lemma wvl_done_S : forall X i, (i < wv_nitems (y_t X))%nat -> wv_done X (S i) = wv_done X i ++ wvl_item X i.
Proof.
intros X i Hi. unfold wv_done, wvl_item.
destruct (y_t X) as [| | | txt bits | s | l | l]; cbn [wv_nitems] in Hi; try lia.
- rewrite (wvl_firstn_S l i PjTree.JNull Hi), wv_arr_go_app, firstn_length_le by lia.
  cbn [wv_arr_go app Nat.add]. rewrite app_nil_r. reflexivity.
- rewrite (wvl_firstn_S l i ([], PjTree.JNull) Hi), wv_obj_go_app, firstn_length_le by lia.
  destruct (nth i l ([], PjTree.JNull)) as [k x]. cbn [wv_obj_go app Nat.add fst snd]. rewrite app_nil_r.
  reflexivity.
Qed.

Lemma wvl_split : forall X j, (0 < wv_nitems (y_t X))%nat -> (j <= wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = wv_done X j ++ wvl_rest X j.
Proof.
intros X j Hn Hj. unfold wv_done, wvl_rest.
destruct (y_t X) as [| | | txt bits | s | l | l]; cbn [wv_nitems] in Hn, Hj; try lia.
- rewrite wv_arr_pieces.
  assert (Hm : (match l with [] => [] | _ :: _ => WriterValue.wind (y_p X) (y_dep X) end) =
               WriterValue.wind (y_p X) (y_dep X)) by (destruct l; [cbn in Hn; lia | reflexivity]).
  rewrite Hm. rewrite <- (firstn_skipn j l) at 1. rewrite wv_arr_go_app, firstn_length_le by lia.
  cbn [app Nat.add]. rewrite !app_assoc. reflexivity.
- rewrite wv_obj_pieces.
  assert (Hm : (match l with [] => [] | _ :: _ => WriterValue.wind (y_p X) (y_dep X) end) =
               WriterValue.wind (y_p X) (y_dep X)) by (destruct l; [cbn in Hn; lia | reflexivity]).
  rewrite Hm. rewrite <- (firstn_skipn j l) at 1. rewrite wv_obj_go_app, firstn_length_le by lia.
  cbn [app Nat.add]. rewrite !app_assoc. reflexivity.
Qed.

(* the pieces around item i: what precedes it and what follows it *)
Lemma wvl_split_item : forall X i, (i < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = wv_done X i ++ wvl_item X i ++ wvl_rest X (S i).
Proof.
intros X i Hi. rewrite (wvl_split X (S i)) by lia. rewrite (wvl_done_S X i Hi), app_assoc. reflexivity.
Qed.

(* after the last item: the indent at dep and the closing bracket *)
Lemma wvl_rest_end : forall X, wvl_rest X (wv_nitems (y_t X)) =
  WriterValue.wind (y_p X) (y_dep X) ++ [[if wv_tagc (y_t X) =? 6 then 125 else 93]] \/
  wv_nitems (y_t X) = 0%nat /\ wvl_rest X 0 = [].
Proof.
intros X. unfold wvl_rest, wv_nitems, wv_tagc.
destruct (y_t X) as [| | | txt bits | s | l | l]; try (right; split; reflexivity).
- left. rewrite skipn_all. reflexivity.
- left. rewrite skipn_all. reflexivity.
Qed.

(* a child's depth is below its container's *)
Lemma wvl_depth_arr : forall l i, (i < length l)%nat ->
  (PjTree.depth (nth i l PjTree.JNull) < PjTree.depth (PjTree.JArr l))%nat.
Proof.
intros l i Hi. cbn [PjTree.depth].
assert (H : Forall (fun k => (k <= list_max (map PjTree.depth l))%nat) (map PjTree.depth l))
  by (apply list_max_le; lia).
rewrite Forall_forall in H.
assert (Hin : In (PjTree.depth (nth i l PjTree.JNull)) (map PjTree.depth l)) by (apply in_map, nth_In; exact Hi).
pose proof (H _ Hin). lia.
Qed.

Lemma wvl_depth_obj : forall l i, (i < length l)%nat ->
  (PjTree.depth (snd (nth i l ([], PjTree.JNull))) < PjTree.depth (PjTree.JObj l))%nat.
Proof.
intros l i Hi. cbn [PjTree.depth].
set (f := fun m : list Z * PjTree.jv => let '(_, v) := m in PjTree.depth v).
assert (H : Forall (fun k => (k <= list_max (map f l))%nat) (map f l)) by (apply list_max_le; lia).
rewrite Forall_forall in H.
assert (Hin : In (f (nth i l ([], PjTree.JNull))) (map f l)) by (apply in_map, nth_In; exact Hi).
pose proof (H _ Hin) as Hle. subst f. cbn beta in Hle.
destruct (nth i l ([], PjTree.JNull)) as [k x]. cbn [snd]. lia.
Qed.

(* ---- the entry's layout facts the loop uses (fpre / fwin of wv_pre) ---- *)
Lemma wvl_pre_facts : forall X ch, wv_pre (fx := y_fx X) X ch -> 176 <= y_STK X ->
  ARx (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) /\
  YM05.alloc_ceiling + 176 <= y_sp X /\ y_sp X <= 2 ^ 47 /\ y_sp X mod 16 = 0 /\
  0 <= y_d X /\ y_d X mod 16 = 0 /\ y_sp X + y_d X <= ly_top (y_ly X) /\ ly_top (y_ly X) <= ly_stk_hi (y_ly X) /\
  ly_stk_hi (y_ly X) <= 2 ^ 47 /\ y_sp X + 64 <= ly_stk_hi (y_ly X) /\
  y_o X mod 8 = 0 /\ y_sp X <= y_o X /\ y_o X + 32 <= y_sp X + y_d X /\
  raZ (y_regs X) < YM05.alloc_ceiling /\ 0 <= WriterApp.w_cnt (y_st X) /\
  (WriterApp.w_cap (y_st X) <> 0 -> In (y_buf X, WriterApp.w_cap (y_st X)) (y_Lam X)) /\
  0 <= WriterApp.w_cap (y_st X).
Proof.
intros X ch Hpre HSTK.
destruct Hpre as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & Ho1 & Ho2 & HOUT & HLED & _).
pose proof HPRE as (HPREx & HRO & HTOP & HRAZ & _).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
unfold y_sp. split; [exact HAR|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
split; [exact Hd0|]. split; [exact Hd16|]. split; [exact Hdtop|]. split; [exact Htop2|]. split; [exact H47|].
split; [exact HTOP|]. split; [exact Hoal|]. split; [exact Ho1|]. split; [exact Ho2|]. split; [exact HRAZ|].
split; [exact (wv_led_cnt _ _ _ _ _ _ _ _ _ _ HLED)|]. split; [|lia].
intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin].
Qed.

(* a byte at or above the ceiling and off the struct is off the writer's footprint (the buffer is a block, below it) *)
Lemma wvl_nfp : forall {most own : Z} ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran o buf st a,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhWriter_out W mem Lam o buf st ->
  YM05.alloc_ceiling <= a -> ~ (o <= a < o + 32) ->
  ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a.
Proof.
intros most own ly S Hp W mem md Lam peak cnt fail ran o buf st a HAR HLED HOUT Ha Ho Hf.
unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hs | Hb]; [exact (Ho Hs)|].
unfold prhWriter_fp in Hb. destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [_|Hc]; [exact (inFP_nil a Hb)|].
destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [lia|].
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (HF _ Hin) as (_ & Hbl & _). cbn [fst snd] in Hbl.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & _ & Hce & _).
destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
Qed.

(* the entry footprint opens no sink *)
Lemma wvl_fp_closed : forall X ch, wv_pre (fx := y_fx X) X ch -> ~ YI16.sink_open_fp (y_FP X).
Proof.
intros X ch Hpre.
destruct Hpre as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & Ho1 & Ho2 & HOUT & HLED & _).
pose proof HPRE as ((HAR & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
pose proof cf_head_nonneg as Hh0.
unfold y_FP. apply wv_cfp_closed; [unfold y_sp in *; lia|].
intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia|].
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (HF _ Hin) as (_ & Hbl & _). cbn [fst snd] in Hbl.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hbl) as (_ & H4096 & _). lia.
Qed.

(* ---- what a run from a seated join keeps: every byte (the seated state has no write window) ---- *)
Lemma wvl_nowin : forall E tg kr (m0 m1 : word -> option byte) (H : word -> bool),
  frame_of E (wvl_mem tg kr) (mrestrict H m0) (mrestrict H m1) ->
  forall a, aview SEGS H m1 a = aview SEGS H m0 a.
Proof.
intros E tg kr m0 m1 H Hfr a. apply (aview_eq_of SEGS). apply Hfr.
intros (r & Hr & Ha). unfold wvl_mem in Hr.
destruct kr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [unfold wvl_frame, wvh_node, wvh_key in Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]);
  destruct Hr.
Qed.

(* the seated registers' atoms are all below 55 *)
Lemma wvl_regs_atoms : forallb (fun r : bv 5 => sv_atoms_lt 55 (sr_get wvh_regs r)) all_regs = true.
Proof. vm_compute. reflexivity. Qed.

(* a state whose callee-saved registers are the seated ones (syntactically), at an env that agrees with the seat's
   below 55, has the seat's callee-saved values *)
Lemma wvl_aregs : forall E E' (srs : list sv) regs0 regs1,
  (forall r, getr regs1 r = sv_denot E' (sr_get srs r)) -> regs_ok E wvh_regs regs0 -> env_agree 55 E E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get wvh_regs r)) CALLEE_SAVED = true ->
  aregs_preserved regs0 regs1.
Proof.
intros E E' srs regs0 regs1 HS HR HA Hcs r Hr.
assert (Hin : In (Z_to_bv 5 r : bv 5) CALLEE_SAVED).
{ unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (H : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
              r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H as [->|H]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (HS (Z_to_bv 5 r)), Hq, (HR (Z_to_bv 5 r)).
apply (sv_denot_agree 55 E E'); [exact HA|].
pose proof wvl_regs_atoms as Ha. rewrite forallb_forall in Ha. apply Ha. apply all_regs_in.
Qed.

Lemma wvl_agree_ext : forall E K ws, (55 <= K)%nat -> env_agree 55 E (extK E K ws).
Proof.
intros E K ws HK. destruct (env_agree_extK E K ws) as [HA HD]. split; [intros n Hn; apply HA; lia | exact HD].
Qed.

Lemma wvl_agree_trans : forall E1 E2 E3, env_agree 55 E1 E2 -> env_agree 55 E2 E3 -> env_agree 55 E1 E3.
Proof.
intros E1 E2 E3 [A1 D1] [A2 D2]. split; [intros n Hn; rewrite (A2 n Hn); exact (A1 n Hn) | congruence].
Qed.

(* the env after a run (the engine's ewset's above the seat's 55 atoms) agrees with the seat's below 55 *)
Lemma wvl_agree_set : forall E E' k w, (55 <= k)%nat -> env_agree 55 E E' -> env_agree 55 E (ewset E' k w).
Proof.
intros E E' k w Hk [HA HD]. split; [intros n Hn; rewrite ew_ewset_other by lia; exact (HA n Hn) | exact HD].
Qed.

End l0.

Ltac wvl_agree := repeat (apply wvl_agree_set; [lia|]); first [apply env_agree_refl | apply wvl_agree_ext; lia].

Local Ltac wvl_cs := unfold acallee_saved; lia.

Section l0b. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
(* the item loop runs after the opening bracket's put: its runners take the journal at wle' (YC1fPx / YSRrG R forms) *)
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* the register and frame-word facts survive a keep of the frame and of the callee-saved registers *)
Lemma wvl_rf_keep : forall X i (W W' : world SEGS) regs regs' mem mem',
  wvl_rf X i W regs mem -> aregs_preserved regs regs' ->
  (forall a, y_sp X - 176 <= a < y_sp X -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  wvl_rf X i W' regs' mem'.
Proof.
intros X i W W' regs regs' mem mem' HRF HAP HK.
unfold wvl_rf in HRF |- *. cbv beta zeta in HRF |- *.
destruct HRF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168).
assert (RW : forall off, 0 <= off <= 168 ->
  rdword (aview SEGS (w_H W') mem') (y_sp X - 176 + off) = rdword (aview SEGS (w_H W) mem) (y_sp X - 176 + off))
  by (intros off Hoff; apply wv_rdword_ext; intros j Hj; apply HK; lia).
assert (RG : forall r : Z, acallee_saved r -> forall w, getr regs (Z_to_bv 5 r) = w -> getr regs' (Z_to_bv 5 r) = w)
  by (intros r Hr w Hw; rewrite (HAP r Hr); exact Hw).
split; [exact (RG 2 ltac:(wvl_cs) _ G2)|]. split; [exact (RG 3 ltac:(wvl_cs) _ G3)|].
split; [exact (RG 4 ltac:(wvl_cs) _ G4)|]. split; [exact (RG 8 ltac:(wvl_cs) _ G8)|].
split; [exact (RG 9 ltac:(wvl_cs) _ G9)|]. split; [exact (RG 18 ltac:(wvl_cs) _ G18)|].
split; [exact (RG 19 ltac:(wvl_cs) _ G19)|]. split; [exact (RG 20 ltac:(wvl_cs) _ G20)|].
split; [exact (RG 21 ltac:(wvl_cs) _ G21)|]. split; [exact (RG 22 ltac:(wvl_cs) _ G22)|].
split; [exact (RG 23 ltac:(wvl_cs) _ G23)|]. split; [exact (RG 24 ltac:(wvl_cs) _ G24)|].
split; [exact (RG 25 ltac:(wvl_cs) _ G25)|]. split; [exact (RG 26 ltac:(wvl_cs) _ G26)|].
split; [exact (RG 27 ltac:(wvl_cs) _ G27)|].
repeat (split; [rewrite RW by lia; assumption|]). rewrite RW by lia. assumption.
Qed.

(* wv_common across a run that writes nothing: the journal and Pm are the runner's, the rest is kept *)
Lemma wvl_common_run : forall X P lyc Sc Hpc Wc memc mdc kc mem' md',
  wv_common X P lyc Sc Hpc Wc memc mdc kc ->
  0 <= y_o X -> y_o X + 32 <= 2 ^ 64 ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (y_STK X + y_d X)
    (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc mem' md' kc ->
  Pm mem' ->
  (forall a, aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a) ->
  wv_common X P lyc Sc Hpc Wc mem' md' kc.
Proof.
intros X P lyc Sc Hpc Wc memc mdc kc mem' md' Hc Ho0 Ho64 HJ' HPm' HK.
destruct Hc as (HJ & HKW & _ & (ok & ranc & bufc & Lamc & peakc & Hoks & HG & HOUT & HLED & HBLK & Hpos) & Hroom & HRO & HZ
  & HF).
pose proof (ajxR_ar HJ) as HAR.
assert (HKP : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a)
  by (intros a _ _; apply HK).
split; [exact HJ'|]. split; [intros a Ha Hf; rewrite HK; exact (HKW a Ha Hf)|]. split; [exact HPm'|].
split.
- exists ok, ranc, bufc, Lamc, peakc. split; [exact Hoks|]. split; [exact HG|]. split.
  + eapply (wv_out_keep lyc Sc Hpc Wc Wc memc mem' mdc Lamc peakc _ _ ranc (y_o X) bufc _ (fun _ => False));
      [exact HAR | exact HLED | exact HOUT | exact HKP | intros a _ [] | intros a Ha; split; [lia | intros []]].
  + split; [|split; [exact HBLK | exact Hpos]].
    eapply (wv_led_keep lyc Sc Hpc Wc mdc memc mem' Lamc peakc _ _ ranc (fun _ => False));
      [exact HAR | exact HLED | exact HKP | intros a _ []].
- split; [exact Hroom|].
  split; [apply (wv_arodata_keep Wc Wc memc mem' (fun _ => False)); [exact HRO | exact HKP | intros a _ []] |].
  exact (conj HZ HF).
Qed.

(* ---- the stack each inner call needs fits under write_value's own frame ---- *)
Lemma wvl_stk : forall n', STK_put + 176 <= STK_write_value (S n') /\ STK_indent + 176 <= STK_write_value (S n') /\
  STK_put_string + 176 <= STK_write_value (S n') /\ STK_write_value n' + 176 <= STK_write_value (S n') /\
  176 <= STK_write_value n'.
Proof.
intros n'. unfold STK_write_value.
assert (HF : pi_frame F_write_value = 176) by (vm_compute; reflexivity). rewrite !HF.
assert (H1 : STK_put <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
assert (H2 : STK_indent <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
assert (H3 : STK_put_string <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
assert (H4 : 0 <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
rewrite !Nat2Z.inj_succ. lia.
Qed.

(* the stack top of the journal's current layout is the entry's *)
Lemma wvl_stkhi : forall {R : world SEGS -> world SEGS -> Prop} STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc
    kc,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc ->
  ly_stk_hi lyc = ly_stk_hi ly.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc HJ.
pose proof (ajxR_ly HJ) as Hly. destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _). exact Eshi.
Qed.

(* eight visible bytes form a word *)
Lemma wvl_rdword_some : forall (rd : Z -> option Z) a, (forall j, 0 <= j < 8 -> rd (a + j) <> None) ->
  exists w, rdword rd a = Some w.
Proof.
intros rd a H. unfold rdword.
destruct (rd a) as [b0|] eqn:E0; [| exfalso; apply (H 0); [lia | rewrite Z.add_0_r; exact E0]].
destruct (rd (a + 1)) as [b1|] eqn:E1; [| exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [| exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [| exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [| exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [| exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [| exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [| exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.

(* The kit's case-1 words below o (form (a)) at any join: case 1 from the entry's (the bytes [o - 16, o) are kept: in the
   caller window, off FP), case 2 (o = sp + 8) from the saved ra at R + 168 (below the ceiling by fpre) and the caller
   word at sp (present by fwin, kept) *)
Lemma wvl_owords : forall X ch i P lyc Sc Hpc Wc regs memc mdc kc,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  exists ra, rdword (aview SEGS (w_H Wc) memc) (y_o X - 8) = Some ra /\
    exists nfp, rdword (aview SEGS (w_H Wc) memc) (y_o X - 16) = Some nfp /\ nfp < YM05.alloc_ceiling.
Proof.
intros X ch i P lyc Sc Hpc Wc regs memc mdc kc HSTK Hpre (Hcom & Hrf).
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcut & HWIN & _ & _ & HOUT & HLED & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hca & _).
destruct Hcom as (_ & HKW & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HK16 : forall a, y_sp X <= a < y_o X ->
    aview SEGS (w_H Wc) memc a = aview SEGS (w_H (y_W X)) (y_mem X) a).
{ intros a Ha. apply HKW; [lia|]. unfold y_FP.
  eapply (wvl_nfp _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HAR0 HLED HOUT); lia. }
destruct Hcut as [H1 | H2].
- apply (wv_reca_keep (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) memc) (y_o X));
    [intros a Ha; apply HK16; lia | exact (Hca H1)].
- unfold wvl_rf in Hrf. cbv beta zeta in Hrf.
  destruct Hrf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F168).
  pose proof HWIN as (_ & _ & _ & Hdpres).
  destruct (wvl_rdword_some (aview SEGS (w_H (y_W X)) (y_mem X)) (y_sp X)) as [w Hw].
  { intros j Hj. apply (aview_some_of_apresent SEGS). apply Hdpres. unfold y_sp in *. lia. }
  exists w. split.
  + rewrite (wv_rdword_ext (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) memc)).
    * replace (y_o X - 8) with (y_sp X) by lia. exact Hw.
    * intros j Hj. apply HK16. lia.
  + exists (bv_unsigned (getr (y_regs X) 1)). split.
    * replace (y_o X - 16) with (y_sp X - 176 + 168) by lia. exact F168.
    * exact HRAZ.
Qed.

(* ---- THE MODEL-RUN POSITION AT A JOIN: the container's entry list (wv_pre's prh_run_at conjunct), and a callee's own entry
   list at the exact advance after the pieces P under the outcomes ok (all granted after P, or none if the writer
   failed in P: a failed writer makes no event) ---- *)
Lemma wvl_pre_ev : forall X ch, wv_pre (fx := y_fx X) X ch ->
  prh_run_at (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))).
Proof.
intros X ch Hpre.
destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & Hev & _).
exact Hev.
Qed.

Lemma wvl_run_at_mid : forall rp_sm rp_x rp_os rp_i st PP P2 P3 ok,
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (PP ++ P2 ++ P3)) ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st PP))%nat
    (prhWriter_evs [] (prhWriter_putN ok st PP) P2).
Proof.
intros rp_sm rp_x rp_os rp_i st PP P2 P3 ok HE.
destruct (prhW_putN_ok_or_failed PP ok st) as [Est|Ef].
- assert (HL : length (prhWriter_evs ok st PP) = length (prhWriter_evs [] st PP)).
  { pose proof (prhW_evs_len PP ok st) as L1. pose proof (prhW_evs_len PP [] st) as L2.
    assert (Hk : prhWriter_k ok st PP = prhWriter_k [] st PP) by (unfold prhWriter_k; rewrite Est; reflexivity).
    rewrite Est in L1. lia. }
  rewrite HL, Est.
  rewrite prhWriter_evs_app0 in HE. apply prh_run_at_app_iff in HE. destruct HE as (_ & HE).
  rewrite prhWriter_evs_app0 in HE. apply prh_run_at_app_iff in HE. destruct HE as (HE & _). exact HE.
- rewrite (prhWriter_evs_failed P2 [] (prhWriter_putN ok st PP) Ef). unfold prh_run_at. reflexivity.
Qed.

(* ---- AFTER AN INNER CALL: the join at P ++ Q, from the join at P and the callee's post (its journal from the entry,
   its window keep from the call memory, the preserved registers, the room, the writer's run Q, the memnorm keep) ---- *)
Lemma wvl_after : forall X ch i P Q lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc
    ly2 S2 Hp2 W2 regs2 mem2 md2 k2 lo hi,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  prh_oks ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P)
    (prhWriter_reqs ok (y_st X) P) (y_most X) (y_ran X) ranc ->
  prh_granted ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) ->
  prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
    (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) ->
  prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
    (prhWriter_putN ok (y_st X) P) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (y_STK X + y_d X)
    (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] ly2 S2 Hp2 W2 mem2 md2 k2 ->
  lo <= y_sp X - 176 -> y_sp X + y_d X <= hi ->
  (forall a, lo <= a < hi -> ~ inFP (prhWriter_cfp (y_o X) bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P))) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  aregs_preserved regs regs2 ->
  room_live_cf S2 ->
  prhWriter_ret_pos B (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpH0 X) (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat
    lyc Sc Lamc peakc ranc (y_most X) (y_own X) (y_o X) bufc (prhWriter_putN ok (y_st X) P) Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  forall fx' : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
  wvl_st (fx := fx') X i (P ++ Q) ly2 S2 Hp2 W2 regs2 mem2 md2 k2.
Proof.
intros X ch i P Q lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 lo hi
  HSTK Hpre (Hcom & Hrf) Hoks HG HOUT HLED HBLK HJ2 Hlo Hhi HKC HAP Hroom2 HRP HMN fx' HZ2 HF2.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as ((_ & HRO0 & _) & _).
destruct Hcom as (HJc & HKW & HPmc & _ & _ & HROc & HZc & HFc).
pose proof (ajxR_ar HJc) as HARc.
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HNF : forall a, YM05.alloc_ceiling <= a -> ~ (y_o X <= a < y_o X + 32) ->
    ~ inFP (prhWriter_cfp (y_o X) bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P))) a)
  by (intros a Ha Ho; exact (wvl_nfp lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (y_o X) bufc _ a HARc HLED HOUT Ha Ho)).
split.
- split; [exact HJ2|].
  split.
  { intros a Ha Hf. rewrite (HKC a ltac:(lia)); [exact (HKW a Ha Hf)|].
    apply HNF; [lia|]. intros Ho. apply Hf. unfold y_FP, prhWriter_cfp. apply inFP_cons. left. exact Ho. }
  split; [exact (PCALL memc mem2 HMN HPmc)|].
  split.
  { destruct (wv_ret_pos_app (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpH0 X) (y_rpi X) _ (y_ly X) (y_S X) (y_Lam X)
      (y_peak X) (y_ran X) (y_o X) (y_buf X) (y_st X) P Q ok ranc bufc Lamc peakc lyc Sc Hpc Wc memc
      ly2 S2 Hp2 W2 regs2 mem2 md2 Hcnt eq_refl Hoks HG HOUT HLED HBLK HRP) as (ok' & HR & G' & hist' & Hpos').
    destruct (prhWriter_blk_of_ret_ok B ok' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR G')
      as (ran' & buf' & Lam' & peak' & HR1 & HR2 & HR3 & HR4).
    exists ok', ran', buf', Lam', peak'.
    split; [exact HR1|]. split; [exact G'|]. split; [exact HR2|]. split; [exact HR3|]. split; [exact HR4|].
    exists hist'. exact Hpos'. }
  split; [exact Hroom2|].
  split; [exact (wv_arodata_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 (wvl_fp_closed X ch Hpre) HRO0)|].
  split; [exact HZ2 | exact (wv_fk_trans _ _ _ HFc HF2)].
- apply (wvl_rf_keep X i Wc W2 regs regs2 memc mem2 Hrf HAP).
  intros a Ha. apply HKC; [lia|]. apply HNF; [lia|]. lia.
Qed.

(* ---- AN INNER CALL SITE: what every inner call (put / indent / put_string / write_value at the frame base
   R = sp - 176, oc = - (d + 176)) takes, from wv_pre and the join at the call memory, for a run of pieces P2 that the
   container's pieces continue after P ---- *)
Lemma wvl_ctx : forall n' X ch i P P2 P3 lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ P2 ++ P3 ->
  exists ok ranc bufc Lamc peakc rpi rph ra1 nfp1,
    prh_oks ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P)
      (prhWriter_reqs ok (y_st X) P) (y_most X) (y_ran X) ranc /\
    prh_granted ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) /\
    prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) /\
    prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
      (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) /\
    prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
      (prhWriter_putN ok (y_st X) P) /\
    rpi = (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat /\
    PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph Sc /\
    prh_run_at (y_rpsm X) (y_rpx X) (y_rpos X) rpi (prhWriter_evs [] (prhWriter_putN ok (y_st X) P) P2) /\
    room_live_cf Sc /\
    arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
    ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (y_STK X + y_d X)
      (y_sp X + y_d X) (y_FP X)
      (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc /\
    rdword (aview SEGS (w_H Wc) memc) (y_o X - 8) = Some ra1 /\
    rdword (aview SEGS (w_H Wc) memc) (y_o X - 16) = Some nfp1 /\ nfp1 < YM05.alloc_ceiling /\
    spZ regs = y_sp X + y_d X + - (y_d X + 176) /\ (- (y_d X + 176)) mod 16 = 0 /\ - (y_d X + 176) <= 0 /\
    y_sp X + y_d X + - (y_d X + 176) + 64 <= ly_stk_hi lyc /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ s0Z regs = y_o X /\
    y_sp X + y_d X + - (y_d X + 176) + 16 <= y_o X /\ y_o X + 32 <= y_sp X + y_d X /\
    Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok (y_st X) P))) + Z.of_nat (length (concat P2)) + 1
      <= prhWriter_WMAX /\
    PRH_Base.prh_cons_from (y_rpsm X) (y_rpx X) (y_rpos X) rpi
      (length (prhWriter_evs [] (prhWriter_putN ok (y_st X) P) P2)) /\
    prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok (y_st X) P) P2) /\
    fp_sub_xW B (y_STK X + y_d X) (y_sp X + y_d X) (y_FP X)
      (prhWriter_cfp (y_o X) bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P))) (y_ly X) (y_S X) [] lyc Sc /\
    (WriterApp.w_cap (prhWriter_putN ok (y_st X) P) <> 0 ->
       In (bufc, WriterApp.w_cap (prhWriter_putN ok (y_st X) P)) Lamc) /\
    0 <= WriterApp.w_cap (prhWriter_putN ok (y_st X) P) /\
    prh_univ_closure B CTX0 /\ prhWriter_WMAX + cf_head < cf_malloc_max /\
    Z.of_nat (length (frames Sc)) < fs_frames 0.
Proof.
intros n' X ch i P P2 P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
destruct (wvl_owords X ch i P lyc Sc Hpc Wc regs memc mdc kc HSTK Hpre Hst) as (ra1 & Hra1 & nfp1 & Hnfp1 & Hnfpc).
pose proof Hpre as (_ & _ & _ & Hcl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HLED0 & _ & _ & _ & _ &
  _ & _ & Hfr0 & Hwmax & Hhead & Hlive & _ & Hcons0 & _).
assert (Hbufb : WriterApp.w_cap (y_st X) <> 0 ->
    In (y_buf X - cf_head, WriterApp.w_cap (y_st X) + cf_head) (ablocks B (y_ly X) (y_S X))).
{ intros Hc. destruct (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED0 _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
destruct Hst as (Hcom & Hrf).
destruct Hcom as (HJc & HKW & HPmc & (ok & ranc & bufc & Lamc & peakc & Hoks & HG & HOUT & HLED & HBLK & (rph & Hrp)) &
  Hroom & HROc & _).
pose proof (ajxR_ar HJc) as HARc.
unfold wvl_rf in Hrf. cbv beta zeta in Hrf.
destruct Hrf as (G2 & G3 & G4 & G8 & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
pose proof HOUT as (_ & _ & Hcapc & _).
exists ok, ranc, bufc, Lamc, peakc, (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat, rph, ra1, nfp1.
split; [exact Hoks|]. split; [exact HG|]. split; [exact HOUT|]. split; [exact HLED|]. split; [exact HBLK|].
split; [reflexivity|]. split; [exact Hrp|].
split; [apply (wvl_run_at_mid _ _ _ _ _ P P2 P3); rewrite <- Hpcs; exact (wvl_pre_ev X ch Hpre)|].
split; [exact Hroom|]. split; [exact HROc|]. split; [exact HJc|].
split; [exact Hra1|]. split; [exact Hnfp1|]. split; [exact Hnfpc|].
split.
{ assert (E2 : spZ regs = bv_unsigned (w64 (y_sp X - 176))) by (unfold spZ; f_equal; exact G2).
  rewrite E2. unfold w64. rewrite unsigned_lit_small; unfold y_sp in *; lia. }
split; [apply wv_neg_mod16; rewrite Z.add_mod, Hd16 by lia; reflexivity|].
split; [lia|].
split; [rewrite (wvl_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc); lia|].
split; [exact G3|]. split; [exact G4|].
split.
{ assert (E8 : s0Z regs = bv_unsigned (w64 (y_o X))) by (unfold s0Z; f_equal; exact G8).
  rewrite E8. unfold w64. rewrite unsigned_lit_small; [reflexivity | unfold y_sp in *; lia]. }
split; [lia|]. split; [exact Ho2|].
split; [apply (wv_wmax_next ok (y_st X) P P2 P3); rewrite <- Hpcs; exact Hwmax|].
split; [rewrite Hpcs in Hcons0; exact (wv_cons_next _ _ _ _ _ P P2 P3 ok Hcons0)|].
split; [rewrite Hpcs in Hlive;
        exact (wv_live_next _ _ _ _ _ _ _ _ _ _ _ ok P P2 P3 Hcap0 Hbufb HBLK Hlive)|].
split; [exact (wv_fp_sub (y_STK X + y_d X) (y_sp X + y_d X) (y_ly X) (y_S X) lyc Sc Hpc Wc memc mdc (y_o X)
          (y_Lam X) (y_peak X) (y_buf X) (y_st X) Lamc peakc bufc _ HARc Hcap0 HBLK)|].
split.
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
split; [lia|]. split; [exact Hcl|]. split; [exact Hhead|].
pose proof (ajxR_frs HJc) as Hfrs. rewrite Hfrs. cbn [app]. exact Hfr0.
Qed.

(* THE RECURSIVE CALL over the text (twrite_value_specI is the batch kit's twrite_value_specX: wv_call_self's twin) *)
Lemma wvl_call_selfI : forall {gm go : Z} (n' : nat) rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o v2 pretty dep buf (st : WriterApp.wst) (t2 : PjTree.jv) D2
    Lam peak ran oc,
  twrite_value_specI n' ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0 mem0
    md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_write_value n' - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 v2 -> getr regsc 12 = w64 pretty -> getr regsc 13 = w64 dep ->
  0 <= pretty < 2 ^ 64 -> 0 <= dep < 2 ^ 31 -> dep + Z.of_nat (PjTree.depth t2) <= 2 ^ 31 - 1 ->
  (PjTree.depth t2 <= n')%nat ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gm go ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v2 t2 D2 ->
  ((sp0 + oc <= v2 /\ v2 + 56 <= ly_stk_hi lyc) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v2 /\ v2 + 56 <= x + y) \/ prhWriter_in_frame lyc Sc v2) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v2 56 ->
  prhWriter_tree_vis W memc D2 ->
  (forall a k0, In (a, k0) D2 -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v2 D2 x) ->
  Z.of_nat (length (frames Sc)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep))) ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) ->
  fp_sub_xW B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_write_value)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       YK0o.frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc sp0 FP ly S Hp W0
         mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
         (STK_write_value n' + - oc) (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\ pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) v2 t2 D2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gm go o buf st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)
            ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces t2 (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros gm go n' rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc
  raw ra1 nfp1 o v2 pretty dep buf st t2 D2 Lam peak ran oc
  IH HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab HFRM Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos4 Hcl H10 H11 H12 H13 Hpr Hdep Hdep2
  Hdn Ho1 Ho2 Hout Hled Hev Hnode Hloc Hra56 Hvis HD Hoff Hfr0 Hwmax Hhead Hcons Hlive Hfp.
exact (wv_call_self (fx := fx) n' rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W
  memc mdc k regsc raw ra1 nfp1 o v2 pretty dep buf st t2 D2 Lam peak ran oc IH HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw
  Hra4 Hrab HFRM Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos4 Hcl H10 H11 H12 H13 Hpr Hdep Hdep2 Hdn Ho1 Ho2 Hout Hled Hev
  Hnode Hloc Hra56 Hvis HD Hoff Hfr0 Hwmax Hhead Hcons Hlive Hfp).
Qed.

(* ---- the tree at a join: the node and its i-th item / member ---- *)
Lemma wvl_items_nth : forall (Pn : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D i,
  pj_itemsR Pn a l D -> (i < length l)%nat ->
  exists D1 Dpre Dpost, D = Dpre ++ D1 ++ Dpost /\ Pn (a + 56 * Z.of_nat i) (nth i l PjTree.JNull) D1.
Proof.
intros Pn l. induction l as [|u r IH]; intros a D i H Hi; cbn [length] in Hi; [lia|].
destruct H as (D1 & D2 & -> & H1 & H2). destruct i as [|i].
- exists D1, [], D2. split; [reflexivity|]. rewrite Z.add_0_r. exact H1.
- destruct (IH (a + 56) D2 i H2 ltac:(lia)) as (D3 & Dp & Dq & -> & H3).
  exists D3, (D1 ++ Dp), Dq. split; [rewrite <- app_assoc; reflexivity|].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact H3.
Qed.

Lemma wvl_mems_nth : forall m lblk (Pn : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i,
  pj_memsR SEGS m lblk Pn a ka l D -> (i < length l)%nat ->
  exists x k D1 Dpre Dpost, D = Dpre ++ (x, k) :: D1 ++ Dpost /\ rd_u64 SEGS m (ka + 8 * Z.of_nat i) x /\
    pj_cstrR SEGS m lblk x k (fst (nth i l ([], PjTree.JNull))) /\
    Pn (a + 56 * Z.of_nat i) (snd (nth i l ([], PjTree.JNull))) D1.
Proof.
intros m lblk Pn l. induction l as [|[nm u] r IH]; intros a ka D i H Hi; cbn [length] in Hi; [lia|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). destruct i as [|i].
- exists x, k, D1, [], D2. split; [reflexivity|]. rewrite !Z.add_0_r. split; [exact Hx|]. split; [exact Hc | exact H1].
- destruct (IH (a + 56) (ka + 8) D2 i H2 ltac:(lia)) as (x3 & k3 & D3 & Dp & Dq & -> & H3x & H3c & H3).
  exists x3, k3, D3, ((x, k) :: D1 ++ Dp), Dq. split; [cbn [app]; rewrite <- app_assoc; reflexivity|].
  replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact H3x|]. split; [exact H3c | exact H3].
Qed.

(* the tree at a join's memory: the entry's, its footprint kept by the journal and the window clause *)
Lemma wvl_node_cur : forall X ch P lyc Sc Hpc Wc memc mdc kc,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wv_common X P lyc Sc Hpc Wc memc mdc kc ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X) /\
  prhWriter_tree_vis Wc memc (y_D X) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (y_v X) 56.
Proof.
intros X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as ((HPREx & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HLED0 & HNODE &
  HLOC & HRA & HTV & HD & Hoff & _).
pose proof HPREx as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hcom as (HJc & HKW & _ & (ok & ranc & bufc & Lamc & peakc & Hoks & HG & HOUT & HLED & HBLK & _) & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (Hbufb : WriterApp.w_cap (y_st X) <> 0 ->
    In (y_buf X - cf_head, WriterApp.w_cap (y_st X) + cf_head) (ablocks B (y_ly X) (y_S X))).
{ intros Hc. pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED0 _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
assert (HLK : forall a k, In (a, k) (y_Lam X) -> a <> y_buf X -> In (a, k) Lamc).
{ intros a k Hin Hab.
  exact (proj1 (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ HLED) HBLK a k Hin Hab)). }
split; [|split].
- apply (wv_nodeR_keep (y_W X) Wc (y_mem X) memc (y_Lam X) (y_v X) (y_t X) (y_D X) HNODE).
  + intros x Hx. exact (proj1 (wv_foot_keep (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X)
      (y_STK X) (y_STK X + y_d X) (y_d X) (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)) (y_Lam X) (y_peak X)
      _ _ (y_ran X) (y_v X) (y_D X) lyc Sc Hpc Wc memc mdc kc HSTK Hd0 HAR0 Hstk HLED0 HLOC HD Hoff Hcap0 Hbufin
      HJc HKW x Hx)).
  + intros x Hx. exact (proj2 (wv_foot_keep (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X)
      (y_STK X) (y_STK X + y_d X) (y_d X) (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)) (y_Lam X) (y_peak X)
      _ _ (y_ran X) (y_v X) (y_D X) lyc Sc Hpc Wc memc mdc kc HSTK Hd0 HAR0 Hstk HLED0 HLOC HD Hoff Hcap0 Hbufin
      HJc HKW x Hx)).
- eapply (wv_tvis_cur (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_buf X) (y_D X)
    (y_STK X + y_d X) (y_sp X + y_d X) (y_o X) (WriterApp.w_cap (y_st X)) lyc Sc Hpc Wc memc mdc kc Lamc peakc
    _ _ ranc HAR0 HTV HD).
  + intros a k Hin. pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED0 _ Hin) as (_ & Hbl & _). exact Hbl.
  + exact HJc.
  + exact HLED.
  + exact HLK.
  + unfold y_sp in *. lia.
  + exact Hbufb.
- eapply (wv_ra_cur (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_buf X) (y_v X) (y_regs X)
    (y_STK X) (y_d X) (y_o X) (WriterApp.w_cap (y_st X)) lyc Sc Hpc Wc memc mdc kc Lamc peakc _ _ ranc
    HAR0 Hstk HRA HLOC HJc HLED HLK); [unfold y_sp in *; lia | exact Hbufb].
Qed.

(* the tree under a wider block predicate (the current ledger keeps every tree block) *)
Lemma wvl_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (Pn Pn' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR SEGS m lblk Pn a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  (forall nm u a' D1, In (nm, u) l -> incl D1 D -> Pn a' u D1 -> Pn' a' u D1) ->
  pj_memsR SEGS m lblk' Pn' a ka l D.
Proof.
intros m lblk lblk' Pn Pn' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in H |- *;
  [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & (Hl & Hc) & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [split; [apply HL; [left; reflexivity | exact Hl] | exact Hc]|].
split; [apply (HP nm u a D1 (or_introl eq_refl)); [intros y Hy; right; apply in_or_app; left; exact Hy | exact H1]|].
apply (IH (a + 56) (ka + 8) D2 H2).
- intros x' k' Hin Hl'. apply HL; [right; apply in_or_app; right; exact Hin | exact Hl'].
- intros nm' u' a' D1' Hin Hinc HP'. apply (HP nm' u' a' D1' (or_intror Hin)); [|exact HP'].
  intros y Hy. right. apply in_or_app. right. exact (Hinc y Hy).
Qed.

Lemma wvl_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR SEGS m lblk p t D ->
  (forall a k, In (a, k) D -> lblk a k -> lblk' a k) -> pj_nodeR SEGS m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [|exact Hc]. apply HL; [subst D; left; reflexivity | exact Hl].
- destruct Hb as (E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [|exact Hc]. apply HL; [subst D; left; reflexivity | exact Hl].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hlk)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | exact Hlk]. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros a k Hin Hl. apply HL; [apply HDi; apply Hinc; exact Hin | exact Hl].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hlk1 & Hlk2)]; [left; exact Hz | right; split; [exact Hp|]].
    split; [apply HL; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | exact Hlk1]
           | apply HL; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; right; left; reflexivity | exact Hlk2]]. }
  exists Di. split; [exact ED|].
  apply (wvl_mems_lblk m lblk lblk' (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') members kids keys Di Hi).
  + intros x k Hin Hl. apply HL; [apply HDi; exact Hin | exact Hl].
  + intros nm u a' D1 Hin Hinc HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hin). cbn [snd] in IH.
    apply (IH m lblk lblk' a' D1 HP). intros a k Hin2 Hl. apply HL; [apply HDi; apply Hinc; exact Hin2 | exact Hl].
Qed.

(* the item i of a container: its value and (an object's) key *)
Definition wvl_child (X : wvx) (i : nat) : PjTree.jv :=
  match y_t X with
  | PjTree.JArr l => nth i l PjTree.JNull
  | PjTree.JObj l => snd (nth i l ([], PjTree.JNull))
  | _ => PjTree.JNull
  end.
Definition wvl_key (X : wvx) (i : nat) : list Z :=
  match y_t X with PjTree.JObj l => fst (nth i l ([], PjTree.JNull)) | _ => [] end.

(* ---- the node's fields and item i at a join's memory, from the tree there ---- *)
Lemma wvl_item_facts : forall X ch P lyc Sc Hpc Wc memc mdc kc i,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wv_common X P lyc Sc Hpc Wc memc mdc kc ->
  (i < wv_nitems (y_t X))%nat ->
  exists kids keys nn cap D1,
    val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 (wv_tagc (y_t X)) /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) kids /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) keys /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) nn /\
    nn = Z.of_nat (wv_nitems (y_t X)) /\ nn <= cap /\ 0 < cap /\
    In (kids, 56 * cap) (y_D X) /\
    pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) (kids + 56 * Z.of_nat i) (wvl_child X i) D1 /\
    (forall b, In b D1 -> In b (y_D X)) /\
    (wv_tagc (y_t X) = 5 -> keys = 0) /\
    (wv_tagc (y_t X) = 6 ->
       In (keys, 8 * cap) (y_D X) /\
       exists x k, In (x, k) (y_D X) /\ rd_u64 SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) x /\
         pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) x k (wvl_key X i)).
Proof.
intros X ch P lyc Sc Hpc Wc memc mdc kc i HSTK Hpre Hcom Hi.
destruct (wvl_node_cur X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom) as (HNODE & _ & _).
unfold wv_nitems, wvl_child, wvl_key, wv_tagc in *.
destruct (y_t X) as [| | | txt bits | s | l | l]; try (cbn in Hi; lia).
- destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
  destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
  destruct Hbody as (_ & Hkeys0 & Hn & Hncap & Hcb & Di & HDi & Hitems).
  destruct Hcb as [(Hc0 & _) | (Hcp & _)]; [lia|].
  destruct (wvl_items_nth _ l kids Di i Hitems Hi) as (D1 & Dp & Dq & EDi & HN1).
  replace (cap =? 0) with false in HDi by (symmetry; apply Z.eqb_neq; lia). cbn [app] in HDi.
  exists kids, keys, nn, cap, D1.
  split; [exact Vtg|]. split; [exact Hkids|]. split; [exact Hkeys|]. split; [exact Hnn|].
  split; [exact Hn|]. split; [exact Hncap|]. split; [exact Hcp|].
  split; [rewrite HDi; left; reflexivity|]. split; [exact HN1|].
  split; [intros b Hb; rewrite HDi, EDi; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
  split; [intros _; exact Hkeys0|].
  intros H. exfalso. cbn in H. lia.
- destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
  destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
  destruct Hbody as (_ & Hn & Hncap & Hcb & Di & HDi & Hmems).
  destruct Hcb as [(Hc0 & _) | (Hcp & _)]; [lia|].
  destruct (wvl_mems_nth _ _ _ l kids keys Di i Hmems Hi) as (x & k & D1 & Dp & Dq & EDi & Hx & Hcs & HN1).
  replace (cap =? 0) with false in HDi by (symmetry; apply Z.eqb_neq; lia). cbn [app] in HDi.
  exists kids, keys, nn, cap, D1.
  split; [exact Vtg|]. split; [exact Hkids|]. split; [exact Hkeys|]. split; [exact Hnn|].
  split; [exact Hn|]. split; [exact Hncap|]. split; [exact Hcp|].
  split; [rewrite HDi; left; reflexivity|]. split; [exact HN1|].
  split.
  { intros b Hb. rewrite HDi, EDi. right. right. apply in_or_app. right. right. apply in_or_app. left. exact Hb. }
  split; [intros H; exfalso; cbn in H; lia|].
  intros _. split; [rewrite HDi; right; left; reflexivity|].
  exists x, k. split; [rewrite HDi, EDi; right; right; apply in_or_app; right; left; reflexivity|].
  split; [exact Hx | exact Hcs].
Qed.

(* ---- THE FOUR INNER CALL SITES: from the join at the call memory (P), the call's argument registers and its return
   address, and the continuation at the return site (the join at P ++ the callee's pieces) ---- *)
Lemma wvl_site_put : forall n' X ch i P P3 slot bs ret lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  In (slot, bs) wv_lits ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ [bs] ++ P3 ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 (WV_STR slot) -> getr regs 12 = w64 (Z.of_nat (length bs)) ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, wvl_st X i (P ++ [bs]) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin X)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i P P3 slot bs ret lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hlit Hpcs H10 H11 H12 Hra Hrok
  Hra4 Hrac HK.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
pose proof (wv_common_float X P lyc Sc Hpc Wc memc mdc kc (proj1 Hst)) as (HZc & HFc).
destruct (wvl_ctx n' X ch i P [bs] P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HG & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hroom &
   HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax & Hcons & Hlive & Hfp &
   Hbufin & Hcap0 & Hcl & Hhead & Hfr0).
pose proof (ajxR_ar HJc) as HARc.
destruct (HLIT slot bs lyc Sc Hpc Wc memc mdc Hlit HARc HROc) as (Hsrc & Hkept & Himg).
assert (Hlen0 : 0 < Z.of_nat (length bs))
  by (unfold wv_lits in Hlit; cbn [In] in Hlit;
      repeat (destruct Hlit as [Hl | Hlit]; [injection Hl as <- <-; cbn; lia |]); destruct Hlit).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; lia).
assert (Hhome : prhWriter_src_home B lyc Sc Lamc bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P)) (WV_STR slot)
    (Z.of_nat (length bs)))
  by (eapply (wv_lit_home lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc bufc _ (WV_STR slot) (Z.of_nat (length bs))
        HARc HLED Hbufin Hcap0 Hlen0 Hkept);
      intros a Ha; replace a with (WV_STR slot + (a - WV_STR slot)) by lia; apply Himg; lia).
assert (Hwmax' : Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok (y_st X) P))) + Z.of_nat (length bs) + 1
    <= prhWriter_WMAX) by (cbn [concat] in Hwmax; rewrite app_nil_r in Hwmax; exact Hwmax).
eapply SRr'_bind.
{ exact (wv_call_put (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs (Z_to_bv 64 (BASE + ret))
    ra1 nfp1 (y_o X) (WV_STR slot) (Z.of_nat (length bs)) bufc (prhWriter_putN ok (y_st X) P) bs Lamc peakc ranc
    (- (y_d X + 176)) HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok ltac:(rewrite HB64; lia)
    ltac:(rewrite HB64; exact Hrac) HZc Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp (wv_pre_os4 X ch Hpre) Hcl H10 H11 H12
    Ho1 Ho2 HOUT HLED Hsrc
    eq_refl Hhome (wv_ev_first (y_rpsm X) (y_rpx X) (y_rpos X) rpi (prhWriter_putN ok (y_st X) P) bs [] Hev2)
    Hwmax' Hhead Hcons Hlive Hfp). }
cbv beta. intros W2 c2 _ (ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HKC & HAP &
  (Hroom2 & HPP & HRET) & HMN).
rewrite Hrpi in HPP.
apply (HK ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvl_after X ch i P [bs] lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc ly2 S2' Hp2 W2 regs2 mem2 md2
  (kc + k1) (y_sp X + y_d X + - (y_d X + 176))
  (y_sp X + y_d X + - (y_d X + 176) + - - (y_d X + 176)) ltac:(lia) Hpre Hst Hoks HG HOUT HLED HBLK HJ2 ltac:(lia) ltac:(lia)
  HKC HAP Hroom2
  (wv_ret_pos_one (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpH0 X) _ rph lyc Sc Hpc Wc memc Lamc peakc ranc (y_o X) bufc
     (prhWriter_putN ok (y_st X) P) bs ly2 S2' Hp2 W2 regs2 mem2 md2 HOUT HLED HPP HRET) HMN fx HZc (wv_fk_refl fx)).
Qed.

Lemma wvl_site_indent : forall n' X ch i P P3 depth ret lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ WriterValue.wind (y_p X) depth ++ P3 ->
  - 2 ^ 31 <= depth < 2 ^ 31 ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 (y_pretty X) -> getr regs 12 = w64 depth ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     wvl_st X i (P ++ WriterValue.wind (y_p X) depth) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin X)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (SIGMA AS_indent)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i P P3 depth ret lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs Hdepth H10 H11 H12 Hra Hrok
  Hra4 Hrac HK.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
pose proof (wv_common_float X P lyc Sc Hpc Wc memc mdc kc (proj1 Hst)) as (HZc & HFc).
destruct (wvl_ctx n' X ch i P (WriterValue.wind (y_p X) depth) P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst
  Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HG & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hroom &
   HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax & Hcons & Hlive & Hfp &
   Hbufin & Hcap0 & Hcl & Hhead & Hfr0).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; lia).
eapply SRr'_bind.
{ exact (wv_call_indent (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs
    (Z_to_bv 64 (BASE + ret)) ra1 nfp1 (y_o X) (y_pretty X) depth bufc (prhWriter_putN ok (y_st X) P) Lamc peakc
    ranc (- (y_d X + 176)) HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok ltac:(rewrite HB64; lia)
    ltac:(rewrite HB64; exact Hrac) HZc Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp (wv_pre_os4 X ch Hpre) Hcl H10 H11 H12
    Hpr Hdepth Ho1 Ho2 HOUT
    HLED Hev2 Hwmax Hhead Hcons Hlive Hfp). }
cbv beta. intros W2 c2 _ (ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HKC & HAP & HQI & HMN).
apply tindP_R_of in HQI. destruct HQI as (okp & histp & HRI).
rewrite Hrpi in HRI.
apply (HK ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvl_after X ch i P (WriterValue.wind (y_p X) depth) lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc
  ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 176))
  (y_sp X + y_d X + - (y_d X + 176) + - - (y_d X + 176)) ltac:(lia) Hpre Hst Hoks HG HOUT HLED HBLK HJ2 ltac:(lia) ltac:(lia)
  HKC
  HAP (tindP_room HRI)
  (ex_intro _ okp (conj (tindP_ret_ok HRI) (conj (tindP_granted HRI) (ex_intro _ histp (tindP_pos HRI)))))
  HMN fx HZc (wv_fk_refl fx)).
Qed.

(* an object's key i: put_string from the join at P; the key string is a tree block (x, k) of D at the call memory *)
Lemma wvl_site_put_string : forall n' X ch i P P3 x k ret lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ WriterSpec.spieces (wvl_key X i) ++ P3 ->
  In (x, k) (y_D X) ->
  pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) x k (wvl_key X i) ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 x ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     wvl_st (fx := fx') X i (P ++ WriterSpec.spieces (wvl_key X i)) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin X)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i P P3 x k ret lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs HxD Hcs H10 H11 Hra Hrok
  Hra4 Hrac HK.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
pose proof (wv_common_float X P lyc Sc Hpc Wc memc mdc kc (proj1 Hst)) as (HZc & HFc).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_node_cur X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre (proj1 Hst)) as (_ & HTVc & _).
destruct (wvl_ctx n' X ch i P (WriterSpec.spieces (wvl_key X i)) P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst
  Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HG & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hroom &
   HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax & Hcons & Hlive & Hfp &
   Hbufin & Hcap0 & Hcl & Hhead & Hfr0).
pose proof (ajxR_ar HJc) as HARc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _ & _ & _ & _ & HD & _).
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; lia).
destruct Hcs as (Hlam & Hlen & Hlen32 & Hrng & Hgs). unfold prh_lin in Hlam.
destruct (HD x k HxD) as (HinL & Hxb).
destruct (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ HLED) HBLK x k HinL Hxb)
  as (HinLc & Hxbc).
destruct (HTVc x k HxD) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (wv_cstr_blk (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_peak X) _ _ (y_ran X)
  Wc memc x k (wvl_key X i) HAR0 HLED0 HinL Hlen Hlen32 Hrng Hgs T3 T5 T6 T7) as Hcstr.
assert (Hkept : kept_at B Lamc x (Z.of_nat (length (wvl_key X i)) + 1))
  by (left; exists x, k; split; [exact HinLc | lia]).
assert (Hapart : WriterApp.w_cap (prhWriter_putN ok (y_st X) P) = 0 \/
    x + Z.of_nat (length (wvl_key X i)) + 1 <= bufc \/ bufc + WriterApp.w_cap (prhWriter_putN ok (y_st X) P) <= x).
{ destruct (wv_blk_apart lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc x k bufc
    (WriterApp.w_cap (prhWriter_putN ok (y_st X) P)) (Z.of_nat (length (wvl_key X i)) + 1) HARc HLED HinLc Hxbc
    Hbufin ltac:(lia) ltac:(lia)) as [H|[H|H]]; [left; exact H | right; left; lia | right; right; exact H]. }
eapply SRr'_bind.
{ exact (wv_call_put_string (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs
    (Z_to_bv 64 (BASE + ret)) ra1 nfp1 (y_o X) x bufc (prhWriter_putN ok (y_st X) P) (wvl_key X i) Lamc peakc ranc
    (- (y_d X + 176)) HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok ltac:(rewrite HB64; lia)
    ltac:(rewrite HB64; exact Hrac) HZc Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp (wv_pre_os4 X ch Hpre) Hcl H10 H11
    Ho1 Ho2 HOUT HLED Hcstr
    Hkept Hev2 Hapart Hfr0 Hwmax Hhead Hcons Hlive Hfp). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & HZ2 & HFK2 & HJ2 & _ & HKC & HAP &
  HQS & HMN).
apply tpusP_R_of in HQS. destruct HQS as (okp & histp & HRS).
rewrite Hrpi in HRS.
apply (HK fx' ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvl_after X ch i P (WriterSpec.spieces (wvl_key X i)) lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc
  ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 176))
  (y_sp X + y_d X + - (y_d X + 176) + - - (y_d X + 176)) ltac:(lia) Hpre Hst Hoks HG HOUT HLED HBLK HJ2 ltac:(lia) ltac:(lia)
  HKC
  HAP (tpusP_room HRS)
  (ex_intro _ okp (conj (tpusP_ret_ok HRS) (conj (tpusP_granted HRS) (ex_intro _ histp (tpusP_pos HRS)))))
  HMN fx' HZ2 HFK2).
Qed.

(* the item's value: the recursive call at depth n' (the interim text), from the join at P; the child node v2 is in
   a tree block, its blocks among the container's *)
Lemma wvl_site_self : forall n' X ch i P P3 v2 t2 D2 ret lyc Sc Hpc Wc regs memc mdc kc,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ WriterValue.wvpieces t2 (y_p X) (y_dep X + 1) ++ P3 ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) v2 t2 D2 ->
  (PjTree.depth t2 < PjTree.depth (y_t X))%nat ->
  (forall b, In b D2 -> In b (y_D X)) ->
  (exists x y, In (x, y) (y_D X) /\ x <= v2 /\ v2 + 56 <= x + y) ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 v2 -> getr regs 12 = w64 (y_pretty X) ->
  getr regs 13 = w64 (y_dep X + 1) ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     wvl_st (fx := fx') X i (P ++ WriterValue.wvpieces t2 (y_p X) (y_dep X + 1)) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin X)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (SIGMA AS_write_value)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i P P3 v2 t2 D2 ret lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hst Hpcs HN2 Hdt2 HD2 Hv2 H10
  H11 H12 H13 Hra Hrok Hra4 Hrac HK.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
pose proof (wv_common_float X P lyc Sc Hpc Wc memc mdc kc (proj1 Hst)) as (HZc & HFc).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_node_cur X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre (proj1 Hst)) as (_ & HTVc & _).
destruct (wvl_ctx n' X ch i P (WriterValue.wvpieces t2 (y_p X) (y_dep X + 1)) P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn
  Hpre Hst Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HG & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hroom &
   HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax & Hcons & Hlive & Hfp &
   Hbufin & Hcap0 & Hcl & Hhead & Hfr0).
pose proof (ajxR_ar HJc) as HARc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & Hdd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD &
  Hoff & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; lia).
assert (HLK : forall a k0, In (a, k0) (y_D X) -> In (a, k0) Lamc /\ a <> bufc).
{ intros a k0 Hin. destruct (HD a k0 Hin) as (HinL & Hab).
  exact (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ HLED) HBLK a k0 HinL Hab). }
destruct Hv2 as (xb & yb & Hxb & Hxv & Hvy).
destruct (HTVc xb yb Hxb) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Hdep0 : (0 < PjTree.depth (y_t X))%nat) by lia.
eapply SRr'_bind.
{ eapply (wvl_call_selfI n' (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs
    (Z_to_bv 64 (BASE + ret)) ra1 nfp1 (y_o X) v2 (y_pretty X) (y_dep X + 1) bufc (prhWriter_putN ok (y_st X) P) t2
    D2 Lamc peakc ranc (- (y_d X + 176)) (IH fx) HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok
    ltac:(rewrite HB64; lia) ltac:(rewrite HB64; exact Hrac) HZc Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp
    (wv_pre_os4 X ch Hpre) Hcl H10 H11 H12
    H13 Hpr ltac:(lia) ltac:(lia) ltac:(lia) Ho1 Ho2 HOUT HLED Hev2
    (wvl_nodeR_lblk t2 _ _ _ v2 D2 HN2 (fun a k0 Hin _ => proj1 (HLK a k0 (HD2 _ Hin))))).
  - right. left. destruct (HLK xb yb Hxb) as (Hin & Hne). exists xb, yb. split; [exact Hin|]. split; [exact Hne|].
    split; [exact Hxv | exact Hvy].
  - exact (wv_ra_sub _ xb yb v2 56 T5 Hxv Hvy).
  - intros a k0 Hin. exact (HTVc a k0 (HD2 _ Hin)).
  - intros a k0 Hin. exact (HLK a k0 (HD2 _ Hin)).
  - intros z Hz Hf. apply (Hoff z Hz). destruct Hf as [Hh | (b & Hb & Hbz)].
    + right. exists (xb, yb). split; [exact Hxb|]. unfold pj_holdsR. cbn [fst snd]. lia.
    + right. exists b. split; [exact (HD2 b Hb) | exact Hbz].
  - exact Hfr0.
  - exact Hwmax.
  - exact Hhead.
  - exact Hcons.
  - exact Hlive.
  - exact Hfp. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & HZ2 & HFK2 & HJ2 & _ & HKC & HAP &
  HQV & HMN).
apply twvP_R_of in HQV. destruct HQV as (okp & histp & HRV).
rewrite Hrpi in HRV.
apply (HK fx' ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvl_after X ch i P (WriterValue.wvpieces t2 (y_p X) (y_dep X + 1)) lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc
  Lamc peakc ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 176))
  (y_sp X + y_d X + - (y_d X + 176) + - - (y_d X + 176)) ltac:(lia) Hpre Hst Hoks HG HOUT HLED HBLK HJ2 ltac:(lia)
  ltac:(lia) HKC HAP (twvP_room HRV)
  (ex_intro _ okp (conj (twvP_ret_ok HRV) (conj (twvP_granted HRV) (ex_intro _ histp (twvP_pos HRV)))))
  HMN fx' HZ2 HFK2).
Qed.

(* ---- the seated env's extra atoms ---- *)
Lemma wvl_E_at : forall X i regs kids keys nn kp,
  ew (wvl_E X i regs kids keys nn kp) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (wvl_E X i regs kids keys nn kp) 33 = Z_to_bv 64 (y_dep X) /\
  ew (wvl_E X i regs kids keys nn kp) 34 = Z_to_bv 64 (WV_STR (wv_sep_slot X)) /\
  ew (wvl_E X i regs kids keys nn kp) 35 = Z_to_bv 64 (WV_STR 151) /\
  ew (wvl_E X i regs kids keys nn kp) 36 = Z_to_bv 64 kids /\
  ew (wvl_E X i regs kids keys nn kp) 37 = Z_to_bv 64 keys /\
  ew (wvl_E X i regs kids keys nn kp) 38 = Z_to_bv 64 nn /\
  ew (wvl_E X i regs kids keys nn kp) 39 = Z_to_bv 64 (keys + 8 * Z.of_nat i) /\
  ew (wvl_E X i regs kids keys nn kp) 40 = Z_to_bv 64 kp /\
  ew (wvl_E X i regs kids keys nn kp) 41 = Z_to_bv 64 (kids + 56 * Z.of_nat i).
Proof.
intros X i regs kids keys nn kp. unfold wvl_E, wv_EH.
repeat split; (rewrite Eimg_low by (unfold A_TEXT; lia)); first
  [ exact (ew_Ereg_extra _ _ 0) | exact (ew_Ereg_extra _ _ 1) | exact (ew_Ereg_extra _ _ 2)
  | exact (ew_Ereg_extra _ _ 3) | exact (ew_Ereg_extra _ _ 4) | exact (ew_Ereg_extra _ _ 5)
  | exact (ew_Ereg_extra _ _ 6) | exact (ew_Ereg_extra _ _ 7) | exact (ew_Ereg_extra _ _ 8)
  | exact (ew_Ereg_extra _ _ 9) ].
Qed.

(* the saved registers' atoms 42 .. 54 (s0, s1, s2 .. s11, ra of the entry) *)
Lemma wvl_E_sv : forall X i regs kids keys nn kp,
  ew (wvl_E X i regs kids keys nn kp) 42 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 8)) /\
  ew (wvl_E X i regs kids keys nn kp) 43 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 9)) /\
  ew (wvl_E X i regs kids keys nn kp) 44 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 18)) /\
  ew (wvl_E X i regs kids keys nn kp) 45 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 19)) /\
  ew (wvl_E X i regs kids keys nn kp) 46 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 20)) /\
  ew (wvl_E X i regs kids keys nn kp) 47 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 21)) /\
  ew (wvl_E X i regs kids keys nn kp) 48 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 22)) /\
  ew (wvl_E X i regs kids keys nn kp) 49 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 23)) /\
  ew (wvl_E X i regs kids keys nn kp) 50 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 24)) /\
  ew (wvl_E X i regs kids keys nn kp) 51 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 25)) /\
  ew (wvl_E X i regs kids keys nn kp) 52 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 26)) /\
  ew (wvl_E X i regs kids keys nn kp) 53 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 27)) /\
  ew (wvl_E X i regs kids keys nn kp) 54 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 1)).
Proof.
intros X i regs kids keys nn kp. unfold wvl_E, wv_EH.
repeat split; (rewrite Eimg_low by (unfold A_TEXT; lia)); first
  [ exact (ew_Ereg_extra _ _ 10) | exact (ew_Ereg_extra _ _ 11) | exact (ew_Ereg_extra _ _ 12)
  | exact (ew_Ereg_extra _ _ 13) | exact (ew_Ereg_extra _ _ 14) | exact (ew_Ereg_extra _ _ 15)
  | exact (ew_Ereg_extra _ _ 16) | exact (ew_Ereg_extra _ _ 17) | exact (ew_Ereg_extra _ _ 18)
  | exact (ew_Ereg_extra _ _ 19) | exact (ew_Ereg_extra _ _ 20) | exact (ew_Ereg_extra _ _ 21)
  | exact (ew_Ereg_extra _ _ 22) ].
Qed.

(* ---- reading a register off a stop of a run from a seat: an atom of the seat's env, a seated register moved, a
   literal, the code pointer (the return address) ---- *)
Lemma wvl_reg_atom : forall E E' srs (regs' : bvmap 5 word) (r : bv 5) (n : nat) z,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> env_agree 55 E E' ->
  sr_get srs r = SOff n 0 -> (n < 55)%nat -> ew E n = Z_to_bv 64 z -> getr regs' r = Z_to_bv 64 z.
Proof.
intros E E' srs regs' r n z HRG [HA _] Hr Hn Hz. rewrite HRG, Hr. cbn [sv_denot].
rewrite (HA n Hn), Hz, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma wvl_reg_mv : forall E E' srs regs0 (regs' : bvmap 5 word) (r r0 : bv 5),
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> regs_ok E wvh_regs regs0 -> env_agree 55 E E' ->
  sv_eqb (sr_get srs r) (sr_get wvh_regs r0) = true -> getr regs' r = getr regs0 r0.
Proof.
intros E E' srs regs0 regs' r r0 HRG HR HA Hq. apply sv_eqb_eq in Hq.
rewrite HRG, Hq, (HR r0). apply (sv_denot_agree 55 E E'); [exact HA|].
pose proof wvl_regs_atoms as Ha. rewrite forallb_forall in Ha. apply Ha. apply all_regs_in.
Qed.

Lemma wvl_reg_lit : forall E' srs (regs' : bvmap 5 word) (r : bv 5) c,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> sr_get srs r = SLit c -> getr regs' r = Z_to_bv 64 c.
Proof. intros E' srs regs' r c HRG Hr. rewrite HRG, Hr. reflexivity. Qed.

Lemma wvl_reg_ra : forall E' srs (regs' : bvmap 5 word) c,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> img_env VAL A_LIM E' ->
  sr_get srs 1 = SOff A_TEXT c -> getr regs' 1 = Z_to_bv 64 (BASE + c).
Proof. intros E' srs regs' c HRG HE Hr. rewrite HRG, Hr. exact (codeptr_val E' c HE). Qed.

(* a run from a state without write windows keeps every byte *)
Lemma wvl_nowin_gen : forall E rs (m0 m1 : word -> option byte) (H : word -> bool),
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  frame_of E rs (mrestrict H m0) (mrestrict H m1) ->
  forall a, aview SEGS H m1 a = aview SEGS H m0 a.
Proof.
intros E rs m0 m1 H Hw Hfr a. apply (aview_eq_of SEGS). apply Hfr.
intros (r & Hr & Ha). rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

(* ---- a join survives a run from its seat that stops (at a call or a branch) with the seated callee-saved registers
   (the seat has no write window, so the run kept every byte; the journal and Pm are the runner's) ---- *)
Lemma wvl_st_run : forall X i P lyc Sc Hpc Wc regs memc mdc kc E E' srs (regs' : bvmap 5 word) mem' md',
  wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc -> 0 <= y_o X -> y_o X + 32 <= 2 ^ 64 ->
  regs_ok E wvh_regs regs -> env_agree 55 E E' ->
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get wvh_regs r)) CALLEE_SAVED = true ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS YGcfRehidePost.RZ_cf) (y_STK X + y_d X)
    (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc mem' md' kc ->
  Pm mem' ->
  (forall a, aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a) ->
  wvl_st X i P lyc Sc Hpc Wc regs' mem' md' kc.
Proof.
intros X i P lyc Sc Hpc Wc regs memc mdc kc E E' srs regs' mem' md' (Hcom & Hrf) Ho0 Ho64 HR HA HRG Hcs
  HJ HPm HK.
split.
- exact (wvl_common_run X P lyc Sc Hpc Wc memc mdc kc mem' md' Hcom Ho0 Ho64 HJ HPm HK).
- apply (wvl_rf_keep X i Wc Wc regs regs' memc mem' Hrf (wvl_aregs E E' srs regs regs' HRG HR HA Hcs)).
  intros a _. apply HK.
Qed.

(* ---- the return pcs of the loop's jal's: text addresses (closed facts, one per slot) ---- *)
Lemma wvl_ret_ok : forall k, 0 <= k <= 236 ->
  4096 <= BASE + WVL_PC k /\ YK0s.ret_ok (Z_to_bv 64 (BASE + WVL_PC k)).
Proof.
intros k Hk. pose proof (@pa_B_ok _ _ PA) as (HB0 & _ & _).
assert (HA0 : 4096 <= AF_write_value) by (vm_compute; congruence).
assert (HA1 : AF_write_value + 4 * 236 < 2 ^ 40) by (vm_compute; reflexivity).
unfold WVL_PC. split; [clear - HB0 HA0 Hk; lia|]. apply (ret_ok_codeptr_v (PI := PA)).
- clear - HA0 HA1 Hk; first [lia | change (2 ^ 40) with 1099511627776 in *; lia].
- apply Z.mod_divide; [lia|]. exists (2 * Z.of_nat WV_SLOT + 2 * k). unfold AF_write_value. lia.
Qed.

Lemma wvl_ceil_158 : BASE + WVL_PC 158 < YM05.alloc_ceiling.
Proof.
unfold WVL_PC.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_write_value + 4 * 158)
  ltac:(split; vm_compute; congruence) ltac:(vm_compute; reflexivity)).
Qed.
Lemma wvl_ceil_162 : BASE + WVL_PC 162 < YM05.alloc_ceiling.
Proof.
unfold WVL_PC.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_write_value + 4 * 162)
  ltac:(split; vm_compute; congruence) ltac:(vm_compute; reflexivity)).
Qed.
Lemma wvl_ceil_181 : BASE + WVL_PC 181 < YM05.alloc_ceiling.
Proof.
unfold WVL_PC.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_write_value + 4 * 181)
  ltac:(split; vm_compute; congruence) ltac:(vm_compute; reflexivity)).
Qed.
Lemma wvl_ceil_185 : BASE + WVL_PC 185 < YM05.alloc_ceiling.
Proof.
unfold WVL_PC.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_write_value + 4 * 185)
  ltac:(split; vm_compute; congruence) ltac:(vm_compute; reflexivity)).
Qed.
Lemma wvl_ceil_193 : BASE + WVL_PC 193 < YM05.alloc_ceiling.
Proof.
unfold WVL_PC.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_write_value + 4 * 193)
  ltac:(split; vm_compute; congruence) ltac:(vm_compute; reflexivity)).
Qed.
Lemma wvl_ceil_210 : BASE + WVL_PC 210 < YM05.alloc_ceiling.
Proof.
unfold WVL_PC.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_write_value + 4 * 210)
  ltac:(split; vm_compute; congruence) ltac:(vm_compute; reflexivity)).
Qed.

(* ---- the node's fields at a join's memory (any item counter, the container non-empty) ---- *)
Lemma wvl_node_facts : forall X ch P lyc Sc Hpc Wc memc mdc kc,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wv_common X P lyc Sc Hpc Wc memc mdc kc ->
  (0 < wv_nitems (y_t X))%nat ->
  exists kids keys nn cap,
    val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 (wv_tagc (y_t X)) /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) kids /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) keys /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) nn /\
    nn = Z.of_nat (wv_nitems (y_t X)) /\ nn <= cap /\ 0 < cap /\ In (kids, 56 * cap) (y_D X) /\
    (wv_tagc (y_t X) = 5 -> keys = 0) /\ (wv_tagc (y_t X) = 6 -> In (keys, 8 * cap) (y_D X)).
Proof.
intros X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom Hn.
destruct (wvl_item_facts X ch P lyc Sc Hpc Wc memc mdc kc 0 HSTK Hpre Hcom Hn) as
  (kids & keys & nn & cap & D1 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & _ & _ & V9 & V10).
exists kids, keys, nn, cap. repeat (split; [assumption|]). intros H. exact (proj1 (V10 H)).
Qed.

(* a tree block's facts: user base 16-aligned, at least 4096, below the ceiling, off the shadow band *)
Lemma wvl_blk_facts : forall X ch a k,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> In (a, k) (y_D X) ->
  a mod 16 = 0 /\ 4096 <= a /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\
  (a + k <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a).
Proof.
intros X ch a k HSTK Hpre Hin.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _ & _ & _ & _ & HD & _).
destruct (HD a k Hin) as (HinL & _).
pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED0 (a, k) HinL) as (Hk0 & Hbl & _ & Ha16 & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR0 Hbl) as (Hp16 & Hp4096 & Hpc & Hpapp & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
split; [exact Ha16|]. split; [lia|]. split; [lia|]. split; [lia|].
change (2 ^ 44) with 17592186044416. unfold SHADOW_OFF. lia.
Qed.

(* the separator literal is one of write_value's literals *)
Lemma wvl_sep_lit : forall X, In (wv_sep_slot X, WriterValue.wsep (y_p X)) wv_lits.
Proof.
intros X. unfold wv_sep_slot, y_p, WriterValue.wsep, wv_lits.
destruct (y_pretty X =? 0); cbn [negb]; cbn [In]; auto 20.
Qed.

(* ---- THE SEAT AT A JOIN: the seated state at pc, from wv_pre, the join at counter i (i <= n; with the key slot,
   kr = true, i < n and an object) and the node's field values at the join's memory ---- *)
Lemma wvl_seat_join : forall n' X ch i P lyc Sc Hpc Wc regs memc mdc kc pc (kr : bool) kids keys nn cap kp,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wvl_st X i P lyc Sc Hpc Wc regs memc mdc kc ->
  (i <= wv_nitems (y_t X))%nat -> (0 < wv_nitems (y_t X))%nat ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 (wv_tagc (y_t X)) ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) kids ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) keys ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) nn ->
  nn = Z.of_nat (wv_nitems (y_t X)) -> nn <= cap -> 0 < cap -> In (kids, 56 * cap) (y_D X) ->
  (wv_tagc (y_t X) = 5 -> keys = 0) -> (wv_tagc (y_t X) = 6 -> In (keys, 8 * cap) (y_D X)) ->
  (kr = true -> (i < wv_nitems (y_t X))%nat /\ wv_tagc (y_t X) = 6 /\
     rd_u64 SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) kp) ->
  img_env VAL A_LIM (wvl_E X i regs kids keys nn kp) /\ regs_ok (wvl_E X i regs kids keys nn kp) wvh_regs regs /\
  st_ok_pi SEGS VAL (wvl_E X i regs kids keys nn kp) (wvl_ss pc (wv_tagc (y_t X)) kr)
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx (wvl_SH kr) (wvl_E X i regs kids keys nn kp) (mrestrict (w_H Wc) memc).
Proof.
intros n' X ch i P lyc Sc Hpc Wc regs memc mdc kc pc kr kids keys nn cap kp HSTKn Hpre Hst Hi Hn0 Vtg (Rkids & Vkids)
  (Rkeys & Vkeys) (Rnn & Vnn) Hnn Hncap Hcap Hkb Hk5 Hk6 Hkr.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as ((HPREx & _) & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & _ & _ & _ & _ & _ & HOUT0 & HLED0 & HNODE0 &
  HLOC & _).
destruct (wv_loc (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X) ch (y_STK X) (y_Lam X) (y_peak X)
  _ _ (y_ran X) (y_buf X) (y_v X) HSTK HPREx HLED0 HLOC) as (Hv4096 & Hv47 & Hvsp & Hband & Hvimg).
assert (Hv8 : y_v X mod 8 = 0)
  by (clear - HNODE0; destruct (y_t X); destruct HNODE0 as (_ & _ & _ & _ & _ & _ & _ & _ & ((Hv8 & _) & _) & _);
      exact Hv8).
pose proof Hst as (Hcom & Hrf).
destruct (wvl_node_cur X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom) as (HNODEc & HTVc & HRAc).
assert (HAPc : pj_apartR (y_D X) (y_v X)) by (clear - HNODEc; destruct (y_t X); exact (proj1 (proj2 HNODEc))).
destruct Hcom as (HJc & _ & _ & _ & _ & HROc & _).
pose proof (ajxR_ar HJc) as HARc.
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wvl_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (Hk16 & Hk4096 & _ & Hkc & _).
assert (HSTR : forall slot bs, In (slot, bs) wv_lits -> 0 <= WV_STR slot < 2 ^ 64).
{ intros slot bs Hl. destruct (HLIT slot bs lyc Sc Hpc Wc memc mdc Hl HARc HROc) as (_ & _ & Himg).
  assert (Hlen0 : 0 < Z.of_nat (length bs))
    by (unfold wv_lits in Hl; cbn [In] in Hl;
        repeat (destruct Hl as [Hl' | Hl]; [injection Hl' as <- <-; cbn; lia |]); destruct Hl).
  pose proof (pa_segs_low _ (Himg 0 ltac:(lia))) as Hlow. rewrite Z.add_0_r in Hlow.
  unfold kLowMemEnd in Hlow. split; [lia|]. change (2 ^ 64) with 18446744073709551616. lia. }
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
assert (Hn : (wv_nitems (y_t X) <= Z.to_nat cap)%nat) by lia.
assert (Hi8 : 0 <= 8 * Z.of_nat i <= 8 * cap) by lia.
assert (Hi56 : 0 <= 56 * Z.of_nat i <= 56 * cap) by lia.
assert (Hkeysb : 0 <= keys /\ keys + 8 * cap <= YM05.alloc_ceiling).
{ destruct Htg as [H5 | H6].
  - rewrite (Hk5 H5). lia.
  - destruct (wvl_blk_facts X ch keys (8 * cap) HSTK Hpre (Hk6 H6)) as (_ & _ & _ & ? & _). lia. }
apply (wvl_seat X i Wc regs memc pc (wv_tagc (y_t X)) kr kids keys nn kp Htg Hrf Hpr Hdep Hsp16
  ltac:(unfold y_sp in *; lia) Hv8 Hv4096 Hv47 ltac:(unfold y_sp in *; exact Hvsp) Hband HRAc Vtg Vkids
  ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia) Vkeys ltac:(lia)
  ltac:(change (2 ^ 64) with 18446744073709551616; lia) Vnn ltac:(rewrite Hnn; change (2 ^ 64) with 18446744073709551616; lia)
  (HSTR _ _ (wvl_sep_lit X)) (HSTR 151%nat [44] ltac:(cbn; auto 20))).
intros Hkt. destruct (Hkr Hkt) as (Hin & Ht6 & (Rkp & Vkp)).
pose proof (Hk6 Ht6) as HkbK.
destruct (wvl_blk_facts X ch keys (8 * cap) HSTK Hpre HkbK) as (Hk16' & Hk4096' & _ & Hkc' & Hkband').
assert (Hi8' : 8 * Z.of_nat i + 8 <= 8 * cap) by lia.
split; [exact Rkp|]. split; [exact Vkp|].
split.
{ apply Z.mod_divide in Hk16' as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (2 * q + Z.of_nat i). lia. }
split; [lia|]. split; [lia|].
split; [change (2 ^ 44) with 17592186044416 in *; unfold SHADOW_OFF in *; lia|].
split.
- destruct (HTVc keys (8 * cap) HkbK) as (_ & _ & _ & _ & T5 & _).
  apply (wv_ra_sub _ keys (8 * cap)); [exact T5 | lia | lia].
- destruct (Z_le_gt_dec (keys + 8 * Z.of_nat i + 8) (y_v X)) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec (y_v X + 56) (keys + 8 * Z.of_nat i)) as [Hr|Hr]; [right; exact Hr|].
  exfalso. set (z := Z.max (y_v X) (keys + 8 * Z.of_nat i)).
  apply (HAPc (keys, 8 * cap) z HkbK); [unfold pj_holdsR; cbn [fst snd]; lia | lia].
Qed.

(* ---- the pieces at the body's joins: after the comma, the indent, an object's key, its separator, the value ---- *)
Definition wvl_itail (X : wvx) (i : nat) : list (list Z) :=
  match y_t X with
  | PjTree.JObj _ => WriterSpec.spieces (wvl_key X i) ++ [WriterValue.wsep (y_p X)] ++
                       WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1)
  | _ => WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1)
  end.
Definition wvl_PA (X : wvx) (i : nat) : list (list Z) := wv_done X i ++ WriterValue.wcomma i.
Definition wvl_PB (X : wvx) (i : nat) : list (list Z) := wvl_PA X i ++ WriterValue.wind (y_p X) (y_dep X + 1).
Definition wvl_Pk (X : wvx) (i : nat) : list (list Z) := wvl_PB X i ++ WriterSpec.spieces (wvl_key X i).
Definition wvl_Ps (X : wvx) (i : nat) : list (list Z) := wvl_Pk X i ++ [WriterValue.wsep (y_p X)].
Definition wvl_PD (X : wvx) (i : nat) : list (list Z) :=
  match y_t X with PjTree.JObj _ => wvl_Ps X i | _ => wvl_PB X i end.

Lemma wvl_item_eq : forall X i, (i < wv_nitems (y_t X))%nat ->
  wvl_item X i = WriterValue.wcomma i ++ WriterValue.wind (y_p X) (y_dep X + 1) ++ wvl_itail X i.
Proof.
intros X i Hi. unfold wvl_item, wvl_itail, wvl_key, wvl_child, wv_nitems in *.
destruct (y_t X); cbn in Hi; try lia; reflexivity.
Qed.

Lemma wvl_pcs_A : forall X i, (i < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvl_PA X i ++ WriterValue.wind (y_p X) (y_dep X + 1) ++ (wvl_itail X i ++ wvl_rest X (S i)).
Proof.
intros X i Hi. rewrite (wvl_split_item X i Hi), (wvl_item_eq X i Hi). unfold wvl_PA.
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvl_pcs_comma : forall X i, (i < wv_nitems (y_t X))%nat -> i <> 0%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wv_done X i ++ [[44]] ++ (WriterValue.wind (y_p X) (y_dep X + 1) ++ wvl_itail X i ++ wvl_rest X (S i)).
Proof.
intros X i Hi Hi0. rewrite (wvl_pcs_A X i Hi). unfold wvl_PA, WriterValue.wcomma.
destruct (Nat.eqb_spec i 0) as [E|_]; [lia|]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvl_PA_comma : forall X i, i <> 0%nat -> wv_done X i ++ [[44]] = wvl_PA X i.
Proof.
intros X i Hi0. unfold wvl_PA, WriterValue.wcomma. destruct (Nat.eqb_spec i 0) as [E|_]; [lia | reflexivity].
Qed.

Lemma wvl_PA_0 : forall X, wvl_PA X 0 = wv_done X 0.
Proof. intros X. unfold wvl_PA. cbn [WriterValue.wcomma Nat.eqb]. apply app_nil_r. Qed.

Lemma wvl_pcs_B : forall X i, (i < wv_nitems (y_t X))%nat -> wv_tagc (y_t X) = 6 ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvl_PB X i ++ WriterSpec.spieces (wvl_key X i) ++
    ([WriterValue.wsep (y_p X)] ++ WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1) ++ wvl_rest X (S i)).
Proof.
intros X i Hi Ht. rewrite (wvl_pcs_A X i Hi). unfold wvl_PB, wvl_itail, wv_tagc in *.
destruct (y_t X); try discriminate Ht. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvl_pcs_k : forall X i, (i < wv_nitems (y_t X))%nat -> wv_tagc (y_t X) = 6 ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvl_Pk X i ++ [WriterValue.wsep (y_p X)] ++
    (WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1) ++ wvl_rest X (S i)).
Proof.
intros X i Hi Ht. rewrite (wvl_pcs_B X i Hi Ht). unfold wvl_Pk. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvl_pcs_D : forall X i, (i < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvl_PD X i ++ WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1) ++ wvl_rest X (S i).
Proof.
intros X i Hi. rewrite (wvl_pcs_A X i Hi). unfold wvl_PD, wvl_Ps, wvl_Pk, wvl_PB, wvl_itail.
destruct (y_t X); rewrite <- !app_assoc; reflexivity.
Qed.

Lemma wvl_done_D : forall X i, (i < wv_nitems (y_t X))%nat ->
  wv_done X (S i) = wvl_PD X i ++ WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1).
Proof.
intros X i Hi. rewrite (wvl_done_S X i Hi), (wvl_item_eq X i Hi). unfold wvl_PD, wvl_Ps, wvl_Pk, wvl_PB, wvl_PA,
  wvl_itail.
destruct (y_t X); rewrite <- !app_assoc; reflexivity.
Qed.

Lemma wvl_pcs_end : forall X, (0 < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X) ++
    [[if wv_tagc (y_t X) =? 6 then 125 else 93]].
Proof.
intros X Hn. rewrite (wvl_split X (wv_nitems (y_t X)) Hn (le_n _)).
destruct (wvl_rest_end X) as [E | (E & _)]; [rewrite E; reflexivity | lia].
Qed.

(* ---- the closing tail put's chain from the entry s0 (wv_tail_gen asks it at the entry and at the tail memory) ---- *)
(* the chain from v that the two words below v give, as a function of those words *)
Definition wvl_ch (top v ra nfp : Z) : list (Z * Z * Z) :=
  if (YM05.alloc_ceiling <=? v) && (v mod 8 =? 0) && (v <? top - 16) && (4096 <=? ra) then [(v, ra, nfp)] else [].

Lemma wvl_chain_one : forall ly rd sp v ra nfp,
  rdword rd (v - 8) = Some ra -> rdword rd (v - 16) = Some nfp -> 0 <= ra ->
  nfp < YM05.alloc_ceiling -> sp + 16 <= v -> achain ly rd sp v (wvl_ch (ly_top ly) v ra nfp).
Proof.
intros ly rd sp v ra nfp H8 H16 Hra0 Hn Hsp. unfold wvl_ch.
destruct (Z.leb_spec YM05.alloc_ceiling v) as [Hv|Hv]; cbn [andb].
2:{ left. split; [left; exact Hv | reflexivity]. }
destruct (Z.eqb_spec (v mod 8) 0) as [Hal|Hal]; cbn [andb].
2:{ left. split; [right; right; exact Hal | reflexivity]. }
destruct (Z.ltb_spec v (ly_top ly - 16)) as [Ht|Ht]; cbn [andb].
2:{ left. split; [right; left; lia | reflexivity]. }
destruct (Z.leb_spec 4096 ra) as [Hr|Hr].
- right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|].
    split; [lia|].
    assert (Hb : bad_next v (ly_top ly) nfp = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb. reflexivity.
  + constructor; [cbn; lia | constructor].
- right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [|constructor].
  cbn [fpchain]. exists ra. split; [exact H8 | lia].
Qed.

(* the chain the closing tail put needs: one that holds at the entry (for its fpre) and at the tail memory *)
Lemma wvl_tail_chain : forall X ch P lyc Sc Hpc Wc memc mdc kc,
  176 <= y_STK X -> wv_pre (fx := y_fx X) X ch -> wv_common X P lyc Sc Hpc Wc memc mdc kc ->
  exists ch', fpre B ARx (y_STK X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X) ch' /\
    achain lyc (aview SEGS (w_H Wc) memc) (y_sp X) (s0Z (y_regs X)) ch'.
Proof.
intros X ch P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcut & HWIN & _ & _ & HOUT0 & HLED0 & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs0 & Hca & _).
pose proof HPRE as ((HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT) & HRO & Htop & HRZ & HFRM).
destruct Hcom as (HJc & HKW & _ & _ & _ & _ & HZc & _).
pose proof (ajxR_ly HJc) as Hly.
assert (Etop : ly_top lyc = ly_top (y_ly X))
  by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); exact Etop).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (HK16 : forall a, y_sp X <= a < y_o X ->
    aview SEGS (w_H Wc) memc a = aview SEGS (w_H (y_W X)) (y_mem X) a).
{ intros a Ha. apply HKW; [lia|]. unfold y_FP.
  eapply (wvl_nfp _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HAR0 HLED0 HOUT0); lia. }
destruct Hs0 as [Es0 | Hlow].
- destruct Hcut as [H1 | H2].
  + destruct (Hca H1) as (ra & Hra & nfp & Hnfp & Hnfpc).
    assert (Hra' : rdword (aview SEGS (w_H Wc) memc) (y_o X - 8) = Some ra)
      by (rewrite (wv_rdword_ext (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) memc));
          [exact Hra | intros j Hj; apply HK16; lia]).
    assert (Hnfp' : rdword (aview SEGS (w_H Wc) memc) (y_o X - 16) = Some nfp)
      by (rewrite (wv_rdword_ext (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) memc));
          [exact Hnfp | intros j Hj; apply HK16; lia]).
    pose proof (wv_rdword_nonneg _ _ _ _ Hra) as Hra0.
    exists (wvl_ch (ly_top (y_ly X)) (y_o X) ra nfp). split.
    * split; [|split; [exact HRO | split; [exact Htop | split; [exact HRZ | exact HZc]]]].
      split; [exact HAR|]. split; [exact Hret|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
      split; [exact Hstk|]. split; [exact Hpres|]. split; [|exact HQT].
      rewrite Es0. apply (wvl_chain_one (y_ly X) _ (spZ (y_regs X)) (y_o X) ra nfp Hra Hnfp Hra0 Hnfpc).
      unfold y_sp in H1. exact H1.
    * rewrite Es0, <- Etop. apply (wvl_chain_one lyc _ (y_sp X) (y_o X) ra nfp Hra' Hnfp' Hra0 Hnfpc H1).
  + (* o = sp + 8: the entry chain is the empty first arm, independent of memory *)
    exists ch. split; [exact (wv_fpre_fx _ _ _ _ _ _ _ _ _ _ _ HPRE HZc)|].
    rewrite Es0 in Hchain. unfold y_sp in *.
    destruct Hchain as [(Hc & Ech) | (Hc & _)]; [|lia].
    left. split; [rewrite Es0, Etop; exact Hc | exact Ech].
- (* s0 below the ceiling: the empty first arm *)
  exists ch. split; [exact (wv_fpre_fx _ _ _ _ _ _ _ _ _ _ _ HPRE HZc)|].
  destruct Hchain as [(Hc & Ech) | (Hc & _)]; [|unfold y_sp in *; lia].
  left. split; [left; exact Hlow | exact Ech].
Qed.

(* ---- small facts the segments use ---- *)
Lemma wvl_awr_ok : forall E pc tg kr STK sp0 FP bl0 blc ly own,
  awr_ok E (ss_mem (wvl_ss pc tg kr)) STK sp0 FP bl0 blc ly own.
Proof.
intros E pc tg kr STK sp0 FP bl0 blc ly own. unfold wvl_ss, wvl_mem. cbn [ss_mem].
destruct kr; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Qed.

Lemma wvl_U_reg : forall E regs (r : bv 5) (n : nat), regs_ok E wvh_regs regs ->
  sr_get wvh_regs r = SOff n 0 -> U E (SOff n 0) = bv_unsigned (getr regs r).
Proof. intros E regs r n HR Hs. unfold U. rewrite (HR r), Hs. reflexivity. Qed.

Lemma wvl_depth_pos : forall t, (0 < wv_nitems t)%nat -> (1 <= PjTree.depth t)%nat.
Proof. intros t H. destruct t; cbn in H |- *; lia. Qed.

Lemma wvl_reg_ret : forall E' srs (regs' : bvmap 5 word) k,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> img_env VAL A_LIM E' ->
  sr_get srs 1 = SOff A_TEXT (WVL_PC k) -> getr regs' 1 = Z_to_bv 64 (BASE + WVL_PC k).
Proof. intros E' srs regs' k HRG HE Hr. exact (wvl_reg_ra E' srs regs' (WVL_PC k) HRG HE Hr). Qed.

(* the head registers of a join *)
Lemma wvl_rf_regs : forall X i W regs mem, wvl_rf X i W regs mem ->
  getr regs 2 = w64 (y_sp X - 176) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (y_o X) /\ getr regs 9 = w64 (y_v X) /\ getr regs 19 = w64 (y_pretty X) /\
  getr regs 21 = w64 (Z.of_nat i) /\ getr regs 22 = w64 (8 * Z.of_nat i) /\ getr regs 24 = w64 (y_dep X + 1) /\
  getr regs 25 = w64 (56 * Z.of_nat i).
Proof.
intros X i W regs mem H. unfold wvl_rf in H. cbv beta zeta in H.
destruct H as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
repeat (split; [assumption|]). exact G25.
Qed.

(* the tail state's callee-saved registers are the entry's (the epilogue reloaded them from the frame) *)
Lemma wvl_tail_aregs : forall X (regs' : bvmap 5 word),
  getr regs' 2 = getr (y_regs X) 2 -> getr regs' 3 = getr (y_regs X) 3 -> getr regs' 4 = getr (y_regs X) 4 ->
  getr regs' 8 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 8)) ->
  getr regs' 9 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 9)) ->
  getr regs' 18 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 18)) ->
  getr regs' 19 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 19)) ->
  getr regs' 20 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 20)) ->
  getr regs' 21 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 21)) ->
  getr regs' 22 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 22)) ->
  getr regs' 23 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 23)) ->
  getr regs' 24 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 24)) ->
  getr regs' 25 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 25)) ->
  getr regs' 26 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 26)) ->
  getr regs' 27 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 27)) ->
  aregs_preserved (y_regs X) regs'.
Proof.
intros X regs' R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 r Hr.
unfold acallee_saved in Hr.
assert (H : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
            r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H as [->|H]; [ first [exact R2 | exact R3 | exact R4
  | exact (eq_trans R8 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R9 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R18 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R19 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R20 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R21 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R22 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R23 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R24 (Z_to_bv_bv_unsigned _ _)) | exact (eq_trans R25 (Z_to_bv_bv_unsigned _ _))
  | exact (eq_trans R26 (Z_to_bv_bv_unsigned _ _)) ] |]).
subst r. exact (eq_trans R27 (Z_to_bv_bv_unsigned _ _)).
Qed.

(* a register that reads atom n of the seated env (n < 55) *)
Lemma wvl_reg_sv : forall E E' srs (regs' : bvmap 5 word) (r : bv 5) (n : nat) w,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> env_agree 55 E E' ->
  sr_get srs r = SOff n 0 -> (n < 55)%nat -> ew E n = w -> getr regs' r = w.
Proof.
intros E E' srs regs' r n w HRG [HA _] Hr Hn Hw. rewrite HRG, Hr. cbn [sv_denot].
rewrite (HA n Hn), Hw, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* a literal's address in a register (the engine's SOff of the PAddHi atom) *)
Lemma wvl_reg_str : forall E' srs (regs' : bvmap 5 word) (r : bv 5) slot,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> img_env VAL A_LIM E' ->
  sr_get srs r = SOff (wv_addhi_atom slot) (wv_addhi_off slot) ->
  (A_TEXT <= wv_addhi_atom slot < A_LIM)%nat -> getr regs' r = w64 (WV_STR slot).
Proof.
intros E' srs regs' r slot HRG HE Hr Hrange. rewrite HRG, Hr. cbn [sv_denot].
rewrite (HE _ Hrange). unfold WV_STR, w64. reflexivity.
Qed.

(* the tail state's sp: the seat's sp + 176, the entry sp *)
Lemma wvl_reg_sp : forall X E E' srs regs (regs' : bvmap 5 word),
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> regs_ok E wvh_regs regs -> env_agree 55 E E' ->
  sr_get srs 2%bv = SOff 2 176 -> getr regs 2 = w64 (y_sp X - 176) -> 176 <= y_sp X < 2 ^ 64 ->
  getr regs' 2 = getr (y_regs X) 2.
Proof.
intros X E E' srs regs regs' HRG HR [HA _] Hs G2 Hsp. rewrite HRG, Hs. cbn [sv_denot].
rewrite (HA 2%nat ltac:(lia)).
pose proof (HR 2%bv) as H2. change (sr_get wvh_regs 2%bv) with (SOff 2 0) in H2. cbn [sv_denot] in H2.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H2. rewrite <- H2, G2. unfold w64.
rewrite unsigned_lit_small by lia. replace (y_sp X - 176 + 176) with (y_sp X) by lia.
unfold y_sp, spZ. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- THE CLOSE (write_value + 4 * 210 .. 236): after the last indent, v's shadow check, the bracket, the epilogue,
   the tail `j put`; wv_tail_gen and wv_post_P give the container's post ---- *)
Lemma wvl_seg_210 : forall n' X ch lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> (0 < wv_nitems (y_t X))%nat ->
  wvl_st X (wv_nitems (y_t X)) (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X))
    lyc Sc Hpc Wc regs memc mdc kc ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVL_PC 210)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hn Hst.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as (HPRE & _ & _ & Hcl & _ & _ & _ & _ & Hpr & Hdep & Hdd & Hcut & HWIN & _ & _ & HOUT0 & HLED0 &
  HNODE0 & HLOC & _ & _ & HD & Hoff & _ & Hwmax & Hhead & Hlive & _ & Hcons & _).
assert (Hbufb : WriterApp.w_cap (y_st X) <> 0 ->
    In (y_buf X - cf_head, WriterApp.w_cap (y_st X) + cf_head) (ablocks B (y_ly X) (y_S X))).
{ intros Hc. destruct (wv_led_hbs _ _ _ _ _ _ _ _ _ _ HLED0 _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
pose proof HPRE as ((_ & _ & _ & Hgp & Htp & _) & _).
pose proof Hst as (Hcom & Hrf).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
destruct (wvl_node_facts X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom Hn) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvl_tail_chain X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom) as (ch' & HPRE' & Hch').
pose proof (wvl_E_sv X (wv_nitems (y_t X)) regs kids keys nn 0) as
  (E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54).
destruct (wvl_seat_join n' X ch (wv_nitems (y_t X)) _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 210) false kids keys nn
  cap 0 HSTKn Hpre Hst (le_n _) Hn Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvl_E X (wv_nitems (y_t X)) regs kids keys nn 0) in *.
pose proof Hcom as (HJ & _ & HPM & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (Hsl : (wv_tagc (y_t X) = 5 /\ (216%nat, [93]) = (216%nat, [93])) \/
              (wv_tagc (y_t X) = 6 /\ (219%nat, [125]) = (219%nat, [125])))
  by (unfold wv_tagc; destruct (y_t X); auto).
destruct Hsl as [(Ht & _) | (Ht & _)]; rewrite Ht in HS.
all: paj_run_to_tok_x_inv RUNTOI
  HS HJ SHOK HPM WV_Bspan (WVL_PC 236); [apply wvl_awr_ok | ].
all: lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
       pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K1 end.
all: clear HF HFr HG.
all: paj_run_tok_x_inv RUNI
  HS HJ SHOK HPM WV_Bspan; [ cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]] | ].
all: lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
       pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K2 end.
all: clear HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  let slot := lazymatch type of Ht with _ = 5 => constr:(216%nat) | _ = 6 => constr:(219%nat) end in
  let cbyte := lazymatch type of Ht with _ = 5 => constr:(93) | _ = 6 => constr:(125) end in
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvl_agree;
  assert (HEI2 : img_env VAL A_LIM E2) by assumption;
  assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a) by (intros a; rewrite K2; apply K1);
  pose proof (wvl_common_run X _ lyc Sc Hpc Wc memc mdc kc (ms_mem ms2) _ Hcom ltac:(zl) ltac:(zl) HJ HPM KM) as Hcom2;
  pose proof (conj Hcom2 (wvl_rf_keep X _ Wc Wc regs regs memc (ms_mem ms2) Hrf (fun r _ => eq_refl) (fun a _ => KM a)))
    as Hst2;
  destruct Hcom2 as (HJ2 & HKW2 & HPM2 & (ok & ranc & bufc & Lamc & peakc & Hoks & HG & HOUT & HLED & HBLK & (rph & Hrp)) &
    Hroom & HRO2 & HZ2 & HF2);
  pose proof (ajxR_ar HJ2) as HARc2;
  pose proof HOUT as (_ & _ & Hcapc0 & _);
  assert (Hbufinc : WriterApp.w_cap (prhWriter_putN ok (y_st X) (wv_done X (wv_nitems (y_t X)) ++
      WriterValue.wind (y_p X) (y_dep X))) <> 0 -> In (bufc, WriterApp.w_cap (prhWriter_putN ok (y_st X)
      (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X)))) Lamc)
    by (intros Hc; destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]);
        [lia | exact Hin]);
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (WV_STR slot))
    by (apply (wvl_reg_str E2 (ss_regs ss2) (ms_regs ms2) 11%bv slot HRG HEI2);
        [vm_compute; reflexivity | split; vm_compute; lia]);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (Z.of_nat (length [cbyte])))
    by (exact (wvl_reg_lit E2 (ss_regs ss2) (ms_regs ms2) 12%bv 1 HRG ltac:(vm_compute; reflexivity)));
  assert (Hra : getr (ms_regs ms2) 1 = getr (y_regs X) 1)
    by (rewrite (wvl_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 1%bv 54%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E54); apply Z_to_bv_bv_unsigned);
  assert (R2 : getr (ms_regs ms2) 2 = getr (y_regs X) 2)
    by (apply (wvl_reg_sp X E E2 (ss_regs ss2) regs (ms_regs ms2) HRG Hregs HA ltac:(vm_compute; reflexivity) G2);
        unfold y_sp in *; zl);
  assert (R3 : getr (ms_regs ms2) 3 = getr (y_regs X) 3)
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 3%bv 3%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)), G3, Hgp; reflexivity);
  assert (R4 : getr (ms_regs ms2) 4 = getr (y_regs X) 4)
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 4%bv 4%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)), G4, Htp; reflexivity);
  assert (HAP : aregs_preserved (y_regs X) (ms_regs ms2))
    by (apply (wvl_tail_aregs X (ms_regs ms2) R2 R3 R4);
        [ exact (wvl_reg_sv E E2 _ _ 8%bv 42%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E42)
        | exact (wvl_reg_sv E E2 _ _ 9%bv 43%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E43)
        | exact (wvl_reg_sv E E2 _ _ 18%bv 44%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E44)
        | exact (wvl_reg_sv E E2 _ _ 19%bv 45%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E45)
        | exact (wvl_reg_sv E E2 _ _ 20%bv 46%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E46)
        | exact (wvl_reg_sv E E2 _ _ 21%bv 47%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E47)
        | exact (wvl_reg_sv E E2 _ _ 22%bv 48%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E48)
        | exact (wvl_reg_sv E E2 _ _ 23%bv 49%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E49)
        | exact (wvl_reg_sv E E2 _ _ 24%bv 50%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E50)
        | exact (wvl_reg_sv E E2 _ _ 25%bv 51%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E51)
        | exact (wvl_reg_sv E E2 _ _ 26%bv 52%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E52)
        | exact (wvl_reg_sv E E2 _ _ 27%bv 53%nat _ HRG HA ltac:(vm_compute; reflexivity) ltac:(lia) E53) ]);
  assert (Hspc : spZ (ms_regs ms2) = spZ (y_regs X)) by (unfold spZ; rewrite R2; reflexivity);
  assert (Hgpc : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp);
  assert (Htpc : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite R4; exact Htp);
  assert (Hch2 : achain lyc (aview SEGS (w_H Wc) (ms_mem ms2)) (spZ (y_regs X)) (s0Z (ms_regs ms2)) ch')
    by (rewrite (wv_s0_pres _ _ HAP);
        pose proof (ajxR_ly HJ2) as Hly;
        destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _);
        apply (achain_kept lyc (aview SEGS (w_H Wc) memc) _ (y_sp X) (s0Z (y_regs X)) ch' (y_sp X) Hch');
        [lia | rewrite Etop; zl | intros a _; apply KM]);
  destruct (HLIT slot [cbyte] lyc Sc Hpc Wc (ms_mem ms2) _ ltac:(cbn; auto 20) HARc2 HRO2) as (Hsrc & Hkept & Himg);
  assert (Hhome : prhWriter_src_home B lyc Sc Lamc bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X)
      (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X)))) (WV_STR slot) (Z.of_nat (length [cbyte])))
    by (eapply (wv_lit_home lyc Sc Hpc Wc (ms_mem ms2) _ Lamc peakc _ _ ranc bufc _ (WV_STR slot) 1 HARc2 HLED Hbufinc
          ltac:(lia) ltac:(lia) Hkept);
        intros a Ha; replace a with (WV_STR slot + (a - WV_STR slot)) by lia; apply Himg; cbn; lia);
  assert (Hpcs : WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
      (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X)) ++ [[cbyte]] ++ [])
    by (rewrite (wvl_pcs_end X Hn), Ht, app_nil_r, <- app_assoc; reflexivity);
  pose proof (wv_wmax_next ok (y_st X) (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X))
    [[cbyte]] [] ltac:(rewrite <- Hpcs; exact Hwmax)) as Hwmax';
  pose proof (wv_live_next (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc ok
    (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X)) [[cbyte]] [] Hcap0 Hbufb HBLK
    ltac:(rewrite <- Hpcs; exact Hlive)) as Hlive';
  pose proof (wv_cons_next (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X) (y_st X)
    (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X)) [[cbyte]] [] ok
    ltac:(rewrite <- Hpcs; exact Hcons)) as Hcons';
  unfold wv_Qfin, wv_Qin; rewrite Hpcs, app_nil_r;
  eapply (wv_post_P (y_fx X) Wc _ (y_STK X) (y_d X) (y_FP X) (y_regs X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X)
    (y_md X) (ms_mem ms2)); [exact HZ2 | exact HF2 | | exact HPM2];
  exact (wv_tail_gen (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X) (y_rpH0 X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X)
    (y_mem X) (y_md X) ch' (y_STK X) (y_d X) (y_o X) (y_v X) (y_t X) (y_D X) (y_Lam X) (y_peak X) (y_ran X) (y_buf X)
    (y_st X) (wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X)) (WV_STR slot) [cbyte] lyc Sc Hpc
    Wc (ms_mem ms2) _ kc (ms_regs ms2) ok ranc bufc Lamc peakc _ rph HSTK ltac:(lia) HPRE' Hcl HWIN Ho1 Ho2 HLED0
    HOUT0 HNODE0 HLOC HD Hoff HJ2 HKW2 Hroom eq_refl Hrp (wv_pre_os4 X ch Hpre) Hoks HG HOUT HLED HBLK HAP Hspc Hra
    Hgpc Htpc Hch2 HRO2 H10 H11
    H12 Hcut (fun _ => wvl_owords X ch _ _ lyc Sc Hpc Wc regs (ms_mem ms2) _ kc HSTK Hpre Hst2)
    ltac:(pose proof (wvl_pre_ev X ch Hpre) as HevT; rewrite Hpcs, app_nil_r in HevT; exact HevT) Hsrc Hhome Hwmax'
    Hhead Hcons' Hlive')
end.
Qed.

(* a seated register read through the seat's env *)
Lemma wvl_ew_reg : forall E regs (r : bv 5) (n : nat), regs_ok E wvh_regs regs ->
  sr_get wvh_regs r = SOff n 0 -> ew E n = getr regs r.
Proof.
intros E regs r n HR Hs. pose proof (HR r) as H. rewrite Hs in H. cbn [sv_denot] in H.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. symmetry. exact H.
Qed.

(* ---- the back edge's increments (s5 += 1, s6 += 8, s9 += 56): the join's registers at counter i + 1 ---- *)
Lemma wvl_rf_next : forall X i (W : world SEGS) regs mem E E' srs (regs' : bvmap 5 word) mem',
  wvl_rf X i W regs mem -> regs_ok E wvh_regs regs -> env_agree 55 E E' ->
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get wvh_regs r))
    [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%bv = true ->
  sr_get srs 21%bv = SOff 21 1 -> sr_get srs 22%bv = SOff 22 8 -> sr_get srs 25%bv = SOff 25 56 ->
  56 * Z.of_nat (S i) < 2 ^ 64 ->
  (forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  wvl_rf X (S i) W regs' mem'.
Proof.
intros X i W regs mem E E' srs regs' mem' HRF HR HA HRG Hcs H21 H22 H25 Hb HK.
assert (HP : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%bv -> getr regs' r = getr regs r)
  by (intros r Hr; apply (wvl_reg_mv E E' srs regs regs' r r HRG HR HA);
      exact (proj1 (forallb_forall _ _) Hcs r Hr)).
assert (HI : forall (r : bv 5) (n : nat) c v, sr_get srs r = SOff n c -> (n < 55)%nat ->
    sr_get wvh_regs r = SOff n 0 -> getr regs r = w64 v -> 0 <= v -> v + c < 2 ^ 64 -> 0 <= c ->
    getr regs' r = w64 (v + c)).
{ intros r n c v Hs Hn Hw Hv Hv0 Hvc Hc0. rewrite HRG, Hs. cbn [sv_denot]. destruct HA as [HAe _].
  rewrite (HAe n Hn), (wvl_ew_reg E regs r n HR Hw), Hv. unfold w64.
  rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616 in *; lia). reflexivity. }
assert (RW : forall off, rdword (aview SEGS (w_H W) mem') (y_sp X - 176 + off) =
    rdword (aview SEGS (w_H W) mem) (y_sp X - 176 + off))
  by (intros off; apply wv_rdword_ext; intros j Hj; apply HK).
unfold wvl_rf in HRF |- *. cbv beta zeta in HRF |- *.
destruct HRF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168).
change (2 ^ 64) with 18446744073709551616 in Hb.
split; [rewrite (HP 2%bv ltac:(cbn [In]; auto 20)); exact G2|].
split; [rewrite (HP 3%bv ltac:(cbn [In]; auto 20)); exact G3|].
split; [rewrite (HP 4%bv ltac:(cbn [In]; auto 20)); exact G4|].
split; [rewrite (HP 8%bv ltac:(cbn [In]; auto 20)); exact G8|].
split; [rewrite (HP 9%bv ltac:(cbn [In]; auto 20)); exact G9|].
split; [rewrite (HP 18%bv ltac:(cbn [In]; auto 20)); exact G18|].
split; [rewrite (HP 19%bv ltac:(cbn [In]; auto 20)); exact G19|].
split; [rewrite (HP 20%bv ltac:(cbn [In]; auto 20)); exact G20|].
split; [rewrite (HI 21%bv 21%nat 1 (Z.of_nat i) H21 ltac:(lia) eq_refl G21) by lia; f_equal; lia|].
split; [rewrite (HI 22%bv 22%nat 8 (8 * Z.of_nat i) H22 ltac:(lia) eq_refl G22) by lia; f_equal; lia|].
split; [rewrite (HP 23%bv ltac:(cbn [In]; auto 20)); exact G23|].
split; [rewrite (HP 24%bv ltac:(cbn [In]; auto 20)); exact G24|].
split; [rewrite (HI 25%bv 25%nat 56 (56 * Z.of_nat i) H25 ltac:(lia) eq_refl G25) by lia; f_equal; lia|].
split; [rewrite (HP 26%bv ltac:(cbn [In]; auto 20)); exact G26|].
split; [rewrite (HP 27%bv ltac:(cbn [In]; auto 20)); exact G27|].
repeat (split; [rewrite RW; assumption|]). rewrite RW. assumption.
Qed.
End l0b.


(* ---- THE LOOP'S SEGMENTS (write_value's item loop, slots 153 .. 236 of its listing), each from a join of the body at
   item counter i (wvl_st: wv_common after the pieces P, the head's registers and frame words) to the container's final
   post wv_Qfin, given the loop head at i + 1 (wvl_next). The joins: 153 the head (P = wv_done X i), 158 after the
   comma (wvl_PA), 162 after the indent (wvl_PB), 181 after an object's key (wvl_Pk), 185 before the value (wvl_PD),
   193 after the value (wv_done X (S i)), 210 after the closing indent (wvl_seg_210). wv_loop chains them by induction
   on the items left. ---- *)
Definition wvl_next (X : wvx) (j : nat) : Prop :=
  forall (fxc : YK11.FPState) P lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc,
    wv_head (fx := fxc) X j P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
      (wv_Qfin X).

(* the write premise of a run from a seated (or seated-then-run) state: no write window *)
Local Ltac wvl_awr := first [ apply wvl_awr_ok
  | cbn [ss_mem add_cond]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]] ].

(* the memory a run from a seat leaves: every byte kept *)
Local Ltac wvl_kept K HF HFr HG :=
  lazymatch type of HFr with frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
    pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K end;
  clear HF HFr HG.

Section s193. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* ---- AFTER THE VALUE (write_value + 4 * 193): v's shadow check, `ld n`, the increments, the `bltu` back edge: to
   the head at i + 1 (HNEXT), or past the last item to the closing indent (slot 209) and the close ---- *)
Lemma wvl_seg_193 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := y_fx X) X ch -> (i < wv_nitems (y_t X))%nat ->
  wvl_st X i (wv_done X (S i)) lyc Sc Hpc Wc regs memc mdc kc -> wvl_next X (S i) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVL_PC 193)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hi Hst HNEXT.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & Hdd & _).
pose proof Hst as (Hcom & Hrf).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
assert (Hn : (0 < wv_nitems (y_t X))%nat) by lia.
destruct (wvl_node_facts X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom Hn) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvl_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (_ & Hk4096 & _ & Hkc & _).
pose proof (wvl_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 193) false kids keys nn cap 0 HSTKn Hpre
  Hst ltac:(lia) Hn Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvl_E X i regs kids keys nn 0) in *.
pose proof Hcom as (HJ & _ & HPM & _).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (Hnn64 : 0 <= nn < 2 ^ 64) by (clear - Hnn Hncap Hkc Hk4096 HCV; zl).
assert (Hb56 : 56 * Z.of_nat (S i) < 2 ^ 64) by (clear - Hi Hnn Hncap Hkc Hk4096 HCV; zl).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; zl).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (wvl_ew_reg E regs 21%bv 21%nat Hregs eq_refl); exact G21).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
(* 193 .. 199: v's shadow check, `ld n`, the increments; stuck at the `bltu` *)
all: paj_run_tok_x_inv RUNI
  HS HJ SHOK HPM WV_Bspan; [apply wvl_awr_ok | ].
all: lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
       pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K1 end.
all: clear HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
       assert (HA1 : env_agree 55 E E1) by wvl_agree end.
all: psrr_branch_tok RUNI
  BR HS SHOK WV_Bspan.
(* the back edge's condition: i + 1 < n (the run made no fresh atom: E1 is E, and the U_agree steps are then
   no-ops) *)
all: rewrite branch_ltu_U in Hc; try rewrite (U_agree 55 E _ (SOff 21 1) HA1 eq_refl) in Hc;
     try rewrite (U_agree 55 E _ (SOff 38 0) HA1 eq_refl) in Hc;
     rewrite (U_atom_off E 21 (Z.of_nat i) 1 E21), (U_atom E 38 nn E38) in Hc by (clear - Hb56 Hnn64; zl).
(* taken: on to the head (slot 153); not taken: 200 `j`, 205 `ld dep`, 206 `beqz n` (n <> 0), the closing indent's
   `jal` at 209 *)
all: lazymatch type of Hc with
     | _ = true =>
         apply Z.ltb_lt in Hc;
         paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM WV_Bspan (WVL_PC 153);
         [ cbn [ss_mem add_cond]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]] | ]
     | _ = false =>
         apply Z.ltb_ge in Hc;
         paj_run_tok_x_inv RUNI
           HS HJ SHOK HPM WV_Bspan;
         [ cbn [ss_mem add_cond]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]] | ]
     end.
all: lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
       pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K2 end.
all: clear HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with
     | st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) =>
       (* the back edge: the head at i + 1 *)
       lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] =>
         replace c with WVH_PC by (unfold WVH_PC; first [reflexivity | vm_compute; reflexivity]) end;
       pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E2 ss2 ms2 r HS) as HRG;
       assert (HA : env_agree 55 E E2) by wvl_agree;
       assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
         by (intros a; rewrite K2; apply K1);
       apply (HNEXT fx (wv_done X (S i)) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc);
       apply wvl_st_head; [ split | clear - Hc Hnn; lia | reflexivity ];
       [ exact (wvl_common_run X _ lyc Sc Hpc Wc memc mdc kc (ms_mem ms2) _ Hcom Ho0 Ho64 HJ HPM KM)
       | exact (wvl_rf_next X i Wc regs memc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) Hrf Hregs HA HRG
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) Hb56 KM) ]
     | st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
       (* the exit: the closing indent at depth dep, then the close (wvl_seg_210) *)
       assert (HSi : S i = wv_nitems (y_t X)) by (clear - Hc Hi Hnn; lia);
       pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
       assert (HA : env_agree 55 E E2) by wvl_agree;
       assert (HEI2 : img_env VAL A_LIM E2) by assumption;
       assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
         by (intros a; rewrite K2; apply K1);
       lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md2) _ =>
       assert (Hst2 : wvl_st X (S i) (wv_done X (S i)) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) md2 kc)
         by (split;
             [ exact (wvl_common_run X _ lyc Sc Hpc Wc memc mdc kc (ms_mem ms2) _ Hcom Ho0 Ho64 HJ HPM KM)
             | exact (wvl_rf_next X i Wc regs memc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) Hrf Hregs HA HRG
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) Hb56 KM) ]);
       rewrite HSi in Hst2;
       assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
         by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
               ltac:(vm_compute; reflexivity)); exact G8);
       assert (H11 : getr (ms_regs ms2) 11 = w64 (y_pretty X))
         by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 11%bv 19%bv HRG Hregs HA
               ltac:(vm_compute; reflexivity)); exact G19);
       assert (H12 : getr (ms_regs ms2) 12 = w64 (y_dep X))
         by (exact (wvl_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 12%bv 33%nat _ HRG HA ltac:(vm_compute; reflexivity)
               ltac:(lia) E33));
       assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVL_PC 210))
         by (exact (wvl_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 210 HRG HEI2 ltac:(vm_compute; reflexivity)));
       destruct (wvl_ret_ok 210 ltac:(lia)) as (Hr4096 & Hrok);
       apply (wvl_site_indent n' X ch (wv_nitems (y_t X)) (wv_done X (wv_nitems (y_t X)))
         [[if wv_tagc (y_t X) =? 6 then 125 else 93]] (y_dep X) (WVL_PC 210) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2)
         md2 kc HSTKn Hpre Hst2 (wvl_pcs_end X Hn) ltac:(clear - Hdep; zl) H10 H11 H12 Hra Hrok Hr4096 wvl_ceil_210);
       intros ly4 S4' Hp4 W4 regs4 mem4 md4 k4 Hst4;
       exact (wvl_seg_210 n' X ch ly4 S4' Hp4 W4 regs4 mem4 md4 k4 HSTKn Hpre Hn Hst4)
       end
     end.
Qed.
End s193.

Section s185. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* a word the memory holds is determined by its bytes' view *)
Lemma wvl_rd_u64_det : forall (H : word -> bool) (m1 m2 : word -> option byte) a v1 v2,
  (forall x, aview SEGS H m2 x = aview SEGS H m1 x) ->
  rd_u64 SEGS (mrestrict H m1) a v1 -> rd_u64 SEGS (mrestrict H m2) a v2 -> v2 = v1.
Proof.
intros H m1 m2 a v1 v2 HK (R1 & V1) (R2 & V2).
pose proof (wvp_rdword_of_val_mem0 H m1 a v1 V1) as W1.
pose proof (wvp_rdword_of_val_mem0 H m2 a v2 V2) as W2.
rewrite (wv_rdword_ext (aview SEGS H m1) (aview SEGS H m2) a) in W2 by (intros j _; apply HK).
rewrite W1 in W2. injection W2 as E. rewrite !Z.mod_small in E by lia. lia.
Qed.

(* ---- BEFORE THE VALUE (write_value + 4 * 185): v + 24's shadow check, kids[i] = kids + 56 i (the seat's alias, atom
   41), the recursive call at slot 192 (return 193) on the child at depth n' ---- *)
Lemma wvl_seg_185 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre (fx := y_fx X) X ch -> (i < wv_nitems (y_t X))%nat ->
  wvl_st X i (wvl_PD X i) lyc Sc Hpc Wc regs memc mdc kc -> wvl_next X (S i) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVL_PC 185)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Hst HNEXT.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV0.
pose proof Hst as (Hcom & Hrf).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
destruct (wvl_node_facts X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 185) false kids keys nn cap 0 HSTKn Hpre
  Hst ltac:(lia) ltac:(lia) Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvl_E X i regs kids keys nn 0) in *.
pose proof (wvl_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
pose proof Hcom as (HJ & _ & HPM & _).
assert (Hdt2 : (PjTree.depth (wvl_child X i) < PjTree.depth (y_t X))%nat).
{ clear - Hi. unfold wvl_child, wv_nitems in *. destruct (y_t X); cbn [length] in Hi; try lia.
  - apply wvl_depth_arr. exact Hi.
  - apply wvl_depth_obj. exact Hi. }
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM WV_Bspan; [wvl_awr | ].
all: wvl_kept K1 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvl_agree;
  assert (HEI2 : img_env VAL A_LIM E2) by assumption;
  pose proof (wvl_st_run X i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2;
  destruct (wvl_item_facts X ch _ lyc Sc Hpc Wc (ms_mem ms2) _ kc i HSTK Hpre (proj1 Hst2) Hi) as
    (kids' & keys' & nn' & cap' & D1 & Vtg' & Rkids' & Rkeys' & Rnn' & Hnn' & Hncap' & Hcap' & Hkb' & HN1 & HD1 &
     _ & _);
  pose proof (wvl_rd_u64_det (w_H Wc) memc (ms_mem ms2) (y_v X + 24) kids kids' K1 Rkids Rkids') as Ekids;
  subst kids';
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (kids + 56 * Z.of_nat i))
    by exact (wvl_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 41%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E41);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (y_pretty X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 12%bv 19%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G19);
  assert (H13 : getr (ms_regs ms2) 13 = w64 (y_dep X + 1))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 13%bv 24%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G24);
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVL_PC 193))
    by exact (wvl_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 193 HRG HEI2 ltac:(vm_compute; reflexivity));
  assert (Hv2 : exists x y, In (x, y) (y_D X) /\ x <= kids + 56 * Z.of_nat i /\
      kids + 56 * Z.of_nat i + 56 <= x + y)
    by (exists kids, (56 * cap'); split; [exact Hkb' | clear - Hi Hnn' Hncap'; split; lia]);
  apply (wvl_site_self n' X ch i (wvl_PD X i) (wvl_rest X (S i)) (kids + 56 * Z.of_nat i) (wvl_child X i) D1
    (WVL_PC 193) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc IH HSTKn Hdn Hpre Hst2 (wvl_pcs_D X i Hi) HN1 Hdt2
    HD1 Hv2 H10 H11 H12 H13 Hra (proj2 (wvl_ret_ok 193 ltac:(lia))) (proj1 (wvl_ret_ok 193 ltac:(lia)))
    wvl_ceil_193);
  intros fx' ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  rewrite <- (wvl_done_D X i Hi) in Hst3;
  exact (@wvl_seg_193 fx' n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 HSTKn Hpre Hi Hst3 HNEXT)
end.
Qed.
End s185.

Section s181. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* ---- AFTER AN OBJECT'S KEY (write_value + 4 * 181): the separator put at slot 184 (return 185), its literal from the
   frame word R + 40 and its length (pretty <> 0) + 1 from R + 32 ---- *)
Lemma wvl_seg_181 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre (fx := y_fx X) X ch -> (i < wv_nitems (y_t X))%nat -> wv_tagc (y_t X) = 6 ->
  wvl_st X i (wvl_Pk X i) lyc Sc Hpc Wc regs memc mdc kc -> wvl_next X (S i) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVL_PC 181)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Ht Hst HNEXT.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV0.
pose proof Hst as (Hcom & Hrf).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
destruct (wvl_node_facts X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 181) false kids keys nn cap 0 HSTKn Hpre
  Hst ltac:(lia) ltac:(lia) Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvl_E X i regs kids keys nn 0) in *.
pose proof (wvl_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
pose proof Hcom as (HJ & _ & HPM & _).
assert (E19 : ew E 19 = Z_to_bv 64 (y_pretty X))
  by (rewrite (wvl_ew_reg E regs 19%bv 19%nat Hregs eq_refl); exact G19).
assert (EPD : wvl_PD X i = wvl_Pk X i ++ [WriterValue.wsep (y_p X)])
  by (unfold wvl_PD, wvl_Ps, wv_tagc in *; destruct (y_t X); try discriminate Ht; reflexivity).
rewrite Ht in HS.
paj_run_tok_x_inv RUNI HS HJ SHOK HPM WV_Bspan; [wvl_awr | ].
wvl_kept K1 HF HFr HG.
pmkst HS.
lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvl_agree;
  assert (HEI2 : img_env VAL A_LIM E2) by assumption;
  pose proof (wvl_st_run X i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2;
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (WV_STR (wv_sep_slot X)))
    by exact (wvl_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 34%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E34);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (Z.of_nat (length (WriterValue.wsep (y_p X)))));
  [ rewrite HRG;
    replace (sr_get (ss_regs ss2) 12%bv) with (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1))
      by (vm_compute; reflexivity);
    try rewrite (sv_denot_agree 55 E E2 (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)) HA eq_refl);
    rewrite (wvl_p1_denot E (y_pretty X) E19 Hpr);
    unfold y_p, WriterValue.wsep; destruct (y_pretty X =? 0); reflexivity
  | ];
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVL_PC 185))
    by exact (wvl_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 185 HRG HEI2 ltac:(vm_compute; reflexivity));
  apply (wvl_site_put n' X ch i (wvl_Pk X i)
    (WriterValue.wvpieces (wvl_child X i) (y_p X) (y_dep X + 1) ++ wvl_rest X (S i)) (wv_sep_slot X)
    (WriterValue.wsep (y_p X)) (WVL_PC 185) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc HSTKn Hpre Hst2
    (wvl_sep_lit X) (wvl_pcs_k X i Hi Ht) H10 H11 H12 Hra (proj2 (wvl_ret_ok 185 ltac:(lia)))
    (proj1 (wvl_ret_ok 185 ltac:(lia))) wvl_ceil_185);
  intros ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  rewrite <- EPD in Hst3;
  exact (wvl_seg_185 n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 IH HSTKn Hdn Hpre Hi Hst3 HNEXT)
end.
Qed.
End s181.

Section s162. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* an array's join before the value is the one after the indent (no key, no separator) *)
Lemma wvl162_PD_arr : forall X i, wv_tagc (y_t X) = 5 -> wvl_PD X i = wvl_PB X i.
Proof. intros X i Ht. unfold wvl_PD. unfold wv_tagc in Ht. destruct (y_t X); try reflexivity. cbn in Ht. discriminate Ht. Qed.

(* ---- AFTER THE INDENT (write_value + 4 * 162): v's shadow check, the tag test (an array goes on to the value at
   slot 185); an object loads keys[i] (two shadow checks) and calls put_string on it (slot 180, return 181) ---- *)
Lemma wvl_seg_162 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre (fx := y_fx X) X ch -> (i < wv_nitems (y_t X))%nat ->
  wvl_st X i (wvl_PB X i) lyc Sc Hpc Wc regs memc mdc kc -> wvl_next X (S i) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVL_PC 162)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc HIS HSTKn Hdepth Hpre Hi Hst HNEXT.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hst as (Hcom & Hrf).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
destruct (wvl_item_facts X ch _ lyc Sc Hpc Wc memc mdc kc i HSTK Hpre Hcom Hi) as
  (kids & keys & nn & cap & D1 & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & _ & _ & Hk5 & Hk6).
pose proof Hcom as (HJ & _ & HPM & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht].
- (* an array: the tag test sends the run on to the value (slot 185) *)
  destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 162) false kids keys nn cap 0 HSTKn Hpre
    Hst ltac:(lia) ltac:(lia) Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 (fun H => proj1 (Hk6 H)) ltac:(discriminate))
    as (HEI & Hregs & HS & SHOK).
  set (E := wvl_E X i regs kids keys nn 0) in *.
  rewrite Ht in HS.
  paj_run_to_tok_x_inv RUNTOI
    HS HJ SHOK HPM WV_Bspan (WVL_PC 185); [apply wvl_awr_ok | ].
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K1 end.
  clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) =>
    pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E2 ss2 ms2 r HS) as HRG;
    assert (HA : env_agree 55 E E2) by wvl_agree;
    pose proof (wvl_st_run X i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _ Hst
      ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2
  end.
  rewrite <- (wvl162_PD_arr X i Ht) in Hst2.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?n)) _ _) _) _ =>
    replace n with (WVL_PC 185) by (unfold WVL_PC; vm_compute; reflexivity) end.
  exact (wvl_seg_185 n' X ch i lyc Sc Hpc Wc _ _ _ kc HIS HSTKn Hdepth Hpre Hi Hst2 HNEXT).
- (* an object: keys[i] (the seat's key slot, its word x the key string) and the put_string call (slot 180) *)
  destruct (Hk6 Ht) as (Hkb6 & x & k & HxD & Rx & Hcs).
  destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 162) true kids keys nn cap x HSTKn Hpre
    Hst ltac:(lia) ltac:(lia) Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 (fun H => proj1 (Hk6 H))
    (fun _ => conj Hi (conj Ht Rx)))
    as (HEI & Hregs & HS & SHOK).
  pose proof (wvl_E_at X i regs kids keys nn x) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
  set (E := wvl_E X i regs kids keys nn x) in *.
  rewrite Ht in HS.
  paj_run_tok_x_inv RUNI
    HS HJ SHOK HPM WV_Bspan; [apply wvl_awr_ok | ].
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (wvl_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K1 end.
  clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
    pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
    assert (HA : env_agree 55 E E2) by wvl_agree;
    assert (HEI2 : img_env VAL A_LIM E2) by assumption;
    pose proof (wvl_st_run X i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _ Hst
      ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2;
    assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
      by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
            ltac:(vm_compute; reflexivity)); exact G8);
    assert (H11 : getr (ms_regs ms2) 11 = w64 x)
      by (exact (wvl_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 40%nat _ HRG HA ltac:(vm_compute; reflexivity)
            ltac:(lia) E40));
    assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVL_PC 181))
      by (exact (wvl_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 181 HRG HEI2 ltac:(vm_compute; reflexivity)));
    assert (Hcs2 : pj_cstrR SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (prh_lin (y_Lam X)) x k (wvl_key X i))
      by (eapply pj_cstrR_frame; [exact Hcs | intros a _; apply (mbyte_of_aview SEGS); apply K1]);
    destruct (wvl_ret_ok 181 ltac:(lia)) as (Hr4 & Hrok);
    exact (wvl_site_put_string n' X ch i (wvl_PB X i) _ x k (WVL_PC 181) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc
      HSTKn Hpre Hst2 (wvl_pcs_B X i Hi Ht) HxD Hcs2 H10 H11 Hra Hrok Hr4 wvl_ceil_181
      (fun fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Hst3 =>
         @wvl_seg_181 fx' n' X ch i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HIS HSTKn Hdepth Hpre Hi Ht Hst3 HNEXT))
  end.
Qed.
End s162.

Section s158. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* ---- AFTER THE COMMA (write_value + 4 * 158): indent (o, pretty, dep + 1) at slot 161 (return 162) ---- *)
Lemma wvl_seg_158 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre (fx := y_fx X) X ch -> (i < wv_nitems (y_t X))%nat ->
  wvl_st X i (wvl_PA X i) lyc Sc Hpc Wc regs memc mdc kc -> wvl_next X (S i) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVL_PC 158)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Hst HNEXT.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV0.
pose proof Hst as (Hcom & Hrf).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & Hdd & _).
assert (Hdep1 : - 2 ^ 31 <= y_dep X + 1 < 2 ^ 31)
  by (pose proof (wvl_depth_pos (y_t X) ltac:(lia)) as Hd1; clear - Hdep Hdd Hd1; zl).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
destruct (wvl_node_facts X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 158) false kids keys nn cap 0 HSTKn Hpre
  Hst ltac:(lia) ltac:(lia) Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvl_E X i regs kids keys nn 0) in *.
pose proof Hcom as (HJ & _ & HPM & _).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM WV_Bspan; [wvl_awr | ].
all: wvl_kept K1 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvl_agree;
  assert (HEI2 : img_env VAL A_LIM E2) by assumption;
  pose proof (wvl_st_run X i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2;
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (y_pretty X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 11%bv 19%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G19);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (y_dep X + 1))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 12%bv 24%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G24);
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVL_PC 162))
    by exact (wvl_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 162 HRG HEI2 ltac:(vm_compute; reflexivity));
  apply (wvl_site_indent n' X ch i (wvl_PA X i) (wvl_itail X i ++ wvl_rest X (S i)) (y_dep X + 1) (WVL_PC 162)
    lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc HSTKn Hpre Hst2 (wvl_pcs_A X i Hi) Hdep1 H10 H11 H12 Hra
    (proj2 (wvl_ret_ok 162 ltac:(lia))) (proj1 (wvl_ret_ok 162 ltac:(lia))) wvl_ceil_162);
  intros ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  exact (wvl_seg_162 n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 IH HSTKn Hdn Hpre Hi Hst3 HNEXT)
end.
Qed.
End s158.

Section s153. Context {fx : YK11.FPState}.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let BR := paj_branchR (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* ---- THE HEAD (write_value + 4 * 153): `beqz s5`: item 0 goes to slot 158 directly; item i > 0 first puts the comma
   (the literal at R + 56, slot 157, return 158) ---- *)
Lemma wvl_seg_153 : forall n' X ch i P lyc Sc Hpc Wc regs memc mdc kc,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre (fx := y_fx X) X ch -> wv_head X i P lyc Sc Hpc Wc regs memc mdc kc -> wvl_next X (S i) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch i P lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hh HNEXT.
destruct (wvl_head_st X i P lyc Sc Hpc Wc regs memc mdc kc Hh) as (Hst & Hi & HP). subst P.
destruct (wvl_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 176 <= y_STK X) by lia.
destruct (wvl_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV0.
pose proof Hst as (Hcom & Hrf).
destruct (wvl_rf_regs X _ Wc regs memc Hrf) as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G24 & G25).
destruct (wvl_node_facts X ch _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvl_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (_ & Hk4096 & _ & Hkc & _).
destruct (wvl_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVL_PC 153) false kids keys nn cap 0 HSTKn Hpre
  Hst ltac:(lia) ltac:(lia) Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvl_E X i regs kids keys nn 0) in *.
pose proof (wvl_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
pose proof Hcom as (HJ & _ & HPM & _).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (Hi64 : 0 <= Z.of_nat i < 2 ^ 64) by (clear - Hi Hnn Hncap Hkc Hk4096 HCV; zl).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite (wvl_ew_reg E regs 21%bv 21%nat Hregs eq_refl); exact G21).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
all: change (BASE + WVH_PC) with (BASE + WVL_PC 153).
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM WV_Bspan; [wvl_awr | ].
all: wvl_kept K1 HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA1 : env_agree 55 E E1) by wvl_agree end.
all: psrr_branch_tok RUNI BR HS SHOK WV_Bspan.
all: rewrite branch_eq_U in Hc; try rewrite (U_agree 55 E _ (SOff 21 0) HA1 eq_refl) in Hc;
  rewrite (U_atom E 21 (Z.of_nat i) E21 Hi64), U_SLit, (zcanon_id 0) in Hc by (unfold M64; zl).
(* item 0: on to slot 158 *)
1, 3: apply Z.eqb_eq in Hc; assert (Hi0 : i = 0%nat) by lia; subst i;
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM WV_Bspan (WVL_PC 158); [wvl_awr | ];
  wvl_kept K2 HF HFr HG;
  pmkst HS;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] => replace c with (WVL_PC 158) by (vm_compute; reflexivity) end;
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) =>
    pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E2 ss2 ms2 r HS) as HRG;
    assert (HA : env_agree 55 E E2) by wvl_agree;
    assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
      by (intros a; rewrite K2; apply K1);
    pose proof (wvl_st_run X 0 _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
      Hst ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM KM) as Hst2;
    rewrite <- (wvl_PA_0 X) in Hst2;
    exact (wvl_seg_158 n' X ch 0 lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc IH HSTKn Hdn Hpre Hi Hst2 HNEXT)
  end.
(* item i > 0: the comma *)
all: apply Z.eqb_neq in Hc; assert (Hi0 : i <> 0%nat) by lia.
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM WV_Bspan; [wvl_awr | ].
all: wvl_kept K2 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvl_agree;
  assert (HEI2 : img_env VAL A_LIM E2) by assumption;
  assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
    by (intros a; rewrite K2; apply K1);
  pose proof (wvl_st_run X i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst ltac:(zl) ltac:(zl) Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM KM) as Hst2;
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvl_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (WV_STR 151))
    by exact (wvl_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 35%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E35);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (Z.of_nat (length [44])))
    by exact (wvl_reg_lit E2 (ss_regs ss2) (ms_regs ms2) 12%bv 1 HRG ltac:(vm_compute; reflexivity));
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVL_PC 158))
    by exact (wvl_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 158 HRG HEI2 ltac:(vm_compute; reflexivity));
  apply (wvl_site_put n' X ch i (wv_done X i)
    (WriterValue.wind (y_p X) (y_dep X + 1) ++ wvl_itail X i ++ wvl_rest X (S i)) 151%nat [44] (WVL_PC 158)
    lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc HSTKn Hpre Hst2 ltac:(cbn; auto 20) (wvl_pcs_comma X i Hi Hi0)
    H10 H11 H12 Hra (proj2 (wvl_ret_ok 158 ltac:(lia))) (proj1 (wvl_ret_ok 158 ltac:(lia))) wvl_ceil_158);
  intros ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  rewrite (wvl_PA_comma X i Hi0) in Hst3;
  exact (wvl_seg_158 n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 IH HSTKn Hdn Hpre Hi Hst3 HNEXT)
end.
Qed.
End s153.

(* ---- THE ITEM LOOP: from the head at item i, at ANY current float state fxc (the head's wv_common carries its
   frm_zero and fs0-fs11 relation to the entry's), to the container's final post, by induction on the items left
   (the internal file REFIT-WRITER.md's float-threading design point 6) ---- *)
Lemma wv_loop : forall (n' : nat) (X : wvx) ch, (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') ->
  STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat -> wv_pre (fx := y_fx X) X ch ->
  forall (fxc : YK11.FPState) i P lyc Sc Hpc Wc regsc memc mdc kc,
  wv_head (fx := fxc) X i P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin X).
Proof.
intros n' X ch IH HSTKn Hdn Hpre.
assert (KEY : forall m i, (wv_nitems (y_t X) - i = m)%nat -> wvl_next X i).
{ induction m as [|m IHm]; intros i Hm fxc P lyc Sc Hpc Wc regsc memc mdc kc Hh.
  - exfalso. destruct Hh as (_ & Hi & _). lia.
  - apply (@wvl_seg_153 fxc n' X ch i P lyc Sc Hpc Wc regsc memc mdc kc IH HSTKn Hdn Hpre Hh).
    apply (IHm (S i)). destruct Hh as (_ & Hi & _). lia. }
intros fxc i P lyc Sc Hpc Wc regsc memc mdc kc Hh.
exact (KEY _ i eq_refl fxc P lyc Sc Hpc Wc regsc memc mdc kc Hh).
Qed.

End cont.

(* ======== THE INTERIM THEOREM: write_value at every depth ======== *)
(* the stack need at depth 0 covers each leaf's tail callee (numerals of the instance) *)
Lemma wv_stk_mono : forall n, STK_write_value 0 <= STK_write_value n.
Proof.
intros n. unfold STK_write_value.
assert (Hf : 0 <= pi_frame F_write_value) by (vm_compute; congruence).
assert (Hn : 1 <= Z.of_nat (S n)) by lia. nia.
Qed.
Lemma wv_stk_leaf : 184 + STK_RT_STR <= STK_write_value 0 /\ STK_put <= STK_write_value 0 /\
  STK_put_string <= STK_write_value 0.
Proof. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* the text from the container's two lemmas (wv_cont at the entry float state, wv_loop at every current float
   state): for every depth n and every entry float state fx; write_value_holds below instantiates it *)
Lemma wv_specI_of :
  (forall (Pm : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS Pm)
  (PCALL : srr_inv_call SEGS Pm) (fx : YK11.FPState) (n' : nat) (X : wvx) ch,
  (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
  STK_write_value (S n') <= y_STK X -> wv_pre (fx := fx) Pm X ch ->
  (forall i P lyc Sc Hpc Wc regsc memc mdc kc, wv_head (fx := fx) Pm X i P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
       (wv_Qfin Pm X)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (y_W X) (cfg_at SEGS (SIGMA AS_write_value) (y_regs X) (y_mem X) (y_md X))
    (wv_Qfin Pm X)) ->
  (forall (Pm : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS Pm)
  (PCALL : srr_inv_call SEGS Pm) (n' : nat) (X : wvx) ch,
  (forall fx0 : YK11.FPState, twrite_value_specI (fx := fx0) n') -> STK_write_value (S n') <= y_STK X ->
  (PjTree.depth (y_t X) <= S n')%nat -> wv_pre (fx := y_fx X) Pm X ch ->
  forall (fxc : YK11.FPState) i P lyc Sc Hpc Wc regsc memc mdc kc,
  wv_head (fx := fxc) Pm X i P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin Pm X)) ->
  forall n (fx : YK11.FPState), twrite_value_specI (fx := fx) n.
Proof.
intros CONT LOOP.
pose proof wv_stk_leaf as (SL1 & SL2 & SL3).
assert (SL0 : 0 <= STK_RT_STR) by (apply Z.leb_le; vm_compute; reflexivity).
induction n as [|n' IH];
  intros fx rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o v pretty dep d buf st t D Lam peak
    ran HPRE Hroom Hrp Hos4 Hcons Hcl H10 H11 H12 H13 Hpr Hdep Hdd Hdn Hcut Hch0 HS0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA
    HTV HD Hoff Hfr Hwmax Hhead Hlive.
all: destruct t as [ | | | txt bits | s | items | members ].
all: lazymatch type of HNODE with
  | pj_nodeR _ _ _ _ PjTree.JNull _ =>
      eapply (wv_leaf_lit PjTree.JNull (or_introl eq_refl) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch)
  | pj_nodeR _ _ _ _ PjTree.JFalse _ =>
      eapply (wv_leaf_lit PjTree.JFalse (or_intror (or_introl eq_refl)) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W
        regs mem md ch)
  | pj_nodeR _ _ _ _ PjTree.JTrue _ =>
      eapply (wv_leaf_lit PjTree.JTrue (or_intror (or_intror eq_refl)) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W
        regs mem md ch)
  | pj_nodeR _ _ _ _ (PjTree.JNum ?txt ?bits) _ =>
      eapply (wv_leaf_num txt bits rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch)
  | pj_nodeR _ _ _ _ (PjTree.JStr ?s) _ =>
      eapply (wv_leaf_str s rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch)
  | _ => idtac
  end.
all: try eassumption.
all: try (match goal with |- context [STK_write_value ?m] => pose proof (wv_stk_mono m) end; lia).
(* depth 0: a container has depth at least 1 *)
1, 2: exfalso; cbn [PjTree.depth] in Hdn; lia.
(* depth S n': the container walk, at Pm := the memnorm keep from the entry *)
all: lazymatch type of HNODE with pj_nodeR _ _ _ _ ?tt _ =>
  pose (X := mkWVX d (STK_write_value (Datatypes.S n')) ly S Hp W regs mem md o v pretty dep buf st tt D Lam peak ran
    rp_sm rp_x rp_os rp_i rp_H0 rp_hist fx most own) end.
all: pose (Pm := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
all: assert (PLAW : srr_inv_laws SEGS Pm) by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
all: assert (PCALL : srr_inv_call SEGS Pm) by (apply srr_inv_call_imp).
all: assert (HP : wv_pre (fx := fx) Pm X ch)
  by exact (conj HPRE (conj Hroom (conj Hrp (conj Hcl (conj H10 (conj H11 (conj H12 (conj H13 (conj Hpr (conj Hdep
    (conj Hdd (conj Hcut (conj HWIN (conj Ho1 (conj Ho2 (conj HOUT (conj HLED (conj HNODE (conj HLOC (conj HRA (conj HTV
    (conj HD (conj Hoff (conj Hfr (conj Hwmax (conj Hhead (conj Hlive (conj (fun h => h) (conj Hcons (conj HS0
    (conj Hch0 (conj Hev (conj eq_refl Hos4))))))))))))))))))))))))))))))))).
all: assert (HSH : (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l))
  by first [exact (or_introl (ex_intro _ _ eq_refl)) | exact (or_intror (ex_intro _ _ eq_refl))].
all: pose proof (CONT Pm PLAW PCALL fx n' X ch HSH (Z.le_refl _) HP
  (LOOP Pm PLAW PCALL n' X ch IH (Z.le_refl _) Hdn HP fx)) as HC.
all: eapply SRr'_mono; [exact HC|].
all: intros W2 c2 _ ((fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k & Hc2 & HZ2 & HF2 & HJ2 & HK2 & HP2 & HQ) & HPm2).
all: exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k.
all: split; [exact Hc2|]; split; [exact HZ2|]; split; [exact HF2|]; split; [exact HJ2|]; split; [exact HK2|].
all: split; [exact HP2|].
all: split; [exact HQ | subst c2; exact HPm2].
Qed.

(* rule 24: proves function write_value (CONFIRM R24Writer 2026-10-30). The batch kit's twrite_value_specX at every depth n and
   every entry float state fx, from the container's two lemmas and the leaves (wv_specI_of), under this Section's
   callee texts PUT / PUTSTR / INDENT, the strlen row STRLEN and the head width HW. *)
Theorem write_value_holds : forall (fx : YK11.FPState) n,
  twrite_value_specX (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0 n.
Proof.
intros fx n.
refine (wv_specI_of _ _ n fx).
- intros. eapply wv_cont; eassumption.
- intros. eapply wv_loop; eassumption.
Qed.

End cl.

(* MEASURED with the engine on this file's entry state (kit preset-tree-at-2026-10-29T11-21-15Z.tsv (sha256 51e240de380a; internal record) + engine pair preset-tree-at-2026-10-29T11-42-54Z.tsv (sha256 acc5c08e4c49; internal record)): from wv_ss2 tg
   the run reaches the switch's `jr` at write_value + 4 * 35 with a1 = SAlu ALU_ADD (SOff 38 WV_JT) (SOff (A_OBJ 2)
   0); the literal cases run to AF + 4 * 236 and stop BEFORE the tail `j put` with a0 = the entry a0 (= o), a1 =
   SOff (A_OBJ 2) (wv_addhi_off slot), a2 = SLit (length), ra / sp / s0 .. s11 = their entry atoms; one more run step
   stops at put's entry in st_ok form with the env unchanged. wv_leaf_lit (Qed) closes the three literal leaves.
   STATE (the batch kit re-fit): every segment lemma of the walk is Qed here (the leaves, wv_cont, the loop's segments,
   wv_loop, wv_specI_of) and write_value_holds composes them. See the internal file PRW_write_value.NEXT.md. *)


End h.
End f.
End d.
