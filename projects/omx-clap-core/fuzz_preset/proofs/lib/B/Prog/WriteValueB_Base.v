(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d, unstripped twin c90d4fa54d43), lane
   of write_value, under a Theorem Labs session: the BASE of the walk of write_value (B' 0x87348, 291 instructions, self-recursive) over the
   ONE image-B' program listing (lib/B/Listing_prog.v c97cc46b3e13, PAImg_prog.v 15fab93fe702), generic in the image
   facts (Context PAImg) and in the allocator relation ARx (LAWS : AR_laws_x), toward the draft's text
   twrite_value_specX (lib/A/PRH_FnWriter.v, lib/A/PRH_Base.v).
   This file: the entry state, the tag switch, the keeps of write_value's own stretches, the tree / struct / ledger
   across a call, the chain helpers and the position composition. The call sites, the leaves, the container and the
   item loop are WriteValueB_Call / _Leaf / _Cont / _Loop.
   INSTRUCTION COMPARE: old B 0x86e58 vs B'
   0x87348, 1164 bytes both, words EQUAL-mod-pcrel (pcrel 25, real 0, unmeasured 0); 2 targets settled by measurement:
   the jump table +0x90 (7 entries, same symbol + offset), .str.1 +0x2fc (a name only): old-B and B' slots alike.
   TEMPLATE (ported, not cited): the kit owner's image-A walk lib/A/Prog/PRW_write_value.v on a working branch
   7819c4b4583 (blob 051bfb4b3368), its Sections d / f / h up to wv_ret_pos_app, restated at B's listing:
   - B's frame is 192 bytes (`addi sp, sp, -192`, slot 0; A's is 176), its jump table the PAddHi at slot 36 and its
     `jr a1` at slot 40, its case labels and its ten literals at B's own slots (wv_lits); A's item-loop head state
     is not here (B's is measured on B's listing, in WriteValueB_Cont);
   - B adds UBSan checks A has not: at entry `beqz a1` (v = NULL) and `bnez (v & 7)` (v misaligned), both resolved NOT
     TAKEN inside the engine's run from v's facts (4096 <= v, alignment 3), MEASURED (no obligation left);
   - #102 kit: the ledger's cells `most own` (prh_ledger .. ran most own), seven program statics (PST), kept_at per
     instance.
   NO IMAGE VALUE IS TYPED HERE: the function's offset is 4 * its generated slot (PAImg_prog B_prog_slot), and every
   .rodata address the code forms is read out of the generated listing (wv_addhi_off reads the addend of the PAddHi at
   a named slot), so a re-pin is a regeneration.
   Numerals: 4 (LENGTH: instruction bytes), 192 (LENGTH: write_value's own frame), 0 .. 56 (LENGTH: the node's field
   offsets and its size, PRH_Reader pj_hdrR), 2 ^ 46 / 2 ^ 47 (LENGTH: the stack atom's range), 2 ^ 44 (LENGTH: the
   shadow span), 6 (WORD: the largest tag, PjTree.tag), the slot numbers (DERIVED: (B pc - entry) / 4). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the function's place in the generated listing, and the .rodata addends the generated listing carries ----
   (no typed image value: both read a generated source) *)
Definition WV_SLOT : nat := B_prog_slot AS_write_value.
Definition AF_write_value : Z := 4 * Z.of_nat WV_SLOT.
(* the addend of the PAddHi / PLdHi at write_value + 4 k (the .rodata literal the code forms there) *)
Definition wv_addhi_off (k : nat) : Z :=
  match nth (WV_SLOT + k) B_prog_listing (PW 0) with
  | PAddHi _ _ _ _ off => off
  | PLdHi _ _ _ _ off _ _ => off
  | _ => 0
  end.
(* the jump table of the tag switch: the PAddHi at write_value + 4 * 36 (old B 0x86ee8) *)
Definition WV_JT : Z := wv_addhi_off 36.
(* the word of the switch's `jr a1` at write_value + 4 * 40 (old B 0x86ef8), read out of the listing *)
Definition WV_JR_W : Z := match nth (WV_SLOT + 40) B_prog_listing (PW 0) with PW w => w | _ => 0 end.

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

(* every lemma of this file abstracts EVERY Section variable, in declaration order, so the walk's other files
   can bind each by one `Let` at their own Section variables *)
#[local] Set Default Proof Using "All".
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Definition WV_Bx : sv := SOff 32 0.
Definition WV_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* the symbolic entry state: write_value's own frame, the GOT word and the shadow-base cell, and the tree node at v
   (read only: 56 bytes, its tag / str / kids / keys / n fields as chunks) *)
Definition wv_regions (tg : Z) : smem :=
  [ stack_region 192; got_regionP; bcell_regionP 32;
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

(* ---- the tag switch's jump table (old B 0x86ee4-0x86ef8): seven rel32 words at WV_JT, each the offset of its case
   label FROM THE TABLE. The case labels are slot deltas from write_value's entry (DERIVED, read off the image's
   table words, old B 0x213d8, and the listing: null 242, false 246, true 223, number 226, string 182, array / object
   41), not addresses. ---- *)
Definition WV_CASE (k : nat) : Z :=
  match k with
  | 0%nat => 242 | 1%nat => 246 | 2%nat => 223 | 3%nat => 226 | 4%nat => 182 | _ => 41
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


(* ---- the .rodata literals write_value puts, by the ATOM AND ADDEND the generated listing carries at the slot that
   forms them (no typed address): the PAddHi at write_value + 4 * k ---- *)
Definition wv_addhi_atom (k : nat) : nat :=
  match nth (WV_SLOT + k) B_prog_listing (PW 0) with
  | PAddHi _ _ _ a _ => a
  | PLdHi _ _ _ a _ _ _ => a
  | _ => O
  end.
Definition WV_STR (k : nat) : Z := VAL (wv_addhi_atom k) + wv_addhi_off k.
(* the ten literals write_value puts, by the slot of the PAddHi that forms each (read out of B_prog_listing; their
   bytes read off the image): null 243, false 247, true 224, "[" 44, "{" 47, ": " 54, ":" 57, "," 88, "]" 180,
   "}" 251 (and, unreachable under pj_nodeR, the empty string 191 for a NULL str and "0" 235 for a NULL number) *)
Definition wv_lits : list (nat * list Z) :=
  [ (243%nat, [110; 117; 108; 108]); (247%nat, [102; 97; 108; 115; 101]); (224%nat, [116; 114; 117; 101]);
    (44%nat, [91]); (47%nat, [123]); (54%nat, [58; 32]); (57%nat, [58]); (88%nat, [44]);
    (180%nat, [93]); (251%nat, [125]) ].


Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* image facts of the instance, discharged at PI_prog_B (B_entry_write_value / B_prog_obj_img) *)
Hypothesis Hent : SIGMA AS_write_value = BASE + AF_write_value.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* ---- IMAGE FACTS OF THE INSTANCE (discharged at PI_prog_B, WriteValueB_Inst), both read off the generated
   listing ----
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
(* IMAGE FACT (discharged at PI_prog_B, WriteValueB_Inst): no static of alloc.c lies in the read-only band, so
   a journal's image clause keeps the band (the same text as put_string's and pj_write's walks) *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).

(* the memory invariant the m-form posts keep (the fQmn over YAkMemnorm, PRH_Base.v blob ee6c7a38d6b6): each walk
   lemma instantiates the runner's invariant ONCE as `fun m => memnorm mem0 -> memnorm m` (srr_inv_laws_imp at
   srr_inv_laws_memnorm_k); each callee keep comes from that callee's own m-form post. *)
Let RUN := @paj_run_x fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).

(* two byte ranges, one in the image's segments and one in none, are disjoint (WalkS3's disj_img) *)
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
  192 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= spZ regs - 192 \/ spZ regs <= v) ->
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
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= sp - 192 \/ sp <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
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

(* ---- the tag switch's indirect jump (old B 0x86ef8, write_value + 4 * 40): a1 holds the case label the table word
   selects, so the walk goes on at the case's own offset. MEASURED with the engine on this file's entry state at
   tags 5 and 0 (old-pin probe, the internal file zfb-20261029T181701Z.log): the run from wv_ss2 tg stops
   at this pc with no obligation left and a1 = SAlu ALU_ADD (SOff 38 WV_JT) (SOff (A_OBJ 2) 0), that is
   jw + WV_JT + VAL (A_OBJ 2), which at jw = WV_JTW k is BASE + AF_wv_case k. ---- *)
Lemma wv_jr_step : forall E ss ms W md Q tgt,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_pc ss = AF_write_value + 4 * 40 ->
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
apply (SRr_jr_pi (PL := PL_prog_B) (PI := PA) W E ss ms md Q WV_JR_W (11%bv : bv 5) tgt HS Hrv).
- rewrite Hpc. vm_compute; reflexivity.
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
  192 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= spZ regs - 192 \/ spZ regs <= v) ->
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
  (VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= spZ regs - 192 \/ spZ regs <= VAL (A_OBJ 2) + WV_JT + 4 * tg) ->
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
assert (HJT0 : 0 <= WV_JT < 2 ^ 32) by (unfold WV_JT, wv_addhi_off, WV_SLOT; vm_compute; split; congruence).
pose proof (wv_case_bounds k) as HAF. pose proof (pa_val_range (A_OBJ 2)) as HV.
pose proof (@pa_B_ok _ B_prog_listing PA) as (HB0 & HB1 & HB4).
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



(* a pair of integers has a decidable equality (for the "block still live" case split) *)
Lemma wv_zz_dec : forall p q : Z * Z, {p = q} + {p <> q}.
Proof.
intros [p1 p2] [q1 q2]. destruct (Z.eq_dec p1 q1) as [->|H1]; [|right; congruence].
destruct (Z.eq_dec p2 q2) as [->|H2]; [left; reflexivity | right; congruence].
Qed.

(* ---- THE LEDGER: read through the named projections (PRH_Base.v d1cbe3c301d6, Section ledger_proj) only; these
   three and wv_led_keep are the walk's one place for them ---- *)
Lemma wv_led_hbs : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  forall ak, In ak Lam -> prh_hblock (PA := PA) B ly S Hp W mem (fst ak) (snd ak).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own LG. pose proof LG as HF. apply prh_ledger_blocks in HF.
rewrite Forall_forall in HF. exact HF.
Qed.

Lemma wv_led_nodup : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> NoDup (map fst Lam).
Proof. intros ly S Hp W mem Lam peak cnt fail ran most own LG. apply prh_ledger_nodup in LG. exact LG. Qed.

Lemma wv_led_cnt : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= cnt.
Proof. intros ly S Hp W mem Lam peak cnt fail ran most own LG. apply prh_ledger_bounds in LG. lia. Qed.

(* ---- A TREE BLOCK ACROSS A CALL: a byte of a live harness block OTHER THAN THE BUFFER, outside the struct, is kept
   by the journal (its block cannot have gone: a gone block's every byte is in FP). Over a world relation R (the
   journal at R; no law of R is used); wv_blk_keep below is its instance at wle ---- *)
Lemma wv_blk_keepR : forall (R : world SEGS -> world SEGS -> Prop) ly S Hp W mem md o buf cap Lam peak cnt fail ran
    most own a k0 x
    ly2 S2 Hp2 W2 mem2 md2 STK0 sp0 k,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k0) Lam -> a <> buf -> a <= x < a + k0 ->
  0 <= cap -> (cap <> 0 -> In (buf, cap) Lam) ->
  ~ (o <= x < o + 32) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R STK0 sp0 (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros R ly S Hp W mem md o buf cap Lam peak cnt fail ran most own a k0 x ly2 S2 Hp2 W2 mem2 md2 STK0 sp0 k
  HAR HLED Hin Hab Hx Hcap0 Hbuf Hoff HJ.
pose proof asan_consts as (C1 & _). pose proof cf_head_nonneg as Hh0.
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
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
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KEEPBLK & _ & _ & GONEFP & _).
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
Lemma wv_blk_keep : forall ly S Hp W mem md o buf cap Lam peak cnt fail ran most own a k0 x
    ly2 S2 Hp2 W2 mem2 md2 STK0 sp0 k,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k0) Lam -> a <> buf -> a <= x < a + k0 ->
  0 <= cap -> (cap <> 0 -> In (buf, cap) Lam) ->
  ~ (o <= x < o + 32) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK0 sp0 (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof. exact (wv_blk_keepR (@wle SEGS)). Qed.

(* ---- THE TREE'S FOOTPRINT ACROSS A CALL: every byte of pj_footR v D is kept, whichever of the three locations the
   node has. The node's own 56 bytes: on the real stack they are in the caller window (kept outside FP) or above it
   (the journal's high clause); in a block or a frame, by the block / frame clause. Its blocks: wv_blk_keepR. Over a
   world relation R (the journal at R; no law of R is used); wv_foot_keep below is its instance at wle ---- *)
Lemma wv_foot_keepR : forall (R : world SEGS -> world SEGS -> Prop) ly S Hp W regs mem md STKv STK0 d o buf cap Lam
    peak cnt fail ran most own v D
    ly2 S2 Hp2 W2 mem2 md2 k,
  192 <= STKv -> 0 <= d ->
  ARx ly S Hp W mem md -> astk_ok STKv ly (spZ regs) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  0 <= cap -> (cap <> 0 -> In (buf, cap) Lam) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R STK0 (spZ regs + d) (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  forall x, pj_footR v D x ->
    (0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros R ly S Hp W regs mem md STKv STK0 d o buf cap Lam peak cnt fail ran most own v D ly2 S2 Hp2 W2 mem2 md2 k
  HSTK Hd HAR Hstk HLED HLOC HD Hoff Hcap0 Hbuf HJ HWIN x Hx.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & KEEPHI & _ & _ & KEEPFR & _).
destruct Hx as [Hhdr | (b & HbD & Hb)].
- destruct HLOC as [(Hv1 & Hv2) | [(y0 & z0 & Hin & Hyb & Hyv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
  + assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
    assert (Himg : ~ in_img SEGS x)
      by (intros Hi; pose proof (pa_segs_low x Hi); unfold kLowMemEnd in *; lia).
    assert (HnFP : ~ inFP (prhWriter_cfp o buf cap) x).
    { intros Hf. unfold prhWriter_cfp in Hf. apply inFP_cons in Hf.
      destruct Hf as [Hf | Hf]; [exact (Hoff x Hf (or_introl Hhdr))|].
      unfold prhWriter_fp in Hf. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [exact (inFP_nil x Hf)|].
      pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
      pose proof (HF (buf, cap) (Hbuf Hc0)) as (_ & Hblb & _). cbn [fst snd] in Hblb.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (buf - cf_head) (cap + cf_head) HAR Hblb)
        as (_ & _ & Hpc & _ & _ & _).
      destruct Hf as (r & Hr & Hrr). unfold ablocks_fp in Hr. cbn [map In] in Hr.
      destruct Hr as [Hr | []]. subst r. cbn [fst snd] in Hrr. lia. }
    split; [split; [exact Hx64 | exact Himg]|].
    destruct (Z_lt_le_dec x (spZ regs + d)) as [Hlt|Hge].
    * exact (HWIN x ltac:(lia) HnFP).
    * exact (KEEPHI x ltac:(lia) ltac:(lia)).
  + exact (wv_blk_keepR R ly S Hp W mem md o buf cap Lam peak cnt fail ran most own y0 z0 x ly2 S2 Hp2 W2 mem2 md2
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
      pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
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
  exact (wv_blk_keepR R ly S Hp W mem md o buf cap Lam peak cnt fail ran most own a k0 x ly2 S2 Hp2 W2 mem2 md2
    STK0 (spZ regs + d) k HAR HLED Hin Hab Hb Hcap0 Hbuf
    ltac:(intros Ho; exact (Hoff x Ho (or_intror (ex_intro _ (a, k0) (conj HbD Hb))))) HJ).
Qed.
Lemma wv_foot_keep : forall ly S Hp W regs mem md STKv STK0 d o buf cap Lam peak cnt fail ran most own v D
    ly2 S2 Hp2 W2 mem2 md2 k,
  192 <= STKv -> 0 <= d ->
  ARx ly S Hp W mem md -> astk_ok STKv ly (spZ regs) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  0 <= cap -> (cap <> 0 -> In (buf, cap) Lam) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK0 (spZ regs + d) (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  forall x, pj_footR v D x ->
    (0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof. exact (wv_foot_keepR (@wle SEGS)). Qed.

(* ---- a .rodata literal is a legal put source: its home is kept (kept_at's read-only arm, which does not read the
   ledger) and it is apart from the buffer, because the buffer is a client block and the literal is image ---- *)
Lemma wv_lit_home : forall ly S Hp W mem md Lam peak cnt fail ran most own buf cap s n,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (cap <> 0 -> In (buf, cap) Lam) -> 0 <= cap -> 0 < n ->
  kept_at B [] s n ->
  (forall a, s <= a < s + n -> in_img SEGS a) ->
  prhWriter_src_home B ly S Lam buf cap s n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own buf cap s n HAR HLED Hbuf Hcap0 Hn Hkept Himg.
pose proof cf_head_nonneg as Hh0.
split.
- left. destruct Hkept as [(b & m & Hin & _) | [H2 | H3]];
    [destruct Hin | right; left; exact H2 | right; right; exact H3].
- destruct (Z.eq_dec cap 0) as [->|Hc0]; [left; reflexivity|].
  destruct (Z_le_gt_dec (s + n) buf) as [Hle|Hgt]; [right; left; exact Hle|].
  destruct (Z_le_gt_dec (buf + cap) s) as [Hle2|Hgt2]; [right; right; exact Hle2|].
  exfalso.
  pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
  pose proof (HF (buf, cap) (Hbuf Hc0)) as (_ & Hblb & _). cbn [fst snd] in Hblb.
  assert (Hrq : cap + cf_head <= req_size (cap + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); lia).
  set (x := Z.max s buf).
  assert (Hx1 : s <= x < s + n) by (subst x; lia).
  assert (Hx2 : buf - cf_head <= x < buf - cf_head + req_size (cap + cf_head)) by (subst x; lia).
  refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR _) (Himg x Hx1)).
  left. exists (buf - cf_head), (cap + cf_head). split; [exact Hblb | exact Hx2].
Qed.

(* ---- WHAT write_value's OWN STEPS KEEP. Its straight-line code writes only its own frame [sp - 192, sp) (the one
   region of the seated state with a write window): the struct (at or above the entry sp), the buffer and every
   harness block, the ledger's statics, the image and the tree all lie outside it. Each keep below is stated over a
   write set P with the two side conditions the walk discharges once (P misses everything below alloc_ceiling, and
   P misses the struct), so the item loop reuses them after every call. ---- *)
Definition wv_wr (sp a : Z) : Prop := sp - 192 <= a < sp.

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

(* THE LEDGER: its five statics are image bytes (generated addresses, all below kLowMemEnd) and each harness block's
   hidden head is in a block, so a write set that misses everything below alloc_ceiling keeps the ledger *)
Lemma wv_led_keep : forall ly S Hp W md mem mem' Lam peak cnt fail ran most own (P : Z -> Prop),
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ P a) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W md mem mem' Lam peak cnt fail ran most own P HAR LG HK HP.
pose proof LG as HND. apply prh_ledger_nodup in HND. pose proof LG as HHB. apply prh_ledger_blocks in HHB.
pose proof LG as HPm. apply prh_ledger_heads in HPm.
pose proof LG as G1. apply prh_ledger_live in G1. pose proof LG as G2. apply prh_ledger_peak in G2.
pose proof LG as G3. apply prh_ledger_count in G3. pose proof LG as G4. apply prh_ledger_fail in G4.
pose proof LG as G5. apply prh_ledger_ran in G5. pose proof LG as Gr. apply prh_ledger_bounds in Gr.
pose proof LG as G6. apply prh_ledger_most in G6. pose proof LG as G7. apply prh_ledger_own in G7.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Hh0.
(* the generated static addresses and widths, read off the image class (the #102 kit's seven statics) *)
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
destruct G6 as (G6 & G6r). destruct G7 as (G7 & G7r).
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
Lemma wv_out_keep : forall ly1 S1 Hp1 (W1 W2 : world SEGS) mem1 mem2 md1 Lam peak1 cnt1 fail1 ran1 most own o buf st
  (P : Z -> Prop),
  ARx ly1 S1 Hp1 W1 mem1 md1 ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam peak1 cnt1 fail1 ran1 most own ->
  prhWriter_out W1 mem1 Lam o buf st ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  (forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ P a) ->
  prhWriter_out W2 mem2 Lam o buf st.
Proof.
intros ly1 S1 Hp1 W1 W2 mem1 mem2 md1 Lam peak1 cnt1 fail1 ran1 most own o buf st P HAR HLEDx HO HK HP HOP.
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
   the callee runs at write_value's OWN entry sp with its entry ra, and its post IS write_value's: aj_call_xW at
   o = - d, e1 = d (the callee's window reaches the caller's window top, which holds the struct). ---- *)
(* ---- the only writable window of the seated state is the own frame [sp - 192, sp): a journal whose stack window
   covers it admits every write the straight-line code makes ---- *)
Lemma wv_awr : forall E tg STK sp0 FP bl0 blc ly own spe,
  bv_unsigned (ew E 2) = spe -> sp0 - STK <= spe - 192 -> spe <= sp0 ->
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

(* ---- THE ONE USE of the location premise (PRH_FnWriter.v twrite_value_specX): the node v is on the real stack
   between sp and ly_stk_hi, in a live harness block of the ledger, or in a live fake frame; in each case it is off
   the image, off the shadow band, 4096 or above, below 2 ^ 47, and apart from write_value's own 192-byte frame ---- *)
Lemma wv_loc : forall ly S Hp W regs mem md ch STKv Lam peak cnt fail ran most own buf v,
  192 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= spZ regs - 192 \/ spZ regs <= v) /\
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) /\ (forall a, v <= a < v + 56 -> ~ in_img SEGS a).
Proof.
intros ly S Hp W regs mem md ch STKv Lam peak cnt fail ran most own buf v HSTK HPRE HLED HLOC.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
destruct HLOC as [(Hv1 & Hv2) | [(x & y & Hin & Hxb & Hxv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
- split; [lia|]. split; [lia|]. split; [right; exact Hv1|]. split; [right; unfold SHADOW_OFF; lia|].
  intros a Ha Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
- pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
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
   above the entry sp (the stack arm) or below alloc_ceiling (a harness block, a fake frame), so the straight-line
   code cannot touch it ---- *)
Lemma wv_foot_wr : forall ly S Hp W regs mem md ch STKv Lam peak cnt fail ran most own buf v D,
  192 <= STKv ->
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ wv_wr (spZ regs) x.
Proof.
intros ly S Hp W regs mem md ch STKv Lam peak cnt fail ran most own buf v D HSTK HPRE HLED HLOC HD x Hx.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Hh0.
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak cnt fail ran most own buf v HSTK HPRE HLED HLOC)
  as (Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
destruct Hx as [Hhdr | ([a k0] & HbD & Hb)].
- split; [lia|]. split; [exact (Hv5 x Hhdr)|]. unfold wv_wr. lia.
- unfold pj_holdsR in Hb. cbn [fst snd] in Hb.
  destruct (HD a k0 HbD) as (Hin & _).
  pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
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

(* THE ONE-RECORD CHAIN (the text's ruled case-1 form): from the two words below a frame pointer v at or above the
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

(* The case-1 words (form (a)) survive any change that keeps [o - 16, o) *)
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

(* the read-only view through a journal (its image clause; HPSTRO), over a world relation R (no law of R is used);
   wv_arodata_j below is its instance at wle *)
Lemma wv_arodata_jR : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2
    mem2 md2 k,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k HJ Hcl HRO a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
rewrite (F3 a Himg Ho He (HPSTRO a Hro) (fp_spares_closed FP a Hcl)). exact (HRO a Hro Ho He).
Qed.
Lemma wv_arodata_j : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k,
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof. exact (wv_arodata_jR (@wle SEGS)). Qed.

(* ---- the writer's run: the room and the text bound for the next piece (the batch cut: the live room at each event of the
   callee's own run, from the caller's, Model.prhW_live_mid) ---- *)
Lemma wv_wmax_next : forall ok st P1 P2 P3,
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (P1 ++ P2 ++ P3))) + 1 <= prhWriter_WMAX ->
  Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok st P1))) + Z.of_nat (length (concat P2)) + 1
    <= prhWriter_WMAX.
Proof.
intros ok st P1 P2 P3 H. pose proof (prhWriter_putN_len_le ok st P1) as L.
rewrite !concat_app, !length_app in H. lia.
Qed.

Lemma wv_live_next : forall S Sc ly lyc Lam peak buf st ok P1 P2 P3 Lamc peakc bufc,
  0 <= WriterApp.w_cap st ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lamc peakc bufc (prhWriter_putN ok st P1) ->
  prh_live_evs S (prhWriter_evs [] st (P1 ++ P2 ++ P3)) ->
  prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok st P1) P2).
Proof.
intros S Sc ly lyc Lam peak buf st ok P1 P2 P3 Lamc peakc bufc Hc0 HBLK HL.
exact (prhW_live_mid B S Sc ly lyc Lam peak buf st ok P1 P2 P3 Lamc peakc bufc Hc0 HBLK HL).
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
  fp_sub_x B STKc sp0 (prhWriter_cfp o buf (WriterApp.w_cap st)) (prhWriter_cfp o buf1 (WriterApp.w_cap st1))
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

(* v's 56 bytes stay addressable: the three locations. Over a world relation R (the journal at R; no law of R is
   used); wv_ra_cur below is its instance at wle *)
Lemma wv_ra_curR : forall (R : world SEGS -> world SEGS -> Prop) ly S Hp W mem md Lam buf v regs STKv d o cap
    lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1 most own,
  ARx ly S Hp W mem md -> astk_ok STKv ly (spZ regs) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R (STKv + d) (spZ regs + d) (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 fail1 ran1 most own ->
  (forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1) ->
  YM05.alloc_ceiling <= o ->
  (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56.
Proof.
intros R ly S Hp W mem md Lam buf v regs STKv d o cap lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1 most own
  HAR Hstk HRA HLOC HJ HLED1 HLK Ho Hbufb.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof cf_head_nonneg as Hh0.
pose proof HJ as (HARc & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
destruct HLOC as [(Hv1 & Hv2) | [(x & y & Hin & Hxb & Hxv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
- (* the real stack: its shadow is zero in every ARx state *)
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  intros z Hz. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. apply (alx_zshadow_byte SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc z HARc). lia.
- (* a harness block of the ledger, still one at the current state *)
  pose proof (HLK x y Hin Hxb) as Hin1.
  pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED1) as HF1.
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
Lemma wv_ra_cur : forall ly S Hp W mem md Lam buf v regs STKv d o cap
    lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1 most own,
  ARx ly S Hp W mem md -> astk_ok STKv ly (spZ regs) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d) (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 fail1 ran1 most own ->
  (forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1) ->
  YM05.alloc_ceiling <= o ->
  (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56.
Proof. exact (wv_ra_curR (@wle SEGS)). Qed.

(* the tree's blocks stay C-visible: their shadow by the harness-block law at the current state, their bytes by the
   journal (a live block outside FP), their tail granule by field 15. Over a world relation R (the journal at R; no
   law of R is used); wv_tvis_cur below is its instance at wle *)
Lemma wv_tvis_curR : forall (R : world SEGS -> world SEGS -> Prop) ly S Hp W mem md Lam buf D STK sp0 o cap lyc Sc Hpc
    Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1 most own,
  ARx ly S Hp W mem md -> prhWriter_tree_vis W mem D ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R STK sp0 (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 fail1 ran1 most own ->
  (forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1) ->
  YM05.alloc_ceiling <= o ->
  (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  prhWriter_tree_vis Wc memc D.
Proof.
intros R ly S Hp W mem md Lam buf D STK sp0 o cap lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1 most own
  HAR HT HD HLB HJ HLED1 HLK Ho Hbufb a k HinD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof cf_head_nonneg as Hh0.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (HD a k HinD) as (HinL & Hab).
destruct (HT a k HinD) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (HLK a k HinL Hab) as Hin1.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED1) as HF1.
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
Lemma wv_tvis_cur : forall ly S Hp W mem md Lam buf D STK sp0 o cap lyc Sc Hpc Wc memc mdc kc Lam1 peak1 cnt1 fail1 ran1 most own,
  ARx ly S Hp W mem md -> prhWriter_tree_vis W mem D ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 (prhWriter_cfp o buf cap)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 fail1 ran1 most own ->
  (forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1) ->
  YM05.alloc_ceiling <= o ->
  (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  prhWriter_tree_vis Wc memc D.
Proof. exact (wv_tvis_curR (@wle SEGS)). Qed.

(* ---- THE MODEL-RUN POSITION (kit-oldpin b501d43ce5af: PRH_FnWriter 5f7cd294e4b6, PRH_Base 819d870ee0f7). Every
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

Lemma wv_ret_pos_one : forall rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Hp (W : world SEGS) mem Lam peak ran most own o buf st bs
    ly2 S2 Hp2 W2 regs2 mem2 md2,
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_i rp_hist st bs o W2 mem2 S2 ->
  (exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2 /\
     prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs])) ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
intros rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Hp W mem Lam peak ran most own o buf st bs ly2 S2 Hp2 W2 regs2 mem2 md2
  HOUT HLED HPP HRET.
pose proof HLED as Hbd. apply prh_ledger_bounds in Hbd. destruct Hbd as (Hpk & _ & Hc & _).
assert (HcntW : 0 <= WriterApp.w_cnt st) by lia.
assert (HOK0 : prhW_oksg [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st []) ran ran).
{ rewrite prhW_k_nil. split; [intros i Hi; exfalso; lia|]. split; [intros i Hi; exfalso; lia | reflexivity]. }
assert (HBLK0 : prhWriter_blk B ly S Lam peak buf st ly S Lam peak buf (prhWriter_putN [] st [])).
{ unfold prhWriter_blk. left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. apply Permutation_refl. }
exact (prhWriter_ret_pos_step B rp_sm rp_x rp_os rp_H0 rp_i rp_i rp_hist ly S Lam peak ran most own o buf st [] bs
  [] ran buf Lam peak ly S Hp W mem ly2 S2 Hp2 W2 regs2 mem2 md2 HcntW ltac:(lia) (eq_sym (Nat.add_0_r rp_i))
  HOK0 HOUT HLED HBLK0 HPP HRET).
Qed.

Lemma wv_ret_pos_app : forall rp_sm rp_x rp_os rp_H0 rp_i rp_c ly S Lam peak ran most own o buf st PP P2
    ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 (W1 : world SEGS) mem1 ly2 S2 Hp2 W2 regs2 mem2 md2,
  0 <= WriterApp.w_cnt st -> 0 <= peak ->
  rp_c = (rp_i + length (prhWriter_evs ok1 st PP))%nat ->
  prhW_oksg ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st PP) ran ran1 ->
  prhWriter_out W1 mem1 Lam1 o buf1 (prhWriter_putN ok1 st PP) ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st PP))
    (WriterApp.w_fail (prhWriter_putN ok1 st PP)) ran1 most own ->
  prhWriter_blk B ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 (prhWriter_putN ok1 st PP) ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_c ly1 S1 Lam1 peak1 ran1 most own o buf1 (prhWriter_putN ok1 st PP) P2
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st (PP ++ P2) ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
intros rp_sm rp_x rp_os rp_H0 rp_i rp_c ly S Lam peak ran most own o buf st PP P2 ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1
  ly2 S2 Hp2 W2 regs2 mem2 md2 Hc0 Hpk Hrc Hok1 Hout1 Hled1 Hblk1 (ok2 & Hret2 & G2 & hist2 & Hpos2).
pose proof Hled1 as Hb1. apply prh_ledger_bounds in Hb1. destruct Hb1 as (Hpk1 & _ & Hr1 & Hf1 & _).
assert (Hpk1' : 0 <= peak1) by lia.
destruct (prhWriter_ret_ok_g B ok2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpk1' G2 Hret2)
  as (ran2 & buf2 & Lam2 & peak2 & Hok2 & Hout2 & Hled2 & Hblk2).
pose proof Hled1 as Hnd1. apply prh_ledger_nodup in Hnd1.
destruct (prhW_app_model st PP P2 ok1 ok2 ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2) as (ok & Hput & Hoks).
pose proof (prhW_cap_after PP ok1 st) as Hcap.
exists ok. split; [|split].
{ apply (prhWriter_ret_ok_of_g B ok ly S Lam peak ran most own o buf st (PP ++ P2) ly2 S2 Hp2 W2 regs2 mem2 md2
    ran2 buf2 Lam2 peak2 Hpk Hoks); rewrite Hput; [exact Hout2 | exact Hled2 |].
  eapply prhW_blk_trans; [exact Hnd1 | exact Hcap | exact Hblk1 | exact Hblk2]. }
{ exact (proj1 (proj2 Hoks)). }
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

End h.
End f.
End d.
