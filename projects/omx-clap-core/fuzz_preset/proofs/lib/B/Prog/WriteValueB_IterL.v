(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d), segment
   WvbIter: THE ITEM LOOP's SUPPORT of write_value's container walk (an array or an object), between the loop head
   (write_value + 4 * 90, WriteValueB_Defs.wv_headR) and the close (write_value + 4 * 173, wv_clR), at wle' SEGS RZ_cf: the seated states of
   the loop body (the head's registers and frame words, the node, an object's key slot), the join predicate wvi_st
   (Defs' wv_commonR at wle' SEGS RZ_cf, at the current float state, + the head's register and frame facts), the
   pieces algebra, and the four inner call sites (put, indent, put_string, the recursive write_value) as continuation
   lemmas, each concluding SRr' SEGS RZ_cf (a callee may realloc, so the loop's worlds are related by wle').
   PORTED (not cited) from a Theorem Labs lane's image-A loop scratch (lib/A/Prog/PRW_write_value_lp.v :3250-5375, the wvl
   lemmas):
   B's frame (192), B's head registers and frame words (Defs' wv_head, measured), B's #102 ledger cells most / own,
   the call lemmas of WriteValueB_Call (fp_sub_x, FRM0-ENTRY), the granule bound of an object's key from AR_laws_x's
   field alx_blocks_ceil8 (wv_cstr_blk, copied from WriteValueB_Leaf), and THE FLOAT STATE: every join is stated
   at its float state fxc (wv_common's frm_zero / fregs_kept_x conjuncts); put and indent keep it, put_string and
   write_value end at their exit float state, so their site lemmas hand the continuation the callee's fx2.
   Numerals: 192 (LENGTH: write_value's frame), 8 .. 184 (LENGTH: frame offsets), 24 / 32 / 40 / 56 (LENGTH: the
   node's fields and size, PRH_Reader pj_hdrR), 8 (LENGTH: a key slot), 2 ^ 42 .. 2 ^ 48 (LENGTH: atom ranges), the
   slots (DERIVED). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base
  WriteValueB_Call WriteValueB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the pure pieces of the loop: the item i, what follows item j, a child's depth ---- *)
Lemma wvi_firstn_S : forall {A} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia.
- reflexivity.
- change (firstn (S (S i)) (x :: l)) with (x :: firstn (S i) l).
  change (firstn (S i) (x :: l)) with (x :: firstn i l). change (nth (S i) (x :: l) d) with (nth i l d).
  rewrite (IH i d) by lia. reflexivity.
Qed.

Lemma wvi_depth_arr : forall l i, (i < length l)%nat ->
  (PjTree.depth (nth i l PjTree.JNull) < PjTree.depth (PjTree.JArr l))%nat.
Proof.
intros l i Hi. cbn [PjTree.depth].
assert (H : Forall (fun k => (k <= list_max (map PjTree.depth l))%nat) (map PjTree.depth l))
  by (apply list_max_le; lia).
rewrite Forall_forall in H.
assert (Hin : In (PjTree.depth (nth i l PjTree.JNull)) (map PjTree.depth l)) by (apply in_map, nth_In; exact Hi).
pose proof (H _ Hin). lia.
Qed.

Lemma wvi_depth_obj : forall l i, (i < length l)%nat ->
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

(* lia with the powers this walk meets as numerals (with the euclidean-division flag off it treats 2 ^ k as an atom) *)
Ltac wvi_zl :=
  pose proof (eq_refl : 2 ^ 64 = 18446744073709551616); pose proof (eq_refl : 2 ^ 63 = 9223372036854775808);
  pose proof (eq_refl : 2 ^ 60 = 1152921504606846976); pose proof (eq_refl : 2 ^ 48 = 281474976710656);
  pose proof (eq_refl : 2 ^ 47 = 140737488355328); pose proof (eq_refl : 2 ^ 46 = 70368744177664);
  pose proof (eq_refl : 2 ^ 45 = 35184372088832); pose proof (eq_refl : 2 ^ 44 = 17592186044416);
  pose proof (eq_refl : 2 ^ 42 = 4398046511104);
  pose proof (eq_refl : 2 ^ 32 = 4294967296); pose proof (eq_refl : 2 ^ 31 = 2147483648); lia.
Ltac wvi_zs := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; wvi_zl.

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

(* ---- THE LOOP'S SEATED STATES (measured with the engine on B's listing, WvbIter's probe, log
   the internal file zfb-20261029T194028Z.log): the head's registers
   (Defs' wv_head: s2 = v + 40, s4 = shadow (v + 24), s8 = v + 24, s10 = 0, s11 = shadow (v + 40); s0, s1, s3, s5, s6,
   s7, s9 their own atoms 8, 9, 19, 21, 22, 23, 25), the own frame READ ONLY (the body from the head, slot 90, to the
   closing indent's `jal`, slot 172, stores nothing), the node (tag, kids, keys, n as atoms 36, 37, 38) and, where the
   object case reads it (kr), the key slot keys + 8 i (atom 39, its word the atom 40) ---- *)
Definition wvi_sh (k : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0).
Definition wvi_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 9 40)) 20%bv (wvi_sh 9 24)) 24%bv (SOff 9 24))
    27%bv (wvi_sh 9 40)) 26%bv (SLit 0).
Definition wvi_chunks : list YP09.chunk :=
  [ YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
    YP09.mkChunk 32 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)));
    YP09.mkChunk 40 (CVal 8 (wvi_sh 9 32)); YP09.mkChunk 48 (CVal 8 (SOff 9 32));
    YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0));
    YP09.mkChunk 72 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (wvi_sh 9 0));
    YP09.mkChunk 88 (CVal 8 (SOff 53 0)); YP09.mkChunk 96 (CVal 8 (SOff 52 0));
    YP09.mkChunk 104 (CVal 8 (SOff 51 0)); YP09.mkChunk 112 (CVal 8 (SOff 50 0));
    YP09.mkChunk 120 (CVal 8 (SOff 49 0)); YP09.mkChunk 128 (CVal 8 (SOff 48 0));
    YP09.mkChunk 136 (CVal 8 (SOff 47 0)); YP09.mkChunk 144 (CVal 8 (SOff 46 0));
    YP09.mkChunk 152 (CVal 8 (SOff 45 0)); YP09.mkChunk 160 (CVal 8 (SOff 44 0));
    YP09.mkChunk 168 (CVal 8 (SOff 43 0)); YP09.mkChunk 176 (CVal 8 (SOff 42 0));
    YP09.mkChunk 184 (CVal 8 (SOff 54 0)) ].
Definition wvi_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 192 0 0 wvi_chunks.
Definition wvi_node (tg : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0
    [ YP09.mkChunk 0 (CVal 4 (SLit tg)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
      YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 38 0)) ].
Definition wvi_keyr : YP09.region := YP09.mkRegion (Some 39%nat) 0 8 0 0 [ YP09.mkChunk 0 (CVal 8 (SOff 40 0)) ].
Definition wvi_mem (tg : Z) (kr : bool) : smem := wvi_frame :: wvi_node tg :: (if kr then [wvi_keyr] else []).
(* the atoms' ranges (closed numerals), i < n, n <> 0, and the two aliases kids + 56 i (atom 41), keys + 8 i (atom 39);
   keys is a block only for an object (an array's keys field is 0) *)
Definition wvi_facts (tg : Z) (kr : bool) : facts :=
  mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
             (9%nat, mkAF 4096 (2 ^ 47 - 56) 3); (21%nat, mkAF 0 (2 ^ 42) 0); (25%nat, mkAF 0 (2 ^ 45) 3);
             (23%nat, mkAF 0 (2 ^ 48) 3); (36%nat, mkAF 4096 (2 ^ 47) 3); (41%nat, mkAF 4096 (2 ^ 47 - 56) 3) ] ++
           (if Z.eqb tg 6 then [(37%nat, mkAF 4096 (2 ^ 47) 3)] else []) ++
           (if kr then [(39%nat, mkAF 4096 (2 ^ 47 - 8) 3)] else []))
    [ mkAC BC_NE (SOff 38 0) (SLit 0); mkAC BC_LTU (SOff 21 0) (SOff 38 0) ]
    ([ (SAlu ALU_ADD (SOff 36 0) (SOff 23 0), SOff 41 0) ] ++
     (if kr then [(SAlu ALU_ADD (SOff 37 0) (SOff 25 0), SOff 39 0)] else [])).
Definition wvi_SH (kr : bool) : list shent := mkSHE 9 0 56 :: (if kr then [mkSHE 39 0 8] else []).
Definition wvi_ss (pc tg : Z) (kr : bool) : sstate := mkSS pc wvi_regs (wvi_mem tg kr) None (wvi_facts tg kr).
Definition WVI_PC (k : Z) : Z := AF_write_value + 4 * k.
(* the seated environment: the registers, then atoms 32 .. 54: the shadow base, dep, the separator and comma
   literals, kids, keys, n, keys + 8 i, the key string, kids + 56 i, and the entry's s0, s1, s2 .. s11, ra (the saved
   words at R + 176, 168, 160 .. 88, 184) *)
Definition wvi_extra (dep sep comma kids keys nn ka kp ca : Z) (sv13 : list Z) : list word :=
  map (Z_to_bv 64) ([SHADOW_OFF; dep; sep; comma; kids; keys; nn; ka; kp; ca] ++ sv13).
Definition wvi_EH (regs : bvmap 5 word) (dep sep comma kids keys nn ka kp ca : Z) (sv13 : list Z) : env :=
  Eimg (Ereg regs (wvi_extra dep sep comma kids keys nn ka kp ca sv13)).
Definition wvi_sv13 (X : wvx) : list Z :=
  [bv_unsigned (getr (y_regs X) 8); bv_unsigned (getr (y_regs X) 9); bv_unsigned (getr (y_regs X) 18);
   bv_unsigned (getr (y_regs X) 19); bv_unsigned (getr (y_regs X) 20); bv_unsigned (getr (y_regs X) 21);
   bv_unsigned (getr (y_regs X) 22); bv_unsigned (getr (y_regs X) 23); bv_unsigned (getr (y_regs X) 24);
   bv_unsigned (getr (y_regs X) 25); bv_unsigned (getr (y_regs X) 26); bv_unsigned (getr (y_regs X) 27);
   bv_unsigned (getr (y_regs X) 1)].
Definition wvi_E (X : wvx) (i : nat) (regsc : bvmap 5 word) (kids keys nn kp : Z) : env :=
  wvi_EH regsc (y_dep X) (WV_STR (wv_sep_slot X)) (WV_STR 88) kids keys nn (keys + 8 * Z.of_nat i) kp
    (kids + 56 * Z.of_nat i) (wvi_sv13 X).

(* ---- the pieces of item i and the joins of the body: after the comma (PA), the indent (PB), an object's key (Pk),
   its separator (Ps), before the value (PD) ---- *)
Definition wvi_child (X : wvx) (i : nat) : PjTree.jv :=
  match y_t X with
  | PjTree.JArr l => nth i l PjTree.JNull
  | PjTree.JObj l => snd (nth i l ([], PjTree.JNull))
  | _ => PjTree.JNull
  end.
Definition wvi_key (X : wvx) (i : nat) : list Z :=
  match y_t X with PjTree.JObj l => fst (nth i l ([], PjTree.JNull)) | _ => [] end.
Definition wvi_PA (X : wvx) (i : nat) : list (list Z) := wv_done X i ++ WriterValue.wcomma i.
Definition wvi_PB (X : wvx) (i : nat) : list (list Z) := wvi_PA X i ++ WriterValue.wind (y_p X) (y_dep X + 1).
Definition wvi_Pk (X : wvx) (i : nat) : list (list Z) := wvi_PB X i ++ WriterSpec.spieces (wvi_key X i).
Definition wvi_Ps (X : wvx) (i : nat) : list (list Z) := wvi_Pk X i ++ [WriterValue.wsep (y_p X)].
Definition wvi_PD (X : wvx) (i : nat) : list (list Z) :=
  match y_t X with PjTree.JObj _ => wvi_Ps X i | _ => wvi_PB X i end.
(* what follows the pieces P of the container's whole run: item j onward, the closing indent and bracket *)
Definition wvi_rest (X : wvx) (j : nat) : list (list Z) :=
  match y_t X with
  | PjTree.JArr l => wv_arr_go (y_p X) (y_dep X) j (skipn j l) ++ WriterValue.wind (y_p X) (y_dep X) ++ [[93]]
  | PjTree.JObj l => wv_obj_go (y_p X) (y_dep X) j (skipn j l) ++ WriterValue.wind (y_p X) (y_dep X) ++ [[125]]
  | _ => []
  end.

Lemma wvi_done_D : forall X i, (i < wv_nitems (y_t X))%nat ->
  wv_done X (S i) = wvi_PD X i ++ WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1).
Proof.
intros X i Hi. unfold wvi_PD, wvi_Ps, wvi_Pk, wvi_PB, wvi_PA, wvi_child, wvi_key, wv_done.
destruct (y_t X) as [| | | txt bits | s | l | l]; cbn [wv_nitems] in Hi; try lia.
- rewrite (wvi_firstn_S l i PjTree.JNull Hi), wv_arr_go_app, firstn_length_le by lia.
  cbn [wv_arr_go app Nat.add]. rewrite app_nil_r, <- !app_assoc. reflexivity.
- rewrite (wvi_firstn_S l i ([], PjTree.JNull) Hi), wv_obj_go_app, firstn_length_le by lia.
  destruct (nth i l ([], PjTree.JNull)) as [k x]. cbn [wv_obj_go app Nat.add fst snd]. rewrite app_nil_r.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvi_split : forall X j, (0 < wv_nitems (y_t X))%nat -> (j <= wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = wv_done X j ++ wvi_rest X j.
Proof.
intros X j Hn Hj. unfold wv_done, wvi_rest.
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

(* the pieces around item i, cut at each join of the body *)
Lemma wvi_pcs_D : forall X i, (i < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvi_PD X i ++ WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1) ++ wvi_rest X (S i).
Proof.
intros X i Hi. rewrite (wvi_split X (S i)) by lia. rewrite (wvi_done_D X i Hi), <- app_assoc. reflexivity.
Qed.

Lemma wvi_pcs_A : forall X i, (i < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvi_PA X i ++ WriterValue.wind (y_p X) (y_dep X + 1) ++
    ((match y_t X with PjTree.JObj _ => WriterSpec.spieces (wvi_key X i) ++ [WriterValue.wsep (y_p X)] | _ => [] end)
     ++ WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1) ++ wvi_rest X (S i)).
Proof.
intros X i Hi. rewrite (wvi_pcs_D X i Hi). unfold wvi_PD, wvi_Ps, wvi_Pk, wvi_PB.
destruct (y_t X); rewrite <- !app_assoc; reflexivity.
Qed.

Lemma wvi_pcs_comma : forall X i, (i < wv_nitems (y_t X))%nat -> i <> 0%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wv_done X i ++ [[44]] ++
    (WriterValue.wind (y_p X) (y_dep X + 1) ++
     ((match y_t X with PjTree.JObj _ => WriterSpec.spieces (wvi_key X i) ++ [WriterValue.wsep (y_p X)] | _ => [] end)
      ++ WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1) ++ wvi_rest X (S i))).
Proof.
intros X i Hi Hi0. rewrite (wvi_pcs_A X i Hi). unfold wvi_PA, WriterValue.wcomma.
destruct (Nat.eqb_spec i 0) as [E|_]; [lia|]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvi_PA_comma : forall X i, i <> 0%nat -> wv_done X i ++ [[44]] = wvi_PA X i.
Proof.
intros X i Hi0. unfold wvi_PA, WriterValue.wcomma. destruct (Nat.eqb_spec i 0) as [E|_]; [lia | reflexivity].
Qed.

Lemma wvi_PA_0 : forall X, wvi_PA X 0 = wv_done X 0.
Proof. intros X. unfold wvi_PA. cbn [WriterValue.wcomma Nat.eqb]. apply app_nil_r. Qed.

Lemma wvi_pcs_B : forall X i, (i < wv_nitems (y_t X))%nat -> wv_tagc (y_t X) = 6 ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvi_PB X i ++ WriterSpec.spieces (wvi_key X i) ++
    ([WriterValue.wsep (y_p X)] ++ WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1) ++ wvi_rest X (S i)).
Proof.
intros X i Hi Ht. rewrite (wvi_pcs_D X i Hi). unfold wvi_PD, wvi_Ps, wvi_Pk, wv_tagc in *.
destruct (y_t X); try discriminate Ht. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvi_pcs_k : forall X i, (i < wv_nitems (y_t X))%nat -> wv_tagc (y_t X) = 6 ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wvi_Pk X i ++ [WriterValue.wsep (y_p X)] ++
    (WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1) ++ wvi_rest X (S i)).
Proof.
intros X i Hi Ht. rewrite (wvi_pcs_D X i Hi). unfold wvi_PD, wvi_Ps, wv_tagc in *.
destruct (y_t X); try discriminate Ht. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvi_PD_arr : forall X i, wv_tagc (y_t X) = 5 -> wvi_PD X i = wvi_PB X i.
Proof. intros X i Ht. unfold wvi_PD. unfold wv_tagc in Ht. destruct (y_t X); try reflexivity. discriminate Ht. Qed.

Lemma wvi_PD_obj : forall X i, wv_tagc (y_t X) = 6 -> wvi_PD X i = wvi_Pk X i ++ [WriterValue.wsep (y_p X)].
Proof. intros X i Ht. unfold wvi_PD, wvi_Ps, wv_tagc in *. destruct (y_t X); try discriminate Ht. reflexivity. Qed.

(* after the last item: the indent at dep (the close's pieces, wv_clP) and the closing bracket *)
Lemma wvi_pcs_end : forall X, (0 < wv_nitems (y_t X))%nat ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) =
  wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X) ++
    [[if wv_tagc (y_t X) =? 6 then 125 else 93]].
Proof.
intros X Hn. rewrite (wvi_split X (wv_nitems (y_t X)) Hn ltac:(lia)). f_equal.
unfold wvi_rest, wv_tagc. unfold wv_nitems in *.
destruct (y_t X) as [| | | txt bits | s | l | l]; cbn [Z.eqb Pos.eqb] in Hn |- *; try lia; rewrite skipn_all;
  reflexivity.
Qed.

Lemma wvi_clP_eq : forall X, (0 < wv_nitems (y_t X))%nat ->
  wv_clP X = wv_done X (wv_nitems (y_t X)) ++ WriterValue.wind (y_p X) (y_dep X).
Proof.
intros X Hn. unfold wv_clP. destruct (wv_nitems (y_t X)) as [|m] eqn:E; [lia | reflexivity].
Qed.

Lemma wvi_child_depth : forall X i, (i < wv_nitems (y_t X))%nat ->
  (PjTree.depth (wvi_child X i) < PjTree.depth (y_t X))%nat.
Proof.
intros X i Hi. unfold wvi_child, wv_nitems in *. destruct (y_t X); cbn [length] in Hi; try lia.
- apply wvi_depth_arr. exact Hi.
- apply wvi_depth_obj. exact Hi.
Qed.

Lemma wvi_depth_pos : forall t, (0 < wv_nitems t)%nat -> (1 <= PjTree.depth t)%nat.
Proof. intros t H. destruct t; cbn in H |- *; lia. Qed.

(* the separator literal and the comma are write_value's literals *)
Lemma wvi_sep_lit : forall X, In (wv_sep_slot X, WriterValue.wsep (y_p X)) wv_lits.
Proof.
intros X. unfold wv_sep_slot, y_p, WriterValue.wsep, wv_lits.
destruct (y_pretty X =? 0); cbn [negb]; cbn [In]; auto 20.
Qed.

Lemma wvi_comma_lit : In (88%nat, [44]) wv_lits.
Proof. unfold wv_lits. cbn [In]. auto 20. Qed.

(* ---- the return pcs of the loop's jal's: text addresses below the ceiling (closed facts, one per slot) ---- *)
Lemma wvi_AF_lt : 4096 <= AF_write_value < 2 ^ 31.
Proof. unfold AF_write_value, WV_SLOT. split; vm_compute; congruence. Qed.

Lemma wvi_ret_ok : forall k, 0 <= k <= 300 ->
  4096 <= BASE + WVI_PC k /\ YK0s.ret_ok (Z_to_bv 64 (BASE + WVI_PC k)).
Proof.
intros k Hk. unfold WVI_PC. pose proof wvi_AF_lt as HA. pose proof (@pa_B_ok _ _ PA) as (HB0 & _ & _).
split; [lia|]. apply (ret_ok_codeptr_v (PI := PA)).
- change (2 ^ 40) with 1099511627776. change (2 ^ 31) with 2147483648 in HA. lia.
- unfold AF_write_value. apply Z.mod_divide; [lia|]. exists (2 * Z.of_nat WV_SLOT + 2 * k). lia.
Qed.

Ltac wvi_ceil_tac k :=
  unfold WVI_PC; pose proof wvi_AF_lt as HA;
  exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_B) (PI := PA) (AF_write_value + 4 * k)
    ltac:(change (2 ^ 31) with 2147483648 in HA; change (2 ^ 40) with 1099511627776; lia)
    ltac:(vm_compute; reflexivity)).
Lemma wvi_ceil_95 : BASE + WVI_PC 95 < YM05.alloc_ceiling.
Proof. wvi_ceil_tac 95. Qed.
Lemma wvi_ceil_100 : BASE + WVI_PC 100 < YM05.alloc_ceiling.
Proof. wvi_ceil_tac 100. Qed.
Lemma wvi_ceil_130 : BASE + WVI_PC 130 < YM05.alloc_ceiling.
Proof. wvi_ceil_tac 130. Qed.
Lemma wvi_ceil_134 : BASE + WVI_PC 134 < YM05.alloc_ceiling.
Proof. wvi_ceil_tac 134. Qed.
Lemma wvi_ceil_156 : BASE + WVI_PC 156 < YM05.alloc_ceiling.
Proof. wvi_ceil_tac 156. Qed.
Lemma wvi_ceil_173 : BASE + WVI_PC 173 < YM05.alloc_ceiling.
Proof. wvi_ceil_tac 173. Qed.

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

(* WriteValueB_Base's lemmas at this Section's variables *)
Let wv_pairwise_in2 := @WriteValueB_Base.wv_pairwise_in2.
Let wv_pow_facts := @WriteValueB_Base.wv_pow_facts fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_loc := @WriteValueB_Base.wv_loc fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_hbs := @WriteValueB_Base.wv_led_hbs fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_nodup := @WriteValueB_Base.wv_led_nodup fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_cnt := @WriteValueB_Base.wv_led_cnt fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_foot_keepR := @WriteValueB_Base.wv_foot_keepR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_nodeR_keep := @WriteValueB_Base.wv_nodeR_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_lit_home := @WriteValueB_Base.wv_lit_home fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_vm_keep := @WriteValueB_Base.wv_vm_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_keep := @WriteValueB_Base.wv_led_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_out_keep := @WriteValueB_Base.wv_out_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_arodata_keep := @WriteValueB_Base.wv_arodata_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_rdword_ext := @WriteValueB_Base.wv_rdword_ext fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_reca_keep := @WriteValueB_Base.wv_reca_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_cfp_closed := @WriteValueB_Base.wv_cfp_closed fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_arodata_jR := @WriteValueB_Base.wv_arodata_jR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_wmax_next := @WriteValueB_Base.wv_wmax_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_live_next := @WriteValueB_Base.wv_live_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_lam_keep := @WriteValueB_Base.wv_lam_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_fp_sub := @WriteValueB_Base.wv_fp_sub fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ra_sub := @WriteValueB_Base.wv_ra_sub fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ra_curR := @WriteValueB_Base.wv_ra_curR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_tvis_curR := @WriteValueB_Base.wv_tvis_curR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ev_first := @WriteValueB_Base.wv_ev_first fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ret_pos_one := @WriteValueB_Base.wv_ret_pos_one fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ret_pos_app := @WriteValueB_Base.wv_ret_pos_app fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.

Section cl.
Variable CTX0 : list (list Z).
Hypothesis PUT : forall fx' : YK11.FPState, tput_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : forall fx' : YK11.FPState, tput_string_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : forall fx' : YK11.FPState, tindent_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling; at the instance the allocator-model owner's preset_head_wide):
   a key string handed to put_string is cstr_ok (wvi_cstr_blk) *)
Hypothesis HW : prh_head_wide.

(* WriteValueB_Call's lemmas at this Section's float state *)
Let wv_neg_mod16 := @WriteValueB_Call.wv_neg_mod16 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_put := @WriteValueB_Call.wv_call_put fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_indent := @WriteValueB_Call.wv_call_indent fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_put_string := @WriteValueB_Call.wv_call_put_string fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_self := @WriteValueB_Call.wv_call_self fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).

Section cont.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

(* ---- THE JOIN OF THE BODY: wv_common after the pieces P at the float state fxc, and the head's register and frame
   facts at item counter i (wv_head's own conjuncts after the pieces). Every join of the loop comes after a put or
   another call of the container, and a call may realloc, so the join's journal is at wle' SEGS RZ_cf (Defs'
   wv_commonR / wv_headR / wv_clR at that relation) ---- *)
Definition wvi_rf (X : wvx) (i : nat) (Wc : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) : Prop :=
  let R := y_sp X - 192 in let v := y_v X in let rd := aview SEGS (w_H Wc) memc in
  getr regsc 2 = w64 R /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  getr regsc 8 = w64 (y_o X) /\ getr regsc 9 = w64 v /\ getr regsc 18 = w64 (v + 40) /\
  getr regsc 19 = w64 (y_pretty X) /\ getr regsc 20 = w64 (SHADOW_OFF + (v + 24) / 8) /\
  getr regsc 21 = w64 (Z.of_nat i) /\ getr regsc 22 = w64 (y_dep X + 1) /\
  getr regsc 23 = w64 (56 * Z.of_nat i) /\ getr regsc 24 = w64 (v + 24) /\
  getr regsc 25 = w64 (8 * Z.of_nat i) /\ getr regsc 26 = w64 0 /\
  getr regsc 27 = w64 (SHADOW_OFF + (v + 40) / 8) /\
  rdword rd (R + 8) = Some 3 /\ rdword rd (R + 16) = Some 0 /\ rdword rd (R + 24) = Some (y_dep X) /\
  rdword rd (R + 32) = Some (if y_pretty X =? 0 then 1 else 2) /\
  rdword rd (R + 40) = Some (SHADOW_OFF + (v + 32) / 8) /\ rdword rd (R + 48) = Some (v + 32) /\
  rdword rd (R + 56) = Some (WV_STR (wv_sep_slot X)) /\ rdword rd (R + 64) = Some (WV_STR 88) /\
  rdword rd (R + 72) = Some SHADOW_OFF /\ rdword rd (R + 80) = Some (SHADOW_OFF + v / 8) /\
  rdword rd (R + 88) = Some (bv_unsigned (getr (y_regs X) 27)) /\
  rdword rd (R + 96) = Some (bv_unsigned (getr (y_regs X) 26)) /\
  rdword rd (R + 104) = Some (bv_unsigned (getr (y_regs X) 25)) /\
  rdword rd (R + 112) = Some (bv_unsigned (getr (y_regs X) 24)) /\
  rdword rd (R + 120) = Some (bv_unsigned (getr (y_regs X) 23)) /\
  rdword rd (R + 128) = Some (bv_unsigned (getr (y_regs X) 22)) /\
  rdword rd (R + 136) = Some (bv_unsigned (getr (y_regs X) 21)) /\
  rdword rd (R + 144) = Some (bv_unsigned (getr (y_regs X) 20)) /\
  rdword rd (R + 152) = Some (bv_unsigned (getr (y_regs X) 19)) /\
  rdword rd (R + 160) = Some (bv_unsigned (getr (y_regs X) 18)) /\
  rdword rd (R + 168) = Some (bv_unsigned (getr (y_regs X) 9)) /\
  rdword rd (R + 176) = Some (bv_unsigned (getr (y_regs X) 8)) /\
  rdword rd (R + 184) = Some (bv_unsigned (getr (y_regs X) 1)).

Definition wvi_st (X : wvx) (fxc : YK11.FPState) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fxc P lyc Sc Hpc Wc memc mdc kc /\ wvi_rf X i Wc regsc memc.

Lemma wvi_head_st : forall X fxc i P lyc Sc Hpc Wc regsc memc mdc kc,
  wv_headR B ARx Pm (wle' SEGS RZ_cf) X fxc i P lyc Sc Hpc Wc regsc memc mdc kc ->
  wvi_st X fxc i P lyc Sc Hpc Wc regsc memc mdc kc /\ (i < wv_nitems (y_t X))%nat /\ P = wv_done X i.
Proof.
intros X fxc i P lyc Sc Hpc Wc regsc memc mdc kc (Hc & Hi & HP & Hr).
split; [split; [exact Hc | exact Hr] | split; [exact Hi | exact HP]].
Qed.

Lemma wvi_st_head : forall X fxc i P lyc Sc Hpc Wc regsc memc mdc kc,
  wvi_st X fxc i P lyc Sc Hpc Wc regsc memc mdc kc -> (i < wv_nitems (y_t X))%nat -> P = wv_done X i ->
  wv_headR B ARx Pm (wle' SEGS RZ_cf) X fxc i P lyc Sc Hpc Wc regsc memc mdc kc.
Proof.
intros X fxc i P lyc Sc Hpc Wc regsc memc mdc kc (Hc & Hr) Hi HP.
split; [exact Hc|]. split; [exact Hi|]. split; [exact HP | exact Hr].
Qed.

(* the shadow address the head's registers hold, as the engine forms it *)
Lemma wvi_sh_denot : forall E (k : nat) c x,
  ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= x -> 0 <= c -> x + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SHADOW_OFF + (x + c) / 8).
Proof.
intros E k c x Hk H32 Hx Hc Hxc.
assert (Hd : 0 <= (x + c) / 8 < 17592186044416)
  by (split; [apply Z.div_pos; wvi_zl | apply Z.div_lt_upper_bound; wvi_zl]).
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_srl3, (U_atom_off E k x c Hk) by wvi_zl.
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; wvi_zl).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; wvi_zl). lia.
Qed.

(* the frame word at 32: (pretty != 0) + 1 *)
Lemma wvi_p1_denot : forall E p, ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)) =
    Z_to_bv 64 (if p =? 0 then 1 else 2).
Proof.
intros E p Hp Rp. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 19 p Hp Rp), !U_SLit. change (zcanon 0) with 0. change (zcanon 1) with 1.
destruct (Z.eqb_spec p 0) as [->|Hn].
- reflexivity.
- replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Local Ltac wvi_er EL n r := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ n r eq_refl).
Local Ltac wvi_ex EL j := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j).

(* ---- THE SEATED JOIN at slot pc of the body (pa_entry_st_ok_full): the head's register and frame facts, the node's
   fields, i < n, and (kr) the key slot ---- *)
Lemma wvi_seat : forall X i Wc regsc memc pc tg (kr : bool) kids keys nn kp,
  (tg = 5 \/ tg = 6) ->
  wvi_rf X i Wc regsc memc ->
  0 <= y_pretty X < 2 ^ 64 -> 0 <= y_dep X < 2 ^ 31 ->
  y_sp X mod 16 = 0 -> YM05.alloc_ceiling + 192 <= y_sp X <= 2 ^ 47 ->
  y_v X mod 8 = 0 -> 4096 <= y_v X -> y_v X + 56 <= 2 ^ 47 ->
  (y_v X + 56 <= y_sp X - 192 \/ y_sp X <= y_v X) ->
  (y_v X + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= y_v X) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (y_v X) 56 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 tg ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) 8 kids ->
  kids mod 8 = 0 -> 4096 <= kids -> kids + 56 * Z.of_nat i + 56 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  (tg = 6 -> keys mod 8 = 0 /\ 4096 <= keys /\ keys + 8 * Z.of_nat i + 8 <= 2 ^ 47) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) 8 nn -> Z.of_nat i < nn < 2 ^ 64 ->
  Z.of_nat i <= 2 ^ 42 ->
  0 <= WV_STR (wv_sep_slot X) < 2 ^ 64 -> 0 <= WV_STR 88 < 2 ^ 64 ->
  (kr = true -> tg = 6 /\ 0 <= kp < 2 ^ 64 /\
     val_mem SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) 8 kp /\
     keys + 8 * Z.of_nat i + 8 <= YM05.alloc_ceiling /\
     (keys + 8 * Z.of_nat i + 8 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= keys + 8 * Z.of_nat i) /\
     range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 /\
     (keys + 8 * Z.of_nat i + 8 <= y_v X \/ y_v X + 56 <= keys + 8 * Z.of_nat i)) ->
  img_env VAL A_LIM (wvi_E X i regsc kids keys nn kp) /\ regs_ok (wvi_E X i regsc kids keys nn kp) wvi_regs regsc /\
  st_ok_pi SEGS VAL (wvi_E X i regsc kids keys nn kp) (wvi_ss pc tg kr)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx (wvi_SH kr) (wvi_E X i regsc kids keys nn kp) (mrestrict (w_H Wc) memc).
Proof.
intros X i Wc regsc memc pc tg kr kids keys nn kp Htg HRF Hpr Hdep Hsp16 Hsp Hv8 Hv4096 Hv47 Hvsp Hband Hra
  Vtg Vkids Hk8 Hk4096 Hkhi Vkeys Rkeys Hkey6 Vnn Rnn Hi42 Rsep Rcom Hkey.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
unfold wvi_rf in HRF. cbv beta zeta in HRF.
destruct HRF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168 & F176 & F184).
set (v := y_v X) in *. set (sp := y_sp X) in *.
set (E := wvi_E X i regsc kids keys nn kp).
set (ka := keys + 8 * Z.of_nat i) in *. set (ca := kids + 56 * Z.of_nat i) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wvi_E, wvi_EH; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regsc (wvi_extra (y_dep X) (WV_STR (wv_sep_slot X))
    (WV_STR 88) kids keys nn ka kp ca (wvi_sv13 X))) k)
  by (intros k Hk; subst E; unfold wvi_E, wvi_EH; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regsc 2) by wvi_er EL 2%nat (2%bv : bv 5).
assert (E9 : ew E 9 = getr regsc 9) by wvi_er EL 9%nat (9%bv : bv 5).
assert (E19 : ew E 19 = getr regsc 19) by wvi_er EL 19%nat (19%bv : bv 5).
assert (E21 : ew E 21 = getr regsc 21) by wvi_er EL 21%nat (21%bv : bv 5).
assert (E23 : ew E 23 = getr regsc 23) by wvi_er EL 23%nat (23%bv : bv 5).
assert (E25 : ew E 25 = getr regsc 25) by wvi_er EL 25%nat (25%bv : bv 5).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by wvi_ex EL 0%nat.
assert (E33 : ew E 33 = Z_to_bv 64 (y_dep X)) by wvi_ex EL 1%nat.
assert (E34 : ew E 34 = Z_to_bv 64 (WV_STR (wv_sep_slot X))) by wvi_ex EL 2%nat.
assert (E35 : ew E 35 = Z_to_bv 64 (WV_STR 88)) by wvi_ex EL 3%nat.
assert (E36 : ew E 36 = Z_to_bv 64 kids) by wvi_ex EL 4%nat.
assert (E37 : ew E 37 = Z_to_bv 64 keys) by wvi_ex EL 5%nat.
assert (E38 : ew E 38 = Z_to_bv 64 nn) by wvi_ex EL 6%nat.
assert (E39 : ew E 39 = Z_to_bv 64 ka) by wvi_ex EL 7%nat.
assert (E40 : ew E 40 = Z_to_bv 64 kp) by wvi_ex EL 8%nat.
assert (E41 : ew E 41 = Z_to_bv 64 ca) by wvi_ex EL 9%nat.
assert (E42 : ew E 42 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 8))) by wvi_ex EL 10%nat.
assert (E43 : ew E 43 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 9))) by wvi_ex EL 11%nat.
assert (E44 : ew E 44 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 18))) by wvi_ex EL 12%nat.
assert (E45 : ew E 45 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 19))) by wvi_ex EL 13%nat.
assert (E46 : ew E 46 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 20))) by wvi_ex EL 14%nat.
assert (E47 : ew E 47 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 21))) by wvi_ex EL 15%nat.
assert (E48 : ew E 48 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 22))) by wvi_ex EL 16%nat.
assert (E49 : ew E 49 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 23))) by wvi_ex EL 17%nat.
assert (E50 : ew E 50 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 24))) by wvi_ex EL 18%nat.
assert (E51 : ew E 51 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 25))) by wvi_ex EL 19%nat.
assert (E52 : ew E 52 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 26))) by wvi_ex EL 20%nat.
assert (E53 : ew E 53 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 27))) by wvi_ex EL 21%nat.
assert (E54 : ew E 54 = Z_to_bv 64 (bv_unsigned (getr (y_regs X) 1))) by wvi_ex EL 22%nat.
assert (Usp : bv_unsigned (ew E 2) = sp - 192)
  by (rewrite E2, G2; unfold w64; apply unsigned_lit_small; wvi_zl).
assert (Uv : bv_unsigned (ew E 9) = v) by (rewrite E9, G9; unfold w64; apply unsigned_lit_small; wvi_zl).
assert (E9' : ew E 9 = Z_to_bv 64 v) by (rewrite E9, G9; reflexivity).
assert (Ui : bv_unsigned (ew E 21) = Z.of_nat i) by (rewrite E21, G21; unfold w64; apply unsigned_lit_small; wvi_zl).
assert (U8i : bv_unsigned (ew E 25) = 8 * Z.of_nat i)
  by (rewrite E25, G25; unfold w64; apply unsigned_lit_small; wvi_zl).
assert (U56i : bv_unsigned (ew E 23) = 56 * Z.of_nat i)
  by (rewrite E23, G23; unfold w64; apply unsigned_lit_small; wvi_zl).
assert (Ukids : bv_unsigned (ew E 36) = kids) by (rewrite E36; apply unsigned_lit_small; wvi_zl).
assert (Ukeys : bv_unsigned (ew E 37) = keys) by (rewrite E37; apply unsigned_lit_small; wvi_zl).
assert (Uca : bv_unsigned (ew E 41) = ca) by (rewrite E41; apply unsigned_lit_small; subst ca; wvi_zl).
assert (Rbv : forall r : bv 5, 0 <= bv_unsigned (getr (y_regs X) r) < 2 ^ 64)
  by (intros r; apply u64_range).
(* the alignments the facts ask *)
assert (Hsp192 : (sp - 192) mod 16 = 0).
{ apply Z.mod_divide in Hsp16 as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q - 12). lia. }
assert (H8i : (8 * Z.of_nat i) mod 8 = 0) by (rewrite Z.mul_comm; apply Z.mod_mul; lia).
assert (H56i : (56 * Z.of_nat i) mod 8 = 0)
  by (apply Z.mod_divide; [lia|]; exists (7 * Z.of_nat i); lia).
assert (Hca8 : ca mod 8 = 0).
{ apply Z.mod_divide in Hk8 as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q + 7 * Z.of_nat i).
  subst ca. lia. }
(* the frame words, as chunk values *)
assert (FC : forall off e z, sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
    rdword (aview SEGS (w_H Wc) memc) (sp - 192 + off) = Some z ->
    YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp - 192) (YP09.mkChunk off (CVal 8 e))).
{ intros off e z He Hz Hw. apply (chunk_ok_val SEGS E _ (sp - 192) off 8 e z He); [wvi_zs | wvi_zs |].
  exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hw). }
assert (FA : forall off (n : nat) z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
    rdword (aview SEGS (w_H Wc) memc) (sp - 192 + off) = Some z ->
    YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp - 192) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n z Hn Hz Hw. apply (FC off (SOff n 0) z); [|exact Hz|exact Hw].
  cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Hregs : regs_ok E wvi_regs regsc).
{ apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let w := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with w end;
      first
      [ rewrite getr_zero; reflexivity
      | cbn [sv_denot]; rewrite Z.add_0_r, EL by (unfold A_TEXT; lia);
        rewrite ew_Ereg_lt by wvi_zl;
        match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regsc ?x)) =>
          let y := eval vm_compute in x in change x with y end;
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | rewrite (wvi_sh_denot E 9 40 v E9' E32) by wvi_zl; exact G27
      | rewrite (wvi_sh_denot E 9 24 v E9' E32) by wvi_zl; exact G20
      | cbn [sv_denot]; rewrite Uv; first [exact G18 | exact G24]
      | cbn [sv_denot]; exact G26 ]
    | ]).
  destruct Hr. }
assert (Hfacts_common :
  atoms_ok E [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
               (9%nat, mkAF 4096 (2 ^ 47 - 56) 3); (21%nat, mkAF 0 (2 ^ 42) 0); (25%nat, mkAF 0 (2 ^ 45) 3);
               (23%nat, mkAF 0 (2 ^ 48) 3); (36%nat, mkAF 4096 (2 ^ 47) 3);
               (41%nat, mkAF 4096 (2 ^ 47 - 56) 3) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Uv, Ui, U8i, U56i, Ukids, Uca, E32, unsigned_lit_small by (unfold SHADOW_OFF; wvi_zl).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF in *. subst ca.
  repeat match goal with |- _ /\ _ => split end; try exact I; wvi_zl. }
assert (Hf37 : tg = 6 -> atoms_ok E [(37%nat, mkAF 4096 (2 ^ 47) 3)]).
{ intros H6. destruct (Hkey6 H6) as (Hq8 & Hq4096 & Hqhi).
  cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ukeys. change (2 ^ 3) with 8.
  repeat match goal with |- _ /\ _ => split end; try exact I; wvi_zl. }
assert (Hcond : conds_ok E [mkAC BC_NE (SOff 38 0) (SLit 0); mkAC BC_LTU (SOff 21 0) (SOff 38 0)]).
{ cbn [conds_ok]. split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b].
  - rewrite branch_ne_U, (U_atom E 38 nn E38 ltac:(wvi_zl)), U_lit by wvi_zl.
    destruct (Z.eqb_spec nn 0); [wvi_zl | reflexivity].
  - rewrite branch_ltu_U, (U_atom E 38 nn E38 ltac:(wvi_zl)).
    rewrite (U_atom E 21 (Z.of_nat i)) by first [rewrite E21, G21; reflexivity | wvi_zl].
    apply Z.ltb_lt. lia. }
assert (Hal1 : sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 23 0)) = sv_denot E (SOff 41 0)).
{ rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 36 kids E36) by wvi_zl.
  rewrite (U_atom E 23 (56 * Z.of_nat i)) by first [rewrite E23, G23; reflexivity | wvi_zl].
  rewrite (U_atom E 41 ca E41) by (subst ca; wvi_zl). unfold ca. apply zcanon_id. unfold M64. wvi_zl. }
assert (Hframe : region_ok SEGS E (mrestrict (w_H Wc) memc) wvi_frame).
{ unfold region_ok, wvi_frame, wvi_chunks. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Usp. split; [wvi_zl|]. split; [wvi_zl|]. split; [intros o Ho; wvi_zl|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (FC 8 (SLit 3) 3); [reflexivity | wvi_zl | exact F8].
  - apply (FC 16 (SLit 0) 0); [reflexivity | wvi_zl | exact F16].
  - apply (FA 24 33%nat (y_dep X) E33); [wvi_zl | exact F24].
  - apply (FC 32 _ (if y_pretty X =? 0 then 1 else 2)); [| destruct (y_pretty X =? 0); wvi_zl | exact F32].
    apply wvi_p1_denot; [rewrite E19, G19; reflexivity | exact Hpr].
  - apply (FC 40 (wvi_sh 9 32) (SHADOW_OFF + (v + 32) / 8));
      [apply wvi_sh_denot; [exact E9' | exact E32 | wvi_zl | wvi_zl | wvi_zl] | | exact F40].
    assert (0 <= (v + 32) / 8 < 17592186044416) by (split; [apply Z.div_pos; wvi_zl | apply Z.div_lt_upper_bound; wvi_zl]).
    unfold SHADOW_OFF. wvi_zl.
  - apply (FC 48 (SOff 9 32) (v + 32)); [| wvi_zl | exact F48].
    rewrite denot_lit_U. f_equal. apply (U_atom_off E 9 v 32 E9'); wvi_zl.
  - apply (FA 56 34%nat _ E34); [exact Rsep | exact F56].
  - apply (FA 64 35%nat _ E35); [exact Rcom | exact F64].
  - apply (FA 72 32%nat SHADOW_OFF E32); [unfold SHADOW_OFF; wvi_zl | exact F72].
  - apply (FC 80 (wvi_sh 9 0) (SHADOW_OFF + v / 8));
      [unfold wvi_sh; rewrite (wvi_sh_denot E 9 0 v E9' E32) by wvi_zl; rewrite Z.add_0_r; reflexivity | | exact F80].
    assert (0 <= v / 8 < 17592186044416) by (split; [apply Z.div_pos; wvi_zl | apply Z.div_lt_upper_bound; wvi_zl]).
    unfold SHADOW_OFF. wvi_zl.
  - apply (FA 88 53%nat _ E53); [apply Rbv | exact F88].
  - apply (FA 96 52%nat _ E52); [apply Rbv | exact F96].
  - apply (FA 104 51%nat _ E51); [apply Rbv | exact F104].
  - apply (FA 112 50%nat _ E50); [apply Rbv | exact F112].
  - apply (FA 120 49%nat _ E49); [apply Rbv | exact F120].
  - apply (FA 128 48%nat _ E48); [apply Rbv | exact F128].
  - apply (FA 136 47%nat _ E47); [apply Rbv | exact F136].
  - apply (FA 144 46%nat _ E46); [apply Rbv | exact F144].
  - apply (FA 152 45%nat _ E45); [apply Rbv | exact F152].
  - apply (FA 160 44%nat _ E44); [apply Rbv | exact F160].
  - apply (FA 168 43%nat _ E43); [apply Rbv | exact F168].
  - apply (FA 176 42%nat _ E42); [apply Rbv | exact F176].
  - apply (FA 184 54%nat _ E54); [apply Rbv | exact F184]. }
assert (Hnode : region_ok SEGS E (mrestrict (w_H Wc) memc) (wvi_node tg)).
{ unfold region_ok, wvi_node. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Uv. split; [wvi_zl|]. split; [wvi_zl|]. split; [intros o Ho; wvi_zl|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ v 0 4 (SLit tg) tg);
      [reflexivity | destruct Htg as [-> | ->]; wvi_zs | wvi_zs | rewrite Z.add_0_r; exact Vtg].
  - apply (chunk_ok_val SEGS E _ v 24 8 (SOff 36 0) kids);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | wvi_zs | wvi_zs | exact Vkids].
  - apply (chunk_ok_val SEGS E _ v 32 8 (SOff 37 0) keys);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | wvi_zs | wvi_zs | exact Vkeys].
  - apply (chunk_ok_val SEGS E _ v 40 8 (SOff 38 0) nn);
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | wvi_zs | wvi_zs | exact Vnn]. }
assert (Hshv : shent_ok SEGS WV_Bx E (mrestrict (w_H Wc) memc) (mkSHE 9 0 56)).
{ apply (shent_ok_of_range SEGS (w_H Wc) memc E WV_Bx 9 v 56 v 0 56 Hra).
  - unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; wvi_zl). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E9', Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by wvi_zl. reflexivity.
  - wvi_zl.
  - wvi_zl.
  - intros a Ha. unfold SHADOW_OFF in *. wvi_zl. }
assert (HtgW : regions_wf (wvi_mem tg kr) = true) by (destruct Htg as [-> | ->]; destruct kr; vm_compute; reflexivity).
split; [exact HEI|]. split; [exact Hregs|].
destruct kr.
- (* the key slot seated: frame, node and key *)
  destruct (Hkey eq_refl) as (H6 & Rkp & Vkp & Hkac & Hkaband & Hkara & Hkav).
  destruct (Hkey6 H6) as (Hq8 & Hq4096 & Hqhi).
  assert (Hka8 : ka mod 8 = 0).
  { apply Z.mod_divide in Hq8 as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q + Z.of_nat i).
    subst ka. lia. }
  assert (Uka : bv_unsigned (ew E 39) = ka) by (rewrite E39; apply unsigned_lit_small; subst ka; wvi_zl).
  assert (Hkey_r : region_ok SEGS E (mrestrict (w_H Wc) memc) wvi_keyr).
  { unfold region_ok, wvi_keyr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Uka. split; [wvi_zl|]. split; [wvi_zl|]. split; [intros o Ho; wvi_zl|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ ka 0 8 (SOff 40 0) kp);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | wvi_zs | wvi_zs |
       rewrite Z.add_0_r; exact Vkp]. }
  assert (Hal2 : sv_denot E (SAlu ALU_ADD (SOff 37 0) (SOff 25 0)) = sv_denot E (SOff 39 0)).
  { rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 37 keys E37) by wvi_zl.
    rewrite (U_atom E 25 (8 * Z.of_nat i)) by first [rewrite E25, G25; reflexivity | wvi_zl].
    rewrite (U_atom E 39 ka E39) by (subst ka; wvi_zl). unfold ka. apply zcanon_id. unfold M64. wvi_zl. }
  split.
  + rewrite restrict_mkst_fx. unfold wvi_ss.
    apply pa_entry_st_ok_full.
    * exact Hregs.
    * exact HtgW.
    * unfold wvi_mem. repeat apply Forall_cons; try apply Forall_nil; [exact Hframe | exact Hnode | exact Hkey_r].
    * apply pairwise_disjoint_of_extents. unfold wvi_mem, extent_of_region, wvi_frame, wvi_node, wvi_keyr.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv, Uka.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      subst ka. repeat split; wvi_zl.
    * subst tg. unfold wvi_facts. cbn [Z.eqb Pos.eqb app].
      split.
      -- cbn [atoms_ok]. cbn [atoms_ok] in Hfacts_common.
         destruct Hfacts_common as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
         destruct (Hf37 eq_refl) as (A9 & _).
         repeat (split; [eassumption|]). split; [|exact I].
         unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Uka. change (2 ^ 3) with 8. subst ka.
         repeat match goal with |- _ /\ _ => split end; wvi_zl.
      -- split; [exact Hcond|]. cbn [app alias_ok]. split; [exact Hal1|]. split; [exact Hal2 | exact I].
  + unfold sh_ok, wvi_SH. constructor; [exact Hshv | constructor; [|constructor]].
    apply (shent_ok_of_range SEGS (w_H Wc) memc E WV_Bx 39 ka 8 ka 0 8 Hkara).
    * unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; wvi_zl). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (subst ka; wvi_zl). reflexivity.
    * wvi_zl.
    * wvi_zl.
    * intros a Ha. unfold SHADOW_OFF in *. subst ka. wvi_zl.
- (* frame and node only *)
  split.
  + rewrite restrict_mkst_fx. unfold wvi_ss.
    apply pa_entry_st_ok_full.
    * exact Hregs.
    * exact HtgW.
    * unfold wvi_mem. repeat apply Forall_cons; try apply Forall_nil; [exact Hframe | exact Hnode].
    * apply pairwise_disjoint_of_extents. unfold wvi_mem, extent_of_region, wvi_frame, wvi_node.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; wvi_zl.
    * unfold wvi_facts. rewrite !app_nil_r.
      split.
      -- destruct Htg as [-> | ->]; cbn [Z.eqb Pos.eqb app]; [exact Hfacts_common|].
         cbn [atoms_ok]. cbn [atoms_ok] in Hfacts_common.
         destruct Hfacts_common as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
         destruct (Hf37 eq_refl) as (A9 & _).
         repeat (split; [eassumption|]). exact I.
      -- split; [exact Hcond|]. cbn [alias_ok]. split; [exact Hal1 | exact I].
  + unfold sh_ok, wvi_SH. constructor; [exact Hshv | constructor].
Qed.


(* ---- the float invariant of a join across a call: the callee's fregs_kept_x composes ---- *)
Lemma wvi_fk_refl : forall f : YK11.FPState, fregs_kept_x f f.
Proof. intros f r _. reflexivity. Qed.

Lemma wvi_fk_trans : forall f1 f2 f3 : YK11.FPState,
  fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* ---- the entry's layout facts the loop uses (fpre / fwin of wv_pre) ---- *)
Lemma wvi_pre_facts : forall X ch, wv_pre B ARx CTX0 Pm X ch -> 192 <= y_STK X ->
  ARx (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) /\
  YM05.alloc_ceiling + 192 <= y_sp X /\ y_sp X <= 2 ^ 47 /\ y_sp X mod 16 = 0 /\
  0 <= y_d X /\ y_d X mod 16 = 0 /\ y_sp X + y_d X <= ly_top (y_ly X) /\ ly_top (y_ly X) <= ly_stk_hi (y_ly X) /\
  ly_stk_hi (y_ly X) <= 2 ^ 47 /\ y_sp X + 64 <= ly_stk_hi (y_ly X) /\
  y_o X mod 8 = 0 /\ y_sp X <= y_o X /\ y_o X + 32 <= y_sp X + y_d X /\
  raZ (y_regs X) < YM05.alloc_ceiling /\ 0 <= WriterApp.w_cnt (y_st X) /\
  (WriterApp.w_cap (y_st X) <> 0 -> In (y_buf X, WriterApp.w_cap (y_st X)) (y_Lam X)) /\
  0 <= WriterApp.w_cap (y_st X).
Proof.
intros X ch Hpre HSTK.
destruct Hpre as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & Ho1 & Ho2 & HOUT & HLED & _).
pose proof HPRE as (HPREx & HRO & HTOP & HRAZ & _).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
unfold y_sp. split; [exact HAR|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
split; [exact Hd0|]. split; [exact Hd16|]. split; [exact Hdtop|]. split; [exact Htop2|]. split; [exact H47|].
split; [exact HTOP|]. split; [exact Hoal|]. split; [exact Ho1|]. split; [exact Ho2|]. split; [exact HRAZ|].
split; [exact (wv_led_cnt _ _ _ _ _ _ _ _ _ _ _ _ HLED)|]. split; [|lia].
intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin].
Qed.

(* a byte at or above the ceiling and off the struct is off the writer's footprint (the buffer is a block, below it) *)
Lemma wvi_nfp : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own o buf st a,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhWriter_out W mem Lam o buf st ->
  YM05.alloc_ceiling <= a -> ~ (o <= a < o + 32) ->
  ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own o buf st a HAR HLED HOUT Ha Ho Hf.
unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hs | Hb]; [exact (Ho Hs)|].
unfold prhWriter_fp in Hb. destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [_|Hc]; [exact (inFP_nil a Hb)|].
destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [lia|].
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (HF _ Hin) as (_ & Hbl & _). cbn [fst snd] in Hbl.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & _ & Hce & _).
destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
Qed.

(* the entry footprint opens no sink *)
Lemma wvi_fp_closed : forall X ch, wv_pre B ARx CTX0 Pm X ch -> ~ YI16.sink_open_fp (y_FP X).
Proof.
intros X ch Hpre.
destruct Hpre as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & Ho1 & Ho2 & HOUT & HLED & _).
pose proof HPRE as ((HAR & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
pose proof cf_head_nonneg as Hh0.
unfold y_FP. apply wv_cfp_closed; [unfold y_sp in *; lia|].
intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia|].
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
destruct (HF _ Hin) as (_ & Hbl & _). cbn [fst snd] in Hbl.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hbl) as (_ & H4096 & _). lia.
Qed.

(* ---- what a run from a seated join keeps: every byte (the seated state has no write window) ---- *)
Lemma wvi_nowin_gen : forall E rs (m0 m1 : word -> option byte) (H : word -> bool),
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  frame_of E rs (mrestrict H m0) (mrestrict H m1) ->
  forall a, aview SEGS H m1 a = aview SEGS H m0 a.
Proof.
intros E rs m0 m1 H Hw Hfr a. apply (aview_eq_of SEGS). apply Hfr.
intros (r & Hr & Ha). rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

(* the seated registers' atoms are all below 55 *)
Lemma wvi_regs_atoms : forallb (fun r : bv 5 => sv_atoms_lt 55 (sr_get wvi_regs r)) all_regs = true.
Proof. vm_compute. reflexivity. Qed.

(* a state whose callee-saved registers are the seated ones (syntactically), at an env that agrees with the seat's
   below 55, has the seat's callee-saved values *)
Lemma wvi_aregs : forall E E' (srs : list sv) regs0 regs1,
  (forall r, getr regs1 r = sv_denot E' (sr_get srs r)) -> regs_ok E wvi_regs regs0 -> env_agree 55 E E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get wvi_regs r)) CALLEE_SAVED = true ->
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
pose proof wvi_regs_atoms as Ha. rewrite forallb_forall in Ha. apply Ha. apply all_regs_in.
Qed.

Lemma wvi_agree_ext : forall E K ws, (55 <= K)%nat -> env_agree 55 E (extK E K ws).
Proof.
intros E K ws HK. destruct (env_agree_extK E K ws) as [HA HD]. split; [intros n Hn; apply HA; lia | exact HD].
Qed.

Lemma wvi_agree_set : forall E E' k w, (55 <= k)%nat -> env_agree 55 E E' -> env_agree 55 E (ewset E' k w).
Proof.
intros E E' k w Hk [HA HD]. split; [intros n Hn; rewrite ew_ewset_other by lia; exact (HA n Hn) | exact HD].
Qed.

Ltac wvi_agree := repeat (apply wvi_agree_set; [lia|]); first [apply env_agree_refl | apply wvi_agree_ext; lia].

(* an atom of the seat's env, read in an env that agrees with it below 55 *)
Lemma wvi_ew_agree : forall E E' (n : nat) w, env_agree 55 E E' -> (n < 55)%nat -> ew E n = w -> ew E' n = w.
Proof. intros E E' n w [HA _] Hn Hw. rewrite (HA n Hn). exact Hw. Qed.

Local Ltac wvi_cs := unfold acallee_saved; lia.

(* the register and frame-word facts survive a keep of the frame and of the callee-saved registers *)
Lemma wvi_rf_keep : forall X i (W W' : world SEGS) regs regs' mem mem',
  wvi_rf X i W regs mem -> aregs_preserved regs regs' ->
  (forall a, y_sp X - 192 <= a < y_sp X -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  wvi_rf X i W' regs' mem'.
Proof.
intros X i W W' regs regs' mem mem' HRF HAP HK.
unfold wvi_rf in HRF |- *. cbv beta zeta in HRF |- *.
destruct HRF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168 & F176 & F184).
assert (RW : forall off, 0 <= off <= 184 ->
  rdword (aview SEGS (w_H W') mem') (y_sp X - 192 + off) = rdword (aview SEGS (w_H W) mem) (y_sp X - 192 + off))
  by (intros off Hoff; apply wv_rdword_ext; intros j Hj; apply HK; lia).
assert (RG : forall r : Z, acallee_saved r -> forall w, getr regs (Z_to_bv 5 r) = w -> getr regs' (Z_to_bv 5 r) = w)
  by (intros r Hr w Hw; rewrite (HAP r Hr); exact Hw).
split; [exact (RG 2 ltac:(wvi_cs) _ G2)|]. split; [exact (RG 3 ltac:(wvi_cs) _ G3)|].
split; [exact (RG 4 ltac:(wvi_cs) _ G4)|]. split; [exact (RG 8 ltac:(wvi_cs) _ G8)|].
split; [exact (RG 9 ltac:(wvi_cs) _ G9)|]. split; [exact (RG 18 ltac:(wvi_cs) _ G18)|].
split; [exact (RG 19 ltac:(wvi_cs) _ G19)|]. split; [exact (RG 20 ltac:(wvi_cs) _ G20)|].
split; [exact (RG 21 ltac:(wvi_cs) _ G21)|]. split; [exact (RG 22 ltac:(wvi_cs) _ G22)|].
split; [exact (RG 23 ltac:(wvi_cs) _ G23)|]. split; [exact (RG 24 ltac:(wvi_cs) _ G24)|].
split; [exact (RG 25 ltac:(wvi_cs) _ G25)|]. split; [exact (RG 26 ltac:(wvi_cs) _ G26)|].
split; [exact (RG 27 ltac:(wvi_cs) _ G27)|].
repeat (split; [rewrite RW by lia; assumption|]). rewrite RW by lia. assumption.
Qed.

(* wv_common across a run that writes nothing: the journal and Pm are the runner's, the rest is kept *)
Lemma wvi_common_run : forall X fxc P lyc Sc Hpc Wc memc mdc kc mem' md',
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fxc P lyc Sc Hpc Wc memc mdc kc ->
  0 <= y_o X -> y_o X + 32 <= 2 ^ 64 ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc mem' md' kc ->
  Pm mem' ->
  (forall a, aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a) ->
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fxc P lyc Sc Hpc Wc mem' md' kc.
Proof.
intros X fxc P lyc Sc Hpc Wc memc mdc kc mem' md' Hc Ho0 Ho64 HJ' HPm' HK.
destruct Hc as (HJ & HKW & _ & (ok & ranc & bufc & Lamc & peakc & Hoks & HOUT & HLED & HBLK & Hpos) & Hroom & HRO &
  Hz & Hk).
pose proof (proj1 HJ) as HAR.
assert (HKP : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a)
  by (intros a _ _; apply HK).
split; [exact HJ'|]. split; [intros a Ha Hf; rewrite HK; exact (HKW a Ha Hf)|]. split; [exact HPm'|].
split.
- exists ok, ranc, bufc, Lamc, peakc. split; [exact Hoks|]. split.
  + eapply (wv_out_keep lyc Sc Hpc Wc Wc memc mem' mdc Lamc peakc _ _ ranc (y_most X) (y_own X) (y_o X) bufc _
      (fun _ => False));
      [exact HAR | exact HLED | exact HOUT | exact HKP | intros a _ [] | intros a Ha; split; [lia | intros []]].
  + split; [|split; [exact HBLK | exact Hpos]].
    eapply (wv_led_keep lyc Sc Hpc Wc mdc memc mem' Lamc peakc _ _ ranc (y_most X) (y_own X) (fun _ => False));
      [exact HAR | exact HLED | exact HKP | intros a _ []].
- split; [exact Hroom|]. split; [|exact (conj Hz Hk)].
  apply (wv_arodata_keep Wc Wc memc mem' (fun _ => False)); [exact HRO | exact HKP | intros a _ []].
Qed.

(* ---- the stack each inner call needs fits under write_value's own frame ---- *)
Lemma wvi_stk : forall n', STK_put + 192 <= STK_write_value (S n') /\ STK_indent + 192 <= STK_write_value (S n') /\
  STK_put_string + 192 <= STK_write_value (S n') /\ STK_write_value n' + 192 <= STK_write_value (S n') /\
  192 <= STK_write_value n'.
Proof.
intros n'. unfold STK_write_value.
assert (HF : pi_frame F_write_value = 192) by (vm_compute; reflexivity). rewrite !HF.
assert (H1 : STK_put <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
assert (H2 : STK_indent <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
assert (H3 : STK_put_string <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
assert (H4 : 0 <= zmaxl [STK_RT_STR; STK_indent; STK_put; STK_put_string]) by (vm_compute; congruence).
rewrite !Nat2Z.inj_succ. lia.
Qed.

(* the stack top of the journal's current layout is the entry's *)
Lemma wvi_stkhi : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STK sp0 FP ly S Hp W mem md own
    lyc Sc Hpc Wc memc mdc kc ->
  ly_stk_hi lyc = ly_stk_hi ly.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc HJ.
pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _). exact Eshi.
Qed.

(* eight visible bytes form a word *)
Lemma wvi_rdword_some : forall (rd : Z -> option Z) a, (forall j, 0 <= j < 8 -> rd (a + j) <> None) ->
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

(* The case-1 words below o (form (a)) at any join: case 1 from the entry's (the bytes [o - 16, o) are kept: in the
   caller window, off FP), case 2 (o = sp + 8) from the saved ra at R + 184 (below the ceiling by fpre) and the caller
   word at sp (present by fwin, kept) *)
Lemma wvi_owords : forall X ch fxc i P lyc Sc Hpc Wc regs memc mdc kc,
  192 <= y_STK X -> wv_pre B ARx CTX0 Pm X ch -> wvi_st X fxc i P lyc Sc Hpc Wc regs memc mdc kc ->
  exists ra, rdword (aview SEGS (w_H Wc) memc) (y_o X - 8) = Some ra /\
    exists nfp, rdword (aview SEGS (w_H Wc) memc) (y_o X - 16) = Some nfp /\ nfp < YM05.alloc_ceiling.
Proof.
intros X ch fxc i P lyc Sc Hpc Wc regs memc mdc kc HSTK Hpre (Hcom & Hrf).
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcut & Hca & _ & HWIN & _ & _ & HOUT & HLED & _).
destruct Hcom as (_ & HKW & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HK16 : forall a, y_sp X <= a < y_o X ->
    aview SEGS (w_H Wc) memc a = aview SEGS (w_H (y_W X)) (y_mem X) a).
{ intros a Ha. apply HKW; [lia|]. unfold y_FP.
  apply (wvi_nfp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HAR0 HLED HOUT); lia. }
destruct Hcut as [H1 | H2].
- apply (wv_reca_keep (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) memc) (y_o X));
    [intros a Ha; apply HK16; lia | exact (Hca H1)].
- unfold wvi_rf in Hrf. cbv beta zeta in Hrf.
  destruct Hrf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F184).
  pose proof HWIN as (_ & _ & _ & Hdpres).
  destruct (wvi_rdword_some (aview SEGS (w_H (y_W X)) (y_mem X)) (y_sp X)) as [w Hw].
  { intros j Hj. apply (aview_some_of_apresent SEGS). apply Hdpres. unfold y_sp in *. lia. }
  exists w. split.
  + rewrite (wv_rdword_ext (aview SEGS (w_H (y_W X)) (y_mem X)) (aview SEGS (w_H Wc) memc)).
    * replace (y_o X - 8) with (y_sp X) by lia. exact Hw.
    * intros j Hj. apply HK16. lia.
  + exists (bv_unsigned (getr (y_regs X) 1)). split.
    * replace (y_o X - 16) with (y_sp X - 192 + 184) by lia. exact F184.
    * exact HRAZ.
Qed.

(* ---- THE MODEL-RUN POSITION AT A JOIN ---- *)
Lemma wvi_pre_ev : forall X ch, wv_pre B ARx CTX0 Pm X ch ->
  prh_run_at (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpi X)
    (prhWriter_evs [] (y_st X) (WriterValue.wvpieces (y_t X) (y_p X) (y_dep X))).
Proof.
intros X ch Hpre.
destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
exact Hev.
Qed.

Lemma wvi_run_at_mid : forall rp_sm rp_x rp_os rp_i st PP P2 P3 ok,
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

(* ---- AFTER AN INNER CALL: the join at P ++ Q at the callee's exit float state fx2, from the join at P (float state
   fxc) and the callee's post (its journal from the entry, its window keep from the call memory, the preserved
   registers, the room, the writer's run Q, the memnorm keep, frm_zero fx2, fregs_kept_x fxc fx2) ---- *)
Lemma wvi_after : forall X ch (fxc fx2 : YK11.FPState) i P Q lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc
    ly2 S2 Hp2 W2 regs2 mem2 md2 k2 lo hi,
  192 <= y_STK X -> wv_pre B ARx CTX0 Pm X ch -> wvi_st X fxc i P lyc Sc Hpc Wc regs memc mdc kc ->
  prhW_oksg ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) (y_ran X) ranc ->
  prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
    (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) ->
  prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
    (prhWriter_putN ok (y_st X) P) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] ly2 S2 Hp2 W2 mem2 md2 k2 ->
  lo <= y_sp X - 192 -> y_sp X + y_d X <= hi ->
  (forall a, lo <= a < hi -> ~ inFP (prhWriter_cfp (y_o X) bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P))) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  aregs_preserved regs regs2 ->
  room_live_cf S2 ->
  prhWriter_ret_pos B (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpH0 X) (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat
    lyc Sc Lamc peakc ranc (y_most X) (y_own X) (y_o X) bufc (prhWriter_putN ok (y_st X) P) Q
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  frm_zero (@YK11.fp_csr fx2) -> fregs_kept_x fxc fx2 ->
  wvi_st X fx2 i (P ++ Q) ly2 S2 Hp2 W2 regs2 mem2 md2 k2.
Proof.
intros X ch fxc fx2 i P Q lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 lo hi
  HSTK Hpre (Hcom & Hrf) Hoks HOUT HLED HBLK HJ2 Hlo Hhi HKC HAP Hroom2 HRP HMN Hz2 Hk2.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as ((_ & HRO0 & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _).
assert (Hpk0 : 0 <= y_peak X)
  by (pose proof HLED0 as Hb0; apply prh_ledger_bounds in Hb0; destruct Hb0 as (Hb0 & _); lia).
destruct Hcom as (HJc & HKW & HPmc & _ & _ & HROc & Hzc & Hkc).
pose proof (proj1 HJc) as HARc.
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HNF : forall a, YM05.alloc_ceiling <= a -> ~ (y_o X <= a < y_o X + 32) ->
    ~ inFP (prhWriter_cfp (y_o X) bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P))) a)
  by (intros a Ha Ho; exact (wvi_nfp lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (y_most X) (y_own X) (y_o X) bufc _ a
        HARc HLED HOUT Ha Ho)).
split.
- split; [exact HJ2|].
  split.
  { intros a Ha Hf. rewrite (HKC a ltac:(lia)); [exact (HKW a Ha Hf)|].
    apply HNF; [lia|]. intros Ho. apply Hf. unfold y_FP, prhWriter_cfp. apply inFP_cons. left. exact Ho. }
  split; [exact (PCALL memc mem2 HMN HPmc)|].
  split.
  { destruct (wv_ret_pos_app (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpH0 X) (y_rpi X) _ (y_ly X) (y_S X) (y_Lam X)
      (y_peak X) (y_ran X) (y_most X) (y_own X) (y_o X) (y_buf X) (y_st X) P Q ok ranc bufc Lamc peakc lyc Sc Hpc
      Wc memc ly2 S2 Hp2 W2 regs2 mem2 md2 Hcnt Hpk0 eq_refl Hoks HOUT HLED HBLK HRP) as (ok' & HR & HG & hist' & Hpos').
    destruct (prhWriter_ret_ok_g B ok' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpk0 HG HR)
      as (ran' & buf' & Lam' & peak' & HR1 & HR2 & HR3 & HR4).
    exists ok', ran', buf', Lam', peak'.
    split; [exact HR1|]. split; [exact HR2|]. split; [exact HR3|]. split; [exact HR4|].
    exists hist'. exact Hpos'. }
  split; [exact Hroom2|].
  split; [exact (wv_arodata_jR (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 (wvi_fp_closed X ch Hpre)
            HRO0)|].
  split; [exact Hz2 | exact (wvi_fk_trans _ _ _ Hkc Hk2)].
- apply (wvi_rf_keep X i Wc W2 regs regs2 memc mem2 Hrf HAP).
  intros a Ha. apply HKC; [lia|]. apply HNF; [lia|]. lia.
Qed.

(* ---- AN INNER CALL SITE: what every inner call (at the frame base R = sp - 192, oc = - (d + 192)) takes, from
   wv_pre and the join at the call memory, for a run of pieces P2 that the container's pieces continue after P ---- *)
Lemma wvi_ctx : forall n' X ch fxc i P P2 P3 lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wvi_st X fxc i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ P2 ++ P3 ->
  exists ok ranc bufc Lamc peakc rpi rph ra1 nfp1,
    prhW_oksg ok (WriterApp.w_cnt (y_st X)) (WriterApp.w_fail (y_st X)) (prhWriter_k ok (y_st X) P) (y_ran X) ranc /\
    prhWriter_out Wc memc Lamc (y_o X) bufc (prhWriter_putN ok (y_st X) P) /\
    prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (y_st X) P))
      (WriterApp.w_fail (prhWriter_putN ok (y_st X) P)) ranc (y_most X) (y_own X) /\
    prhWriter_blk B (y_ly X) (y_S X) (y_Lam X) (y_peak X) (y_buf X) (y_st X) lyc Sc Lamc peakc bufc
      (prhWriter_putN ok (y_st X) P) /\
    rpi = (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat /\
    PresetRoomPos.iface_room_pos (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph Sc /\
    prh_run_at (y_rpsm X) (y_rpx X) (y_rpos X) rpi (prhWriter_evs [] (prhWriter_putN ok (y_st X) P) P2) /\
    PRH_Base.prh_cons_from (y_rpsm X) (y_rpx X) (y_rpos X) rpi
      (length (prhWriter_evs [] (prhWriter_putN ok (y_st X) P) P2)) /\
    (length (y_rpos X) <= 4)%nat /\
    room_live_cf Sc /\
    arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
    ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (y_STK X + y_d X) (y_sp X + y_d X)
      (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc /\
    rdword (aview SEGS (w_H Wc) memc) (y_o X - 8) = Some ra1 /\
    rdword (aview SEGS (w_H Wc) memc) (y_o X - 16) = Some nfp1 /\ nfp1 < YM05.alloc_ceiling /\
    spZ regs = y_sp X + y_d X + - (y_d X + 192) /\ (- (y_d X + 192)) mod 16 = 0 /\ - (y_d X + 192) <= 0 /\
    y_sp X + y_d X + - (y_d X + 192) + 64 <= ly_stk_hi lyc /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ s0Z regs = y_o X /\
    y_sp X + y_d X + - (y_d X + 192) + 16 <= y_o X /\ y_o X + 32 <= y_sp X + y_d X /\
    Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok (y_st X) P))) + Z.of_nat (length (concat P2)) + 1
      <= prhWriter_WMAX /\
    prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok (y_st X) P) P2) /\
    fp_sub_x B (y_STK X + y_d X) (y_sp X + y_d X) (y_FP X)
      (prhWriter_cfp (y_o X) bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P))) (y_ly X) (y_S X) [] lyc Sc /\
    (WriterApp.w_cap (prhWriter_putN ok (y_st X) P) <> 0 ->
       In (bufc, WriterApp.w_cap (prhWriter_putN ok (y_st X) P)) Lamc) /\
    0 <= WriterApp.w_cap (prhWriter_putN ok (y_st X) P) /\
    prh_univ_closure B CTX0 /\ prhWriter_WMAX + cf_head < cf_malloc_max /\
    Z.of_nat (length (frames Sc)) < fs_frames 0 /\ frm_zero (@YK11.fp_csr fxc).
Proof.
intros n' X ch fxc i P P2 P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
destruct (wvi_owords X ch fxc i P lyc Sc Hpc Wc regs memc mdc kc HSTK Hpre Hst) as (ra1 & Hra1 & nfp1 & Hnfp1 & Hnfpc).
pose proof Hpre as (_ & _ & _ & Hcl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HLED0 & _ & _ & _ &
  _ & _ & _ & _ & Hfr0 & Hwmax & Hhead & Hlive & _ & Hcons0 & Hos).
destruct Hst as (Hcom & Hrf).
destruct Hcom as (HJc & HKW & HPmc & (ok & ranc & bufc & Lamc & peakc & Hoks & HOUT & HLED & HBLK & (rph & Hrp)) &
  Hroom & HROc & Hzc & Hkc).
pose proof (proj1 HJc) as HARc.
unfold wvi_rf in Hrf. cbv beta zeta in Hrf.
destruct Hrf as (G2 & G3 & G4 & G8 & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
pose proof HOUT as (_ & _ & Hcapc & _).
exists ok, ranc, bufc, Lamc, peakc, (y_rpi X + length (prhWriter_evs ok (y_st X) P))%nat, rph, ra1, nfp1.
split; [exact Hoks|]. split; [exact HOUT|]. split; [exact HLED|]. split; [exact HBLK|].
split; [reflexivity|]. split; [exact Hrp|].
split; [apply (wvi_run_at_mid _ _ _ _ _ P P2 P3); rewrite <- Hpcs; exact (wvi_pre_ev X ch Hpre)|].
split; [apply (prhW_cons_mid _ _ _ _ _ _ P P2 P3); rewrite <- Hpcs; exact Hcons0|]. split; [exact Hos|].
split; [exact Hroom|]. split; [exact HROc|]. split; [exact HJc|].
split; [exact Hra1|]. split; [exact Hnfp1|]. split; [exact Hnfpc|].
split.
{ assert (E2 : spZ regs = bv_unsigned (w64 (y_sp X - 192))) by (unfold spZ; f_equal; exact G2).
  rewrite E2. unfold w64. rewrite unsigned_lit_small; unfold y_sp in *; lia. }
split; [apply wv_neg_mod16; rewrite Z.add_mod, Hd16 by lia; reflexivity|].
split; [lia|].
split; [rewrite (wvi_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc); lia|].
split; [exact G3|]. split; [exact G4|].
split.
{ assert (E8 : s0Z regs = bv_unsigned (w64 (y_o X))) by (unfold s0Z; f_equal; exact G8).
  rewrite E8. unfold w64. rewrite unsigned_lit_small; [reflexivity | unfold y_sp in *; lia]. }
split; [lia|]. split; [exact Ho2|].
split; [apply (wv_wmax_next ok (y_st X) P P2 P3); rewrite <- Hpcs; exact Hwmax|].
split.
{ apply (wv_live_next (y_S X) Sc (y_ly X) lyc (y_Lam X) (y_peak X) (y_buf X) (y_st X) ok P P2 P3 Lamc peakc bufc
    Hcap0 HBLK).
  rewrite <- Hpcs. exact Hlive. }
split; [exact (wv_fp_sub (y_STK X + y_d X) (y_sp X + y_d X) (y_ly X) (y_S X) lyc Sc Hpc Wc memc mdc (y_o X)
          (y_Lam X) (y_peak X) (y_buf X) (y_st X) Lamc peakc bufc _ HARc Hcap0 HBLK)|].
split.
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
split; [lia|]. split; [exact Hcl|]. split; [exact Hhead|].
split; [|exact Hzc].
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app]. exact Hfr0.
Qed.

(* ---- the tree at a join: the node and its i-th item / member ---- *)
Lemma wvi_items_nth : forall (Pn : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D i,
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

Lemma wvi_mems_nth : forall m lblk (Pn : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i,
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
Lemma wvi_node_cur : forall X ch fxc P lyc Sc Hpc Wc memc mdc kc,
  192 <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fxc P lyc Sc Hpc Wc memc mdc kc ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) (y_v X) (y_t X) (y_D X) /\
  prhWriter_tree_vis Wc memc (y_D X) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (y_v X) 56.
Proof.
intros X ch fxc P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as ((HPREx & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HLED0 & _ &
  HNODE & HLOC & HRA & HTV & HD & Hoff & _).
pose proof HPREx as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hcom as (HJc & HKW & _ & (ok & ranc & bufc & Lamc & peakc & Hoks & HOUT & HLED & HBLK & _) & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (Hbufb : WriterApp.w_cap (y_st X) <> 0 ->
    In (y_buf X - cf_head, WriterApp.w_cap (y_st X) + cf_head) (ablocks B (y_ly X) (y_S X))).
{ intros Hc. pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED0 _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
assert (HLK : forall a k, In (a, k) (y_Lam X) -> a <> y_buf X -> In (a, k) Lamc).
{ intros a k Hin Hab.
  exact (proj1 (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ _ _ HLED) HBLK a k Hin Hab)). }
split; [|split].
- apply (wv_nodeR_keep (y_W X) Wc (y_mem X) memc (y_Lam X) (y_v X) (y_t X) (y_D X) HNODE).
  + intros x Hx. exact (proj1 (wv_foot_keepR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X)
      (y_mem X) (y_md X) (y_STK X) (y_STK X + y_d X) (y_d X) (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)) (y_Lam X)
      (y_peak X) _ _ (y_ran X) (y_most X) (y_own X) (y_v X) (y_D X) lyc Sc Hpc Wc memc mdc kc HSTK Hd0 HAR0 Hstk HLED0
      HLOC HD Hoff Hcap0 Hbufin HJc HKW x Hx)).
  + intros x Hx. exact (proj2 (wv_foot_keepR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X)
      (y_mem X) (y_md X) (y_STK X) (y_STK X + y_d X) (y_d X) (y_o X) (y_buf X) (WriterApp.w_cap (y_st X)) (y_Lam X)
      (y_peak X) _ _ (y_ran X) (y_most X) (y_own X) (y_v X) (y_D X) lyc Sc Hpc Wc memc mdc kc HSTK Hd0 HAR0 Hstk HLED0
      HLOC HD Hoff Hcap0 Hbufin HJc HKW x Hx)).
- eapply (wv_tvis_curR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_buf X)
    (y_D X) (y_STK X + y_d X) (y_sp X + y_d X) (y_o X) (WriterApp.w_cap (y_st X)) lyc Sc Hpc Wc memc mdc kc Lamc
    peakc _ _ ranc (y_most X) (y_own X) HAR0 HTV HD).
  + intros a k Hin. pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED0 _ Hin) as (_ & Hbl & _). exact Hbl.
  + exact HJc.
  + exact HLED.
  + exact HLK.
  + unfold y_sp in *. lia.
  + exact Hbufb.
- eapply (wv_ra_curR (wle' SEGS RZ_cf) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_buf X)
    (y_v X) (y_regs X) (y_STK X) (y_d X) (y_o X) (WriterApp.w_cap (y_st X)) lyc Sc Hpc Wc memc mdc kc Lamc peakc
    _ _ ranc (y_most X) (y_own X) HAR0 Hstk HRA HLOC HJc HLED HLK); [unfold y_sp in *; lia | exact Hbufb].
Qed.

(* the tree under a wider block predicate (the current ledger keeps every tree block) *)
Lemma wvi_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (Pn Pn' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
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

Lemma wvi_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR SEGS m lblk p t D ->
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
  apply (wvi_mems_lblk m lblk lblk' (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') members kids keys Di Hi).
  + intros x k Hin Hl. apply HL; [apply HDi; exact Hin | exact Hl].
  + intros nm u a' D1 Hin Hinc HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hin). cbn [snd] in IH.
    apply (IH m lblk lblk' a' D1 HP). intros a k Hin2 Hl. apply HL; [apply HDi; apply Hinc; exact Hin2 | exact Hl].
Qed.

(* ---- the node's fields and item i at a join's memory, from the tree there ---- *)
Lemma wvi_item_facts : forall X ch fxc P lyc Sc Hpc Wc memc mdc kc i,
  192 <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fxc P lyc Sc Hpc Wc memc mdc kc ->
  (i < wv_nitems (y_t X))%nat ->
  exists kids keys nn cap D1,
    val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 (wv_tagc (y_t X)) /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) kids /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) keys /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) nn /\
    nn = Z.of_nat (wv_nitems (y_t X)) /\ nn <= cap /\ 0 < cap /\
    In (kids, 56 * cap) (y_D X) /\
    pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) (kids + 56 * Z.of_nat i) (wvi_child X i) D1 /\
    (forall b, In b D1 -> In b (y_D X)) /\
    (wv_tagc (y_t X) = 5 -> keys = 0) /\
    (wv_tagc (y_t X) = 6 ->
       In (keys, 8 * cap) (y_D X) /\
       exists x k, In (x, k) (y_D X) /\ rd_u64 SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) x /\
         pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) x k (wvi_key X i)).
Proof.
intros X ch fxc P lyc Sc Hpc Wc memc mdc kc i HSTK Hpre Hcom Hi.
destruct (wvi_node_cur X ch fxc P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom) as (HNODE & _ & _).
unfold wv_nitems, wvi_child, wvi_key, wv_tagc in *.
destruct (y_t X) as [| | | txt bits | s | l | l]; try (cbn in Hi; lia).
- destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
  destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
  destruct Hbody as (_ & Hkeys0 & Hn & Hncap & Hcb & Di & HDi & Hitems).
  destruct Hcb as [(Hc0 & _) | (Hcp & _)]; [lia|].
  destruct (wvi_items_nth _ l kids Di i Hitems Hi) as (D1 & Dp & Dq & EDi & HN1).
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
  destruct (wvi_mems_nth _ _ _ l kids keys Di i Hmems Hi) as (x & k & D1 & Dp & Dq & EDi & Hx & Hcs & HN1).
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

(* ---- copied from WriteValueB_Leaf (its Section has the strlen premise this walk does not take): a ledger block's
   granule bound by AR_laws_x's alx_blocks_ceil8, a key string as a C string, two ledger blocks apart ---- *)
Lemma wvi_hull_sub : forall rd x n x' n',
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

Lemma wvi_blk_ceil7 : forall ly S Hp W mem md Lam peak cnt fail ran gmo gow a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran gmo gow -> In (a, k) Lam ->
  a + k + 7 <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran gmo gow a k HAR HLED Hin.
pose proof cf_head_nonneg as Hh0.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). cbn [fst snd] in Hk0, Hbl.
pose proof (alx_blocks_ceil8 SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl) as Hc.
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
clear - Hc Hrq. lia.
Qed.

Lemma wvi_cstr_blk : forall ly S Hp W0 mem0 md0 Lam peak cnt fail ran gmo gow (W : world SEGS) m str k s,
  ARx ly S Hp W0 mem0 md0 -> prh_ledger B ly S Hp W0 mem0 Lam peak cnt fail ran gmo gow ->
  In (str, k) Lam -> Z.of_nat (length s) + 1 <= k -> Z.of_nat (length s) + 1 < 2 ^ 32 ->
  Forall (fun c => 0 < c < 256) s -> garr8 SEGS (mrestrict (w_H W) m) str (s ++ [0]) ->
  str + k + 7 <= YM05.alloc_ceiling ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF str k ->
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W) m) str k) ->
  (forall x, str <= x < (str + k + 7) / 8 * 8 -> aview SEGS (w_H W) m x <> None) ->
  cstr_ok W m str s.
Proof.
intros ly S Hp W0 mem0 md0 Lam peak cnt fail ran gmo gow W m str k s HAR HLED Hin Hlen Hlen32 Hrng Hg Hgap HRA HHULL HVIS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0. pose proof HW as HW8. unfold prh_head_wide in HW8.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
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
split; [apply (wvi_hull_sub _ str k str (n + 1) (HHULL ltac:(lia))); lia |].
intros x Hx. apply HVIS.
assert (Hn0 : 0 <= n) by (subst n; lia). clearbody n.
pose proof (Z.div_mod (str + n) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (str + n) 8 ltac:(lia)) as D1b.
assert (D3 : (str + n) / 8 + 1 <= (str + k + 7) / 8).
{ replace ((str + n) / 8 + 1) with ((str + n + 1 * 8) / 8) by (rewrite Z.div_add by lia; reflexivity).
  apply Z.div_le_mono; lia. }
clear - Hx D1 D1b D3 Hn0 Hlen. lia.
Qed.

Lemma wvi_blk_apart : forall ly S Hp W mem md Lam peak cnt fail ran gmo gow a k buf cap n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran gmo gow ->
  In (a, k) Lam -> a <> buf -> (cap <> 0 -> In (buf, cap) Lam) -> 0 <= n -> n <= k ->
  cap = 0 \/ a + n <= buf \/ buf + cap <= a.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran gmo gow a k buf cap n HAR HLED Hin Hab Hbuf Hn Hnk.
destruct (Z.eq_dec cap 0) as [->|Hc0]; [left; reflexivity|]. right.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). pose proof (HF (buf, cap) (Hbuf Hc0)) as (Hc00 & Hblb & _).
cbn [fst snd] in Hk0, Hbl, Hc00, Hblb.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl)
  as (_ & _ & _ & _ & _ & Hpw).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
assert (Hrqb : cap + cf_head <= req_size (cap + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); lia).
pose proof cf_head_nonneg as Hh0.
destruct (wv_pairwise_in2 _ zdisjoint _ (a - cf_head, req_size (k + cf_head))
    (buf - cf_head, req_size (cap + cf_head)) Hpw
    (in_map (fun b => (fst b, req_size (snd b))) _ _ Hbl)
    (in_map (fun b => (fst b, req_size (snd b))) _ _ Hblb)
    ltac:(intros E; injection E as E1 _; lia)) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* ---- THE FOUR INNER CALL SITES, at this Section's float state: from the join at the call memory (P), the call's
   argument registers and its return address, and the continuation at the return site (the join at P ++ the callee's
   pieces): put and indent keep the float state, put_string and write_value end at their exit float state fx2 ---- *)
Lemma wvi_site_put : forall n' X ch i P P3 slot bs ret lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wvi_st X fx i P lyc Sc Hpc Wc regs memc mdc kc ->
  In (slot, bs) wv_lits ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ [bs] ++ P3 ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 (WV_STR slot) -> getr regs 12 = w64 (Z.of_nat (length bs)) ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, wvi_st X fx i (P ++ [bs]) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (@mkst fx regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin B ARx Pm X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc) (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i P P3 slot bs ret lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hlit Hpcs H10 H11 H12 Hra Hrok
  Hra4 Hrac HK.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
destruct (wvi_ctx n' X ch fx i P [bs] P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hcons2 &
   Hos & Hroom & HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax &
   Hlive & Hfp & Hbufin & Hcap0 & Hcl & Hhead & Hfr0 & Hfrm).
pose proof (proj1 HJc) as HARc.
destruct (HLIT slot bs lyc Sc Hpc Wc memc mdc Hlit HARc HROc) as (Hsrc & Hkept & Himg).
assert (Hlen0 : 0 < Z.of_nat (length bs))
  by (unfold wv_lits in Hlit; cbn [In] in Hlit;
      repeat (destruct Hlit as [Hl | Hlit]; [injection Hl as <- <-; cbn; lia |]); destruct Hlit).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; wvi_zl).
assert (Hhome : prhWriter_src_home B lyc Sc Lamc bufc (WriterApp.w_cap (prhWriter_putN ok (y_st X) P)) (WV_STR slot)
    (Z.of_nat (length bs)))
  by (apply (wv_lit_home lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (y_most X) (y_own X) bufc _ (WV_STR slot)
        (Z.of_nat (length bs)) HARc HLED Hbufin Hcap0 Hlen0 Hkept);
      intros a Ha; replace a with (WV_STR slot + (a - WV_STR slot)) by lia; apply Himg; lia).
assert (Hwmax' : Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok (y_st X) P))) + Z.of_nat (length bs) + 1
    <= prhWriter_WMAX) by (cbn [concat] in Hwmax; rewrite app_nil_r in Hwmax; exact Hwmax).
eapply (SRr'_bind SEGS RZ_cf).
{ exact (wv_call_put (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X) (y_FP X)
    (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs (Z_to_bv 64 (BASE + ret))
    ra1 nfp1 (y_o X) (WV_STR slot) (Z.of_nat (length bs)) bufc (prhWriter_putN ok (y_st X) P) bs Lamc peakc ranc
    (y_most X) (y_own X) (- (y_d X + 192)) Hfrm HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok
    ltac:(rewrite HB64; lia) ltac:(rewrite HB64; exact Hrac) Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp Hos Hcons2 Hcl H10
    H11 H12 Ho1 Ho2 HOUT HLED Hsrc eq_refl Hhome
    (wv_ev_first (y_rpsm X) (y_rpx X) (y_rpos X) rpi (prhWriter_putN ok (y_st X) P) bs [] Hev2)
    Hwmax' Hhead Hlive Hfp). }
cbv beta. intros W2 c2 _ (ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HKC & HAP &
  (Hroom2 & HPP & HRET) & HMN).
rewrite Hrpi in HPP.
apply (HK ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvi_after X ch fx fx i P [bs] lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc peakc ly2 S2' Hp2 W2 regs2 mem2
  md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 192))
  (y_sp X + y_d X + - (y_d X + 192) + - - (y_d X + 192)) ltac:(lia) Hpre Hst Hoks HOUT HLED HBLK HJ2 ltac:(lia)
  ltac:(lia) HKC HAP Hroom2
  (wv_ret_pos_one (y_rpsm X) (y_rpx X) (y_rpos X) (y_rpH0 X) _ rph lyc Sc Hpc Wc memc Lamc peakc ranc (y_most X)
     (y_own X) (y_o X) bufc (prhWriter_putN ok (y_st X) P) bs ly2 S2' Hp2 W2 regs2 mem2 md2 HOUT HLED HPP HRET) HMN
  Hfrm (wvi_fk_refl fx)).
Qed.

Lemma wvi_site_indent : forall n' X ch i P P3 depth ret lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wvi_st X fx i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ WriterValue.wind (y_p X) depth ++ P3 ->
  - 2 ^ 31 <= depth < 2 ^ 31 ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 (y_pretty X) -> getr regs 12 = w64 depth ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     wvi_st X fx i (P ++ WriterValue.wind (y_p X) depth) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (@mkst fx regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin B ARx Pm X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (SIGMA AS_indent)) memc (seg_rom SEGS)) mdc) (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i P P3 depth ret lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs Hdepth H10 H11 H12 Hra Hrok
  Hra4 Hrac HK.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
destruct (wvi_ctx n' X ch fx i P (WriterValue.wind (y_p X) depth) P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst
  Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hcons2 &
   Hos & Hroom & HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax &
   Hlive & Hfp & Hbufin & Hcap0 & Hcl & Hhead & Hfr0 & Hfrm).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; wvi_zl).
eapply (SRr'_bind SEGS RZ_cf).
{ exact (wv_call_indent (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs
    (Z_to_bv 64 (BASE + ret)) ra1 nfp1 (y_o X) (y_pretty X) depth bufc (prhWriter_putN ok (y_st X) P) Lamc peakc
    ranc (y_most X) (y_own X) (- (y_d X + 192)) Hfrm HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok
    ltac:(rewrite HB64; lia) ltac:(rewrite HB64; exact Hrac) Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp Hos Hcons2 Hcl H10
    H11 H12 Hpr Hdepth Ho1 Ho2 HOUT HLED Hev2 Hwmax Hhead Hlive Hfp). }
cbv beta. intros W2 c2 _ (ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HKC & HAP &
  (Hroom2 & HRP) & HMN).
rewrite Hrpi in HRP.
apply (HK ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvi_after X ch fx fx i P (WriterValue.wind (y_p X) depth) lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc
  peakc ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 192))
  (y_sp X + y_d X + - (y_d X + 192) + - - (y_d X + 192)) ltac:(lia) Hpre Hst Hoks HOUT HLED HBLK HJ2 ltac:(lia)
  ltac:(lia) HKC HAP Hroom2 HRP HMN Hfrm (wvi_fk_refl fx)).
Qed.

(* an object's key i: put_string from the join at P; the key string is a tree block (x, k) of D at the call memory *)
Lemma wvi_site_put_string : forall n' X ch i P P3 x k ret lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wvi_st X fx i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ WriterSpec.spieces (wvi_key X i) ++ P3 ->
  In (x, k) (y_D X) ->
  pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) x k (wvi_key X i) ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 x ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall (fx2 : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     wvi_st X fx2 i (P ++ WriterSpec.spieces (wvi_key X i)) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin B ARx Pm X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i P P3 x k ret lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst Hpcs HxD Hcs H10 H11 Hra Hrok
  Hra4 Hrac HK.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_node_cur X ch fx P lyc Sc Hpc Wc memc mdc kc HSTK Hpre (proj1 Hst)) as (_ & HTVc & _).
destruct (wvi_ctx n' X ch fx i P (WriterSpec.spieces (wvi_key X i)) P3 lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hst
  Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hcons2 &
   Hos & Hroom & HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax &
   Hlive & Hfp & Hbufin & Hcap0 & Hcl & Hhead & Hfr0 & Hfrm).
pose proof (proj1 HJc) as HARc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _ & _ & _ & _ & _ &
  HD & _).
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; wvi_zl).
destruct Hcs as (Hlam & Hlen & Hlen32 & Hrng & Hgs). unfold prh_lin in Hlam.
destruct (HD x k HxD) as (HinL & Hxb).
destruct (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ _ _ HLED) HBLK x k HinL Hxb)
  as (HinLc & Hxbc).
destruct (HTVc x k HxD) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (wvi_cstr_blk (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) (y_Lam X) (y_peak X) _ _ (y_ran X)
  (y_most X) (y_own X) Wc memc x k (wvi_key X i) HAR0 HLED0 HinL Hlen Hlen32 Hrng Hgs
  (wvi_blk_ceil7 _ _ _ _ _ _ _ _ _ _ _ _ _ x k HAR0 HLED0 HinL) T5 T6 T7) as Hcstr.
assert (Hkept : kept_at B Lamc x (Z.of_nat (length (wvi_key X i)) + 1))
  by (left; exists x, k; split; [exact HinLc | lia]).
assert (Hapart : WriterApp.w_cap (prhWriter_putN ok (y_st X) P) = 0 \/
    x + Z.of_nat (length (wvi_key X i)) + 1 <= bufc \/ bufc + WriterApp.w_cap (prhWriter_putN ok (y_st X) P) <= x).
{ destruct (wvi_blk_apart lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (y_most X) (y_own X) x k bufc
    (WriterApp.w_cap (prhWriter_putN ok (y_st X) P)) (Z.of_nat (length (wvi_key X i)) + 1) HARc HLED HinLc Hxbc
    Hbufin ltac:(lia) ltac:(lia)) as [H|[H|H]]; [left; exact H | right; left; lia | right; right; exact H]. }
eapply (SRr'_bind SEGS RZ_cf).
{ exact (wv_call_put_string (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs
    (Z_to_bv 64 (BASE + ret)) ra1 nfp1 (y_o X) x bufc (prhWriter_putN ok (y_st X) P) (wvi_key X i) Lamc peakc ranc
    (y_most X) (y_own X) (- (y_d X + 192)) Hfrm HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok
    ltac:(rewrite HB64; lia) ltac:(rewrite HB64; exact Hrac) Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp Hos Hcl Hcons2 H10
    H11 Ho1 Ho2 HOUT HLED Hcstr Hkept Hev2 Hapart Hfr0 Hwmax Hhead Hlive Hfp). }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & Hz2 & Hk2 & HJ2 & _ & HKC & HAP &
  (Hroom2 & HRP) & HMN).
rewrite Hrpi in HRP.
apply (HK fx2 ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvi_after X ch fx fx2 i P (WriterSpec.spieces (wvi_key X i)) lyc Sc Hpc Wc regs memc mdc kc ok ranc bufc Lamc
  peakc ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 192))
  (y_sp X + y_d X + - (y_d X + 192) + - - (y_d X + 192)) ltac:(lia) Hpre Hst Hoks HOUT HLED HBLK HJ2 ltac:(lia)
  ltac:(lia) HKC HAP Hroom2 HRP HMN Hz2 Hk2).
Qed.

(* the item's value: the recursive call at depth n' (the text at this Section's float state), from the join at P;
   the child node v2 is in a tree block, its blocks among the container's *)
Lemma wvi_site_self : forall n' X ch i P P3 v2 t2 D2 ret lyc Sc Hpc Wc regs memc mdc kc,
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre B ARx CTX0 Pm X ch -> wvi_st X fx i P lyc Sc Hpc Wc regs memc mdc kc ->
  WriterValue.wvpieces (y_t X) (y_p X) (y_dep X) = P ++ WriterValue.wvpieces t2 (y_p X) (y_dep X + 1) ++ P3 ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin (y_Lam X)) v2 t2 D2 ->
  (PjTree.depth t2 < PjTree.depth (y_t X))%nat ->
  (forall b, In b D2 -> In b (y_D X)) ->
  (exists x y, In (x, y) (y_D X) /\ x <= v2 /\ v2 + 56 <= x + y) ->
  getr regs 10 = w64 (y_o X) -> getr regs 11 = w64 v2 -> getr regs 12 = w64 (y_pretty X) ->
  getr regs 13 = w64 (y_dep X + 1) ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> YK0s.ret_ok (Z_to_bv 64 (BASE + ret)) ->
  4096 <= BASE + ret -> BASE + ret < YM05.alloc_ceiling ->
  (forall (fx2 : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     wvi_st X fx2 i (P ++ WriterValue.wvpieces t2 (y_p X) (y_dep X + 1)) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2)
       (wv_Qfin B ARx Pm X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (SIGMA AS_write_value)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i P P3 v2 t2 D2 ret lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hst Hpcs HN2 Hdt2 HD2 Hv2 H10
  H11 H12 H13 Hra Hrok Hra4 Hrac HK.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_node_cur X ch fx P lyc Sc Hpc Wc memc mdc kc HSTK Hpre (proj1 Hst)) as (_ & HTVc & _).
destruct (wvi_ctx n' X ch fx i P (WriterValue.wvpieces t2 (y_p X) (y_dep X + 1)) P3 lyc Sc Hpc Wc regs memc mdc kc
  HSTKn Hpre Hst Hpcs) as
  (ok & ranc & bufc & Lamc & peakc & rpi & rph & ra1 & nfp1 & Hoks & HOUT & HLED & HBLK & Hrpi & Hrp & Hev2 & Hcons2 &
   Hos & Hroom & HROc & HJc & Hra1 & Hnfp1 & Hnfpc & Hsp & Hoc16 & Hoc0 & Hhi & Hgp & Htp & Hs0 & Ho1 & Ho2 & Hwmax &
   Hlive & Hfp & Hbufin & Hcap0 & Hcl & Hhead & Hfr0 & Hfrm).
pose proof (proj1 HJc) as HARc.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & Hdd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HD & Hoff & _).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & _).
assert (HB64 : bv_unsigned (Z_to_bv 64 (BASE + ret)) = BASE + ret) by (apply unsigned_lit_small; wvi_zl).
assert (HLK : forall a k0, In (a, k0) (y_D X) -> In (a, k0) Lamc /\ a <> bufc).
{ intros a k0 Hin. destruct (HD a k0 Hin) as (HinL & Hab).
  exact (wv_lam_keep _ _ _ _ _ _ _ _ _ _ _ _ (wv_led_nodup _ _ _ _ _ _ _ _ _ _ _ _ HLED) HBLK a k0 HinL Hab). }
destruct Hv2 as (xb & yb & Hxb & Hxv & Hvy).
destruct (HTVc xb yb Hxb) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Hdep0 : (0 < PjTree.depth (y_t X))%nat) by lia.
eapply (SRr'_bind SEGS RZ_cf).
{ apply (wv_call_self n' (y_rpsm X) (y_rpx X) (y_rpos X) rpi (y_rpH0 X) rph (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc memc mdc kc regs
    (Z_to_bv 64 (BASE + ret)) ra1 nfp1 (y_o X) v2 (y_pretty X) (y_dep X + 1) bufc (prhWriter_putN ok (y_st X) P) t2
    D2 Lamc peakc ranc (y_most X) (y_own X) (- (y_d X + 192)) IH Hfrm HJc Hsp Hoc16 Hoc0 ltac:(lia) Hgp Htp Hra Hrok
    ltac:(rewrite HB64; lia) ltac:(rewrite HB64; exact Hrac) Hs0 Hra1 Hnfp1 Hnfpc HROc Hhi Hroom Hrp Hos Hcons2 Hcl H10
    H11 H12 H13 Hpr ltac:(lia) ltac:(lia) ltac:(lia) Ho1 Ho2 HOUT HLED Hev2
    (wvi_nodeR_lblk t2 _ _ _ v2 D2 HN2 (fun a k0 Hin _ => proj1 (HLK a k0 (HD2 _ Hin))))).
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
  - exact Hlive.
  - exact Hfp. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2' & Hp2 & regs2 & mem2 & md2 & k1 & -> & Hz2 & Hk2 & HJ2 & _ & HKC & HAP &
  (Hroom2 & _ & HRP) & HMN).
rewrite Hrpi in HRP.
apply (HK fx2 ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1)).
exact (wvi_after X ch fx fx2 i P (WriterValue.wvpieces t2 (y_p X) (y_dep X + 1)) lyc Sc Hpc Wc regs memc mdc kc ok
  ranc bufc Lamc peakc ly2 S2' Hp2 W2 regs2 mem2 md2 (kc + k1) (y_sp X + y_d X + - (y_d X + 192))
  (y_sp X + y_d X + - (y_d X + 192) + - - (y_d X + 192)) ltac:(lia) Hpre Hst Hoks HOUT HLED HBLK HJ2 ltac:(lia)
  ltac:(lia) HKC HAP Hroom2 HRP HMN Hz2 Hk2).
Qed.

(* ---- the seated env's extra atoms ---- *)
Lemma wvi_E_at : forall X i regs kids keys nn kp,
  ew (wvi_E X i regs kids keys nn kp) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (wvi_E X i regs kids keys nn kp) 33 = Z_to_bv 64 (y_dep X) /\
  ew (wvi_E X i regs kids keys nn kp) 34 = Z_to_bv 64 (WV_STR (wv_sep_slot X)) /\
  ew (wvi_E X i regs kids keys nn kp) 35 = Z_to_bv 64 (WV_STR 88) /\
  ew (wvi_E X i regs kids keys nn kp) 36 = Z_to_bv 64 kids /\
  ew (wvi_E X i regs kids keys nn kp) 37 = Z_to_bv 64 keys /\
  ew (wvi_E X i regs kids keys nn kp) 38 = Z_to_bv 64 nn /\
  ew (wvi_E X i regs kids keys nn kp) 39 = Z_to_bv 64 (keys + 8 * Z.of_nat i) /\
  ew (wvi_E X i regs kids keys nn kp) 40 = Z_to_bv 64 kp /\
  ew (wvi_E X i regs kids keys nn kp) 41 = Z_to_bv 64 (kids + 56 * Z.of_nat i).
Proof.
intros X i regs kids keys nn kp. unfold wvi_E, wvi_EH.
repeat split; (rewrite Eimg_low by (unfold A_TEXT; lia)); first
  [ exact (ew_Ereg_extra _ _ 0) | exact (ew_Ereg_extra _ _ 1) | exact (ew_Ereg_extra _ _ 2)
  | exact (ew_Ereg_extra _ _ 3) | exact (ew_Ereg_extra _ _ 4) | exact (ew_Ereg_extra _ _ 5)
  | exact (ew_Ereg_extra _ _ 6) | exact (ew_Ereg_extra _ _ 7) | exact (ew_Ereg_extra _ _ 8)
  | exact (ew_Ereg_extra _ _ 9) ].
Qed.

(* ---- reading a register off a stop of a run from a seat: a seated register moved, an atom of the seat's env, a
   literal, the code pointer (the return address), a literal's address ---- *)
Lemma wvi_reg_mv : forall E E' srs regs0 (regs' : bvmap 5 word) (r r0 : bv 5),
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> regs_ok E wvi_regs regs0 -> env_agree 55 E E' ->
  sv_eqb (sr_get srs r) (sr_get wvi_regs r0) = true -> getr regs' r = getr regs0 r0.
Proof.
intros E E' srs regs0 regs' r r0 HRG HR HA Hq. apply sv_eqb_eq in Hq.
rewrite HRG, Hq, (HR r0). apply (sv_denot_agree 55 E E'); [exact HA|].
pose proof wvi_regs_atoms as Ha. rewrite forallb_forall in Ha. apply Ha. apply all_regs_in.
Qed.

Lemma wvi_reg_sv : forall E E' srs (regs' : bvmap 5 word) (r : bv 5) (n : nat) w,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> env_agree 55 E E' ->
  sr_get srs r = SOff n 0 -> (n < 55)%nat -> ew E n = w -> getr regs' r = w.
Proof.
intros E E' srs regs' r n w HRG [HA _] Hr Hn Hw. rewrite HRG, Hr. cbn [sv_denot].
rewrite (HA n Hn), Hw, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma wvi_reg_lit : forall E' srs (regs' : bvmap 5 word) (r : bv 5) c,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> sr_get srs r = SLit c -> getr regs' r = Z_to_bv 64 c.
Proof. intros E' srs regs' r c HRG Hr. rewrite HRG, Hr. reflexivity. Qed.

Lemma wvi_reg_ret : forall E' srs (regs' : bvmap 5 word) k,
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) -> img_env VAL A_LIM E' ->
  sr_get srs 1 = SOff A_TEXT (WVI_PC k) -> getr regs' 1 = Z_to_bv 64 (BASE + WVI_PC k).
Proof. intros E' srs regs' k HRG HE Hr. rewrite HRG, Hr. exact (codeptr_val E' (WVI_PC k) HE). Qed.

(* a seated register read through the seat's env *)
Lemma wvi_ew_reg : forall E regs (r : bv 5) (n : nat), regs_ok E wvi_regs regs ->
  sr_get wvi_regs r = SOff n 0 -> ew E n = getr regs r.
Proof.
intros E regs r n HR Hs. pose proof (HR r) as H. rewrite Hs in H. cbn [sv_denot] in H.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. symmetry. exact H.
Qed.

(* ---- a join survives a run from its seat that stops (at a call or a branch) with the seated callee-saved registers
   (the seat has no write window, so the run kept every byte; the journal and Pm are the runner's) ---- *)
Lemma wvi_st_run : forall X fxc i P lyc Sc Hpc Wc regs memc mdc kc E E' srs (regs' : bvmap 5 word) mem' md',
  wvi_st X fxc i P lyc Sc Hpc Wc regs memc mdc kc -> 0 <= y_o X -> y_o X + 32 <= 2 ^ 64 ->
  regs_ok E wvi_regs regs -> env_agree 55 E E' ->
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get wvi_regs r)) CALLEE_SAVED = true ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (y_STK X + y_d X) (y_sp X + y_d X)
    (y_FP X) (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_mem X) (y_md X) [] lyc Sc Hpc Wc mem' md' kc ->
  Pm mem' ->
  (forall a, aview SEGS (w_H Wc) mem' a = aview SEGS (w_H Wc) memc a) ->
  wvi_st X fxc i P lyc Sc Hpc Wc regs' mem' md' kc.
Proof.
intros X fxc i P lyc Sc Hpc Wc regs memc mdc kc E E' srs regs' mem' md' (Hcom & Hrf) Ho0 Ho64 HR HA HRG Hcs
  HJ HPm HK.
split.
- exact (wvi_common_run X fxc P lyc Sc Hpc Wc memc mdc kc mem' md' Hcom Ho0 Ho64 HJ HPm HK).
- apply (wvi_rf_keep X i Wc Wc regs regs' memc mem' Hrf (wvi_aregs E E' srs regs regs' HRG HR HA Hcs)).
  intros a _. apply HK.
Qed.

(* ---- the node's fields at a join's memory (any item counter, the container non-empty) ---- *)
Lemma wvi_node_facts : forall X ch fxc P lyc Sc Hpc Wc memc mdc kc,
  192 <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_commonR B ARx Pm (wle' SEGS RZ_cf) X fxc P lyc Sc Hpc Wc memc mdc kc ->
  (0 < wv_nitems (y_t X))%nat ->
  exists kids keys nn cap,
    val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 (wv_tagc (y_t X)) /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) kids /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) keys /\
    rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) nn /\
    nn = Z.of_nat (wv_nitems (y_t X)) /\ nn <= cap /\ 0 < cap /\ In (kids, 56 * cap) (y_D X) /\
    (wv_tagc (y_t X) = 5 -> keys = 0) /\ (wv_tagc (y_t X) = 6 -> In (keys, 8 * cap) (y_D X)).
Proof.
intros X ch fxc P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom Hn.
destruct (wvi_item_facts X ch fxc P lyc Sc Hpc Wc memc mdc kc 0 HSTK Hpre Hcom Hn) as
  (kids & keys & nn & cap & D1 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & _ & _ & V9 & V10).
exists kids, keys, nn, cap. repeat (split; [assumption|]). intros H. exact (proj1 (V10 H)).
Qed.

(* a tree block's facts: user base 16-aligned, at least 4096, below the ceiling, off the shadow band *)
Lemma wvi_blk_facts : forall X ch a k,
  192 <= y_STK X -> wv_pre B ARx CTX0 Pm X ch -> In (a, k) (y_D X) ->
  a mod 16 = 0 /\ 4096 <= a /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\
  (a + k <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a).
Proof.
intros X ch a k HSTK Hpre Hin.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _ & _ & _ & _ & _ &
  HD & _).
destruct (HD a k Hin) as (HinL & _).
pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED0 (a, k) HinL) as (Hk0 & Hbl & _ & Ha16 & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR0 Hbl) as (Hp16 & Hp4096 & Hpc & Hpapp & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
split; [exact Ha16|]. split; [lia|]. split; [lia|]. split; [lia|].
change (2 ^ 44) with 17592186044416. unfold SHADOW_OFF. lia.
Qed.

(* ---- THE SEAT AT A JOIN: the seated state at pc, from wv_pre, the join at counter i (i < n; with the key slot,
   kr = true, an object) and the node's field values at the join's memory ---- *)
Lemma wvi_seat_join : forall n' X ch i P lyc Sc Hpc Wc regs memc mdc kc pc (kr : bool)
    kids keys nn cap kp,
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wvi_st X fx i P lyc Sc Hpc Wc regs memc mdc kc ->
  (i < wv_nitems (y_t X))%nat ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (y_v X) 4 (wv_tagc (y_t X)) ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 24) kids ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 32) keys ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (y_v X + 40) nn ->
  nn = Z.of_nat (wv_nitems (y_t X)) -> nn <= cap -> 0 < cap -> In (kids, 56 * cap) (y_D X) ->
  (wv_tagc (y_t X) = 5 -> keys = 0) -> (wv_tagc (y_t X) = 6 -> In (keys, 8 * cap) (y_D X)) ->
  (kr = true -> wv_tagc (y_t X) = 6 /\ rd_u64 SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) kp) ->
  img_env VAL A_LIM (wvi_E X i regs kids keys nn kp) /\ regs_ok (wvi_E X i regs kids keys nn kp) wvi_regs regs /\
  st_ok_pi SEGS VAL (wvi_E X i regs kids keys nn kp) (wvi_ss pc (wv_tagc (y_t X)) kr)
    (restrict (w_H Wc) (@mkst fx regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS WV_Bx (wvi_SH kr) (wvi_E X i regs kids keys nn kp) (mrestrict (w_H Wc) memc).
Proof.
intros n' X ch i P lyc Sc Hpc Wc regs memc mdc kc pc kr kids keys nn cap kp HSTKn Hpre Hst Hi Vtg (Rkids & Vkids)
  (Rkeys & Vkeys) (Rnn & Vnn) Hnn Hncap Hcap Hkb Hk5 Hk6 Hkr.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof Hpre as ((HPREx & _) & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & _ & _ & _ & _ & _ & _ & _ & HOUT0 & HLED0 &
  _ & HNODE0 & HLOC & _).
destruct (wv_loc (y_ly X) (y_S X) (y_Hp X) (y_W X) (y_regs X) (y_mem X) (y_md X) ch (y_STK X) (y_Lam X) (y_peak X)
  _ _ (y_ran X) (y_most X) (y_own X) (y_buf X) (y_v X) HSTK HPREx HLED0 HLOC) as (Hv4096 & Hv47 & Hvsp & Hband & Hvimg).
assert (Hv8 : y_v X mod 8 = 0)
  by (clear - HNODE0; destruct (y_t X); destruct HNODE0 as (_ & _ & _ & _ & _ & _ & _ & _ & ((Hv8 & _) & _) & _);
      exact Hv8).
pose proof Hst as (Hcom & Hrf).
destruct (wvi_node_cur X ch fx P lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom) as (HNODEc & HTVc & HRAc).
assert (HAPc : pj_apartR (y_D X) (y_v X)) by (clear - HNODEc; destruct (y_t X); exact (proj1 (proj2 HNODEc))).
destruct Hcom as (HJc & _ & _ & _ & _ & HROc & _).
pose proof (proj1 HJc) as HARc.
pose proof (@alloc_ceiling_value rc) as HCV. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HCL.
destruct (wvi_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (Hk16 & Hk4096 & _ & Hkc & _).
assert (HSTR : forall slot bs, In (slot, bs) wv_lits -> 0 <= WV_STR slot < 2 ^ 64).
{ intros slot bs Hl. destruct (HLIT slot bs lyc Sc Hpc Wc memc mdc Hl HARc HROc) as (_ & _ & Himg).
  assert (Hlen0 : 0 < Z.of_nat (length bs))
    by (unfold wv_lits in Hl; cbn [In] in Hl;
        repeat (destruct Hl as [Hl' | Hl]; [injection Hl' as <- <-; cbn; lia |]); destruct Hl).
  pose proof (pa_segs_low _ (Himg 0 ltac:(lia))) as Hlow. rewrite Z.add_0_r in Hlow.
  unfold kLowMemEnd in Hlow. split; [lia|]. change (2 ^ 64) with 18446744073709551616. lia. }
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
assert (Hk8 : kids mod 8 = 0).
{ apply Z.mod_divide in Hk16 as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (2 * q). lia. }
assert (Hkeysb : 0 <= keys < 2 ^ 64).
{ destruct Htg as [H5 | H6].
  - rewrite (Hk5 H5). wvi_zl.
  - destruct (wvi_blk_facts X ch keys (8 * cap) HSTK Hpre (Hk6 H6)) as (_ & ? & _ & ? & _). wvi_zl. }
assert (Hkey6 : wv_tagc (y_t X) = 6 -> keys mod 8 = 0 /\ 4096 <= keys /\ keys + 8 * Z.of_nat i + 8 <= 2 ^ 47).
{ intros H6. destruct (wvi_blk_facts X ch keys (8 * cap) HSTK Hpre (Hk6 H6)) as (Hq16 & Hq4096 & _ & Hqc & _).
  split; [apply Z.mod_divide in Hq16 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (2 * q); lia|].
  split; [lia | wvi_zl]. }
assert (HkrF : kr = true -> wv_tagc (y_t X) = 6 /\ 0 <= kp < 2 ^ 64 /\
     val_mem SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) 8 kp /\
     keys + 8 * Z.of_nat i + 8 <= YM05.alloc_ceiling /\
     (keys + 8 * Z.of_nat i + 8 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= keys + 8 * Z.of_nat i) /\
     range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 /\
     (keys + 8 * Z.of_nat i + 8 <= y_v X \/ y_v X + 56 <= keys + 8 * Z.of_nat i)).
{ intros Hkt. destruct (Hkr Hkt) as (Ht6 & (Rkp & Vkp)).
  pose proof (Hk6 Ht6) as HkbK.
  destruct (wvi_blk_facts X ch keys (8 * cap) HSTK Hpre HkbK) as (Hk16' & Hk4096' & _ & Hkc' & Hkband').
  assert (Hi8' : 8 * Z.of_nat i + 8 <= 8 * cap) by lia.
  split; [exact Ht6|]. split; [exact Rkp|]. split; [exact Vkp|].
  split; [lia|].
  split; [change (2 ^ 44) with 17592186044416 in *; unfold SHADOW_OFF in *; lia|].
  split.
  - destruct (HTVc keys (8 * cap) HkbK) as (_ & _ & _ & _ & T5 & _).
    apply (wv_ra_sub _ keys (8 * cap)); [exact T5 | lia | lia].
  - destruct (Z_le_gt_dec (keys + 8 * Z.of_nat i + 8) (y_v X)) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec (y_v X + 56) (keys + 8 * Z.of_nat i)) as [Hr|Hr]; [right; exact Hr|].
    exfalso. set (z := Z.max (y_v X) (keys + 8 * Z.of_nat i)).
    apply (HAPc (keys, 8 * cap) z HkbK); [unfold pj_holdsR; cbn [fst snd]; lia | lia]. }
exact (wvi_seat X i Wc regs memc pc (wv_tagc (y_t X)) kr kids keys nn kp Htg Hrf Hpr Hdep Hsp16
  ltac:(unfold y_sp in *; lia) Hv8 Hv4096 Hv47 ltac:(unfold y_sp in *; exact Hvsp) Hband HRAc Vtg Vkids
  Hk8 Hk4096 ltac:(wvi_zl) Vkeys Hkeysb Hkey6 Vnn ltac:(wvi_zl) ltac:(wvi_zl)
  (HSTR _ _ (wvi_sep_lit X)) (HSTR 88%nat [44] wvi_comma_lit) HkrF).
Qed.

(* ---- the back edge's increments (s5 += 1, s9 += 8, s7 += 56): the join's registers at counter i + 1 ---- *)
Lemma wvi_rf_next : forall X i (W : world SEGS) regs mem E E' srs (regs' : bvmap 5 word) mem',
  wvi_rf X i W regs mem -> regs_ok E wvi_regs regs -> env_agree 55 E E' ->
  (forall r, getr regs' r = sv_denot E' (sr_get srs r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get srs r) (sr_get wvi_regs r))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 26; 27]%bv = true ->
  sr_get srs 21%bv = SOff 21 1 -> sr_get srs 25%bv = SOff 25 8 -> sr_get srs 23%bv = SOff 23 56 ->
  56 * Z.of_nat (S i) < 2 ^ 64 ->
  (forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  wvi_rf X (S i) W regs' mem'.
Proof.
intros X i W regs mem E E' srs regs' mem' HRF HR HA HRG Hcs H21 H25 H23 Hb HK.
assert (HP : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 26; 27]%bv -> getr regs' r = getr regs r)
  by (intros r Hr; apply (wvi_reg_mv E E' srs regs regs' r r HRG HR HA);
      exact (proj1 (forallb_forall _ _) Hcs r Hr)).
assert (HI : forall (r : bv 5) (n : nat) c v, sr_get srs r = SOff n c -> (n < 55)%nat ->
    sr_get wvi_regs r = SOff n 0 -> getr regs r = w64 v -> 0 <= v -> v + c < 2 ^ 64 -> 0 <= c ->
    getr regs' r = w64 (v + c)).
{ intros r n c v Hs Hn Hw Hv Hv0 Hvc Hc0. rewrite HRG, Hs. cbn [sv_denot]. destruct HA as [HAe _].
  rewrite (HAe n Hn), (wvi_ew_reg E regs r n HR Hw), Hv. unfold w64.
  rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616 in *; lia). reflexivity. }
assert (RW : forall off, rdword (aview SEGS (w_H W) mem') (y_sp X - 192 + off) =
    rdword (aview SEGS (w_H W) mem) (y_sp X - 192 + off))
  by (intros off; apply wv_rdword_ext; intros j Hj; apply HK).
unfold wvi_rf in HRF |- *. cbv beta zeta in HRF |- *.
destruct HRF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168 & F176 & F184).
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
split; [rewrite (HP 22%bv ltac:(cbn [In]; auto 20)); exact G22|].
split; [rewrite (HI 23%bv 23%nat 56 (56 * Z.of_nat i) H23 ltac:(lia) eq_refl G23) by lia; f_equal; lia|].
split; [rewrite (HP 24%bv ltac:(cbn [In]; auto 20)); exact G24|].
split; [rewrite (HI 25%bv 25%nat 8 (8 * Z.of_nat i) H25 ltac:(lia) eq_refl G25) by lia; f_equal; lia|].
split; [rewrite (HP 26%bv ltac:(cbn [In]; auto 20)); exact G26|].
split; [rewrite (HP 27%bv ltac:(cbn [In]; auto 20)); exact G27|].
repeat (split; [rewrite RW; assumption|]). rewrite RW. assumption.
Qed.

(* ---- THE BRANCHES THE ENGINE LEAVES (measured, WvbIter's probe, the internal file zfb-20261029T194028Z.log): the head's `beqz s5` (slot 90), the back edge's
   `bltu s5 + 1, n` (slot 162), and the four UBSan pointer-overflow arms it cannot decide from atom ranges, each NOT
   taken: slot 116 `bnez (i >> 60)` (i < 2 ^ 42), slot 117 `bltu keys + 8 i, keys` (no wrap), slot 144
   `bltu kids + 56 i, kids` (no wrap), slot 150 `bnez (mulh (i, 56) ^ (56 i >> 63))` (56 i < 2 ^ 63) ---- *)
Lemma wvi_br90 : forall E i, ew E 21 = Z_to_bv 64 (Z.of_nat i) -> Z.of_nat i < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff 21 0)) (sv_denot E (SLit 0)) = (Z.of_nat i =? 0).
Proof.
intros E i E21 Hi. rewrite branch_eq_U, (U_atom E 21 (Z.of_nat i) E21), U_lit by wvi_zl. reflexivity.
Qed.

Lemma wvi_br162 : forall E i nn, ew E 21 = Z_to_bv 64 (Z.of_nat i) -> ew E 38 = Z_to_bv 64 nn ->
  0 <= nn < 2 ^ 64 -> Z.of_nat i + 1 < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff 21 1)) (sv_denot E (SOff 38 0)) = (Z.of_nat i + 1 <? nn).
Proof.
intros E i nn E21 E38 Hn Hi.
rewrite branch_ltu_U, (U_atom_off E 21 (Z.of_nat i) 1 E21), (U_atom E 38 nn E38) by wvi_zl. reflexivity.
Qed.

Lemma wvi_br116 : forall E i, ew E 21 = Z_to_bv 64 (Z.of_nat i) -> Z.of_nat i <= 2 ^ 42 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SOff 21 0) (SLit 60))) (sv_denot E (SLit 0)) = false.
Proof.
intros E i E21 Hi.
assert (Hs : U E (SAlu ALU_SRL (SOff 21 0) (SLit 60)) = 0).
{ rewrite U_SAlu, (U_atom E 21 (Z.of_nat i) E21), U_lit by wvi_zl. cbn [zalu_raw].
  replace (Z.land 60 63) with 60 by reflexivity. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by wvi_zl. reflexivity. }
rewrite branch_ne_U, Hs, U_lit by wvi_zl. reflexivity.
Qed.

Lemma wvi_br117 : forall E keys i, ew E 39 = Z_to_bv 64 (keys + 8 * Z.of_nat i) -> ew E 37 = Z_to_bv 64 keys ->
  0 <= keys -> keys + 8 * Z.of_nat i < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff 39 0)) (sv_denot E (SOff 37 0)) = false.
Proof.
intros E keys i E39 E37 Hk Hk64.
rewrite branch_ltu_U, (U_atom E 39 _ E39), (U_atom E 37 _ E37) by wvi_zl. apply Z.ltb_ge. lia.
Qed.

Lemma wvi_br144 : forall E i kids, ew E 21 = Z_to_bv 64 (Z.of_nat i) -> ew E 36 = Z_to_bv 64 kids ->
  0 <= kids -> kids + 56 * Z.of_nat i < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit 56)) (SOff 36 0)))
    (sv_denot E (SOff 36 0)) = false.
Proof.
intros E i kids E21 E36 Hk0 Hk64.
assert (Hm : U E (SMd M_MUL (SOff 21 0) (SLit 56)) = 56 * Z.of_nat i).
{ rewrite U_SMd, (U_atom E 21 (Z.of_nat i) E21), U_lit by wvi_zl. cbn [zmd_raw].
  rewrite zcanon_id by (unfold M64; wvi_zl). lia. }
assert (Ha : U E (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit 56)) (SOff 36 0)) = kids + 56 * Z.of_nat i).
{ rewrite U_SAlu, Hm, (U_atom E 36 kids E36) by wvi_zl. cbn [zalu_raw].
  rewrite zcanon_id by (unfold M64; wvi_zl). lia. }
rewrite branch_ltu_U, Ha, (U_atom E 36 kids E36) by wvi_zl. apply Z.ltb_ge. lia.
Qed.

Lemma wvi_br150 : forall E i, ew E 21 = Z_to_bv 64 (Z.of_nat i) -> Z.of_nat i <= 2 ^ 42 ->
  branch_taken BC_NE
    (sv_denot E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 21 0) (SLit 56))
       (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SLit 56)) (SLit 63)))))
    (sv_denot E (SLit 0)) = false.
Proof.
intros E i E21 Hi.
assert (Ui : U E (SOff 21 0) = Z.of_nat i) by (apply U_atom; [exact E21 | wvi_zl]).
assert (Hmulh : U E (SMd M_MULH (SOff 21 0) (SLit 56)) = 0).
{ rewrite U_SMd, Ui, U_lit by wvi_zl. cbn [zmd_raw].
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); wvi_zl).
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by wvi_zl. reflexivity. }
assert (Hmul : U E (SMd M_MUL (SOff 21 0) (SLit 56)) = 56 * Z.of_nat i).
{ rewrite U_SMd, Ui, U_lit by wvi_zl. cbn [zmd_raw]. rewrite zcanon_id by (unfold M64; wvi_zl). lia. }
assert (Hsra : U E (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SLit 56)) (SLit 63)) = 0).
{ rewrite U_SAlu, Hmul, U_lit by wvi_zl. cbn [zalu_raw].
  rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); wvi_zl).
  replace (Z.land 63 63) with 63 by reflexivity. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by wvi_zl. reflexivity. }
assert (Hx : U E (SAlu ALU_XOR (SMd M_MULH (SOff 21 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SLit 56)) (SLit 63))) = 0)
  by (rewrite U_SAlu, Hmulh, Hsra; reflexivity).
assert (Hs : U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 21 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SLit 56)) (SLit 63)))) = 0)
  by (rewrite U_SAlu, Hx, U_lit by wvi_zl; reflexivity).
rewrite branch_ne_U, Hs, U_lit by wvi_zl. reflexivity.
Qed.


(* a word the memory holds is determined by its bytes' view *)
Lemma wvi_rd_u64_det : forall (H : word -> bool) (m1 m2 : word -> option byte) a v1 v2,
  (forall x, aview SEGS H m2 x = aview SEGS H m1 x) ->
  rd_u64 SEGS (mrestrict H m1) a v1 -> rd_u64 SEGS (mrestrict H m2) a v2 -> v2 = v1.
Proof.
intros H m1 m2 a v1 v2 HK (R1 & V1) (R2 & V2).
pose proof (YCem.rdword_of_val_mem SEGS H m1 a v1 V1 R1) as W1.
pose proof (YCem.rdword_of_val_mem SEGS H m2 a v2 V2 R2) as W2.
rewrite (wv_rdword_ext (aview SEGS H m1) (aview SEGS H m2) a) in W2 by (intros j _; apply HK).
rewrite W1 in W2. injection W2 as E. lia.
Qed.

(* the close's state (Defs' wv_cl) is a join after the close's pieces: its registers and frame words are the head's *)
Lemma wvi_st_cl : forall X fxc j lyc Sc Hpc Wc regsc memc mdc kc,
  wvi_st X fxc j (wv_clP X) lyc Sc Hpc Wc regsc memc mdc kc ->
  wv_clR B ARx Pm (wle' SEGS RZ_cf) X fxc lyc Sc Hpc Wc regsc memc mdc kc.
Proof.
intros X fxc j lyc Sc Hpc Wc regsc memc mdc kc (Hc & Hr).
unfold wvi_rf in Hr. cbv beta zeta in Hr.
destruct Hr as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 &
  F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 &
  F144 & F152 & F160 & F168 & F176 & F184).
unfold wv_clR. cbv beta zeta.
split; [exact Hc|]. repeat (split; [assumption|]). assumption.
Qed.

End cont.
End cl.
End h.
End f.
End d.
