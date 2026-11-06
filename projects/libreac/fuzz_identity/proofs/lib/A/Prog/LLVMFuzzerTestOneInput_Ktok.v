(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:2091-2096, for libreac/fuzz_identity's ASan build (lib/A). *)
(* The token loop of segment K (fuzz_identity.asan 0x81f00 .. 0x81fa0, listing offsets 0x17f4 .. 0x1894):
   k_token_loop_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v.

   One iteration from the head 0x81f00 (k_loop_at after j bytes of the expected name, t bytes of the token and
   d = "a '-' has been dropped"):
     0x81f00 .. 0x81f10 the shadow test of nm + j (a0) and the load of nm[j] (a6);
     0x81f14 beq a6,a4: nm[j] = '-'; then 0x81f20 beqz a3: the first '-' (d = false) is dropped (0x81f60 a3 := 1)
             and the run goes back to the head with j + 1 (0x81f54 .. 0x81f5c);
     0x81f18 beqz a6: nm[j] = 0 leaves to 0x81f84, the shadow test and the load of tk[t], and 0x81f9c bnez a0
             aborts unless tk[t] = 0; else 0x81fa0, k_mid;
     0x81f24 .. 0x81f4c the shadow test and the load of tk[t], the lower-casing of nm[j] and bne a1,a6, which
             aborts unless tk[t] = lower nm[j]; then a2, a0, a5 step and the run goes back to the head.
   The loop is proved by induction on the bytes of the name still to read (k_loop), one symbolic iteration per
   step (k_step), as IngestSegName.v's name_loop. Every symbolic run's two regions are read-only (nm[j] and
   tk[t]), so the memory after each run reads as the memory before it (k_same). The model decides every branch:
   tk holds n_TK = TOK n_EXP_NM (k_tok_split / k_tok_at, from Kcut's k_tok_app), the expected name has no zero
   byte (k_exp_nm_nz), and both buffers hold their string and its NUL inside their block (k_fits). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Klib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the model: one step of the token ---------------------------------------------------------------------- *)
Lemma k_firstn_S : forall (l : list byte) j d0, (j < length l)%nat -> firstn (S j) l = firstn j l ++ [nth j l d0].
Proof.
  induction l as [|x l IH]; intros j d0 Hj; [cbn in Hj; lia|].
  destruct j as [|j]; [reflexivity|].
  change (firstn (S (S j)) (x :: l)) with (x :: firstn (S j) l).
  change (firstn (S j) (x :: l)) with (x :: firstn j l).
  change (nth (S j) (x :: l) d0) with (nth j l d0).
  rewrite (IH j d0) by (cbn in Hj; lia). reflexivity.
Qed.

Lemma k_skipn_nth : forall (l : list byte) j d0, (j < length l)%nat -> skipn j l = nth j l d0 :: skipn (S j) l.
Proof.
  induction l as [|x l IH]; intros j d0 Hj; [cbn in Hj; lia|].
  destruct j as [|j]; [reflexivity|].
  change (skipn (S j) (x :: l)) with (skipn j l).
  change (skipn (S (S j)) (x :: l)) with (skipn (S j) l).
  change (nth (S j) (x :: l) d0) with (nth j l d0).
  apply IH. cbn in Hj. lia.
Qed.

Lemma k_has_dash_app : forall a b, SlotModel.has_dash (a ++ b) = (SlotModel.has_dash a || SlotModel.has_dash b)%bool.
Proof. intros a b. unfold SlotModel.has_dash. apply existsb_app. Qed.

Lemma k_has_dash1 : forall b, SlotModel.has_dash [b] = (RcIdentModel.bz b =? 45).
Proof. intro b. unfold SlotModel.has_dash. cbn [existsb]. apply orb_false_r. Qed.

(* The token of the whole name, split after j bytes. *)
Lemma k_tok_split : forall l j,
  SlotModel.TOK l = SlotModel.TOK (firstn j l) ++ SlotModel.tok_go (SlotModel.has_dash (firstn j l)) (skipn j l).
Proof.
  intros l j. unfold SlotModel.TOK.
  pose proof (k_tok_app (firstn j l) (skipn j l) false) as H. rewrite firstn_skipn in H. exact H.
Qed.

(* The byte the loop compares at index t: lower nm[j], unless nm[j] is the first '-'. *)
Lemma k_tok_at : forall l j b rest, skipn j l = b :: rest ->
  ~ (RcIdentModel.bz b = 45 /\ SlotModel.has_dash (firstn j l) = false) ->
  (length (SlotModel.TOK (firstn j l)) < length (SlotModel.TOK l))%nat /\
  nth (length (SlotModel.TOK (firstn j l))) (SlotModel.TOK l) (RcIdentModel.zb 0) = SlotModel.lower b.
Proof.
  intros l j b rest Hs Hn. rewrite (k_tok_split l j), Hs. cbn [SlotModel.tok_go].
  destruct (negb (SlotModel.has_dash (firstn j l)) && (RcIdentModel.bz b =? 45))%bool eqn:E.
  - exfalso. apply andb_true_iff in E as [E1 E2]. apply negb_true_iff in E1. apply Z.eqb_eq in E2. tauto.
  - split; [rewrite length_app; cbn [length]; lia|].
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma k_step_dash : forall l j, (j < length l)%nat ->
  RcIdentModel.bz (nth j l (RcIdentModel.zb 0)) = 45 -> SlotModel.has_dash (firstn j l) = false ->
  SlotModel.TOK (firstn (S j) l) = SlotModel.TOK (firstn j l) /\ SlotModel.has_dash (firstn (S j) l) = true.
Proof.
  intros l j Hj Hb Hd. rewrite (k_firstn_S l j (RcIdentModel.zb 0) Hj).
  set (b := nth j l (RcIdentModel.zb 0)) in *. split.
  - unfold SlotModel.TOK. rewrite k_tok_app. rewrite Hd. cbn [orb SlotModel.tok_go negb andb].
    rewrite Hb. cbn. apply app_nil_r.
  - rewrite k_has_dash_app, k_has_dash1, Hd, Hb. reflexivity.
Qed.

Lemma k_step_keep : forall l j, (j < length l)%nat ->
  ~ (RcIdentModel.bz (nth j l (RcIdentModel.zb 0)) = 45 /\ SlotModel.has_dash (firstn j l) = false) ->
  SlotModel.TOK (firstn (S j) l) = SlotModel.TOK (firstn j l) ++ [SlotModel.lower (nth j l (RcIdentModel.zb 0))] /\
  SlotModel.has_dash (firstn (S j) l) = SlotModel.has_dash (firstn j l).
Proof.
  intros l j Hj Hn. rewrite (k_firstn_S l j (RcIdentModel.zb 0) Hj).
  set (b := nth j l (RcIdentModel.zb 0)) in *. split.
  - unfold SlotModel.TOK. rewrite k_tok_app. cbn [orb SlotModel.tok_go].
    destruct (negb (SlotModel.has_dash (firstn j l)) && (RcIdentModel.bz b =? 45))%bool eqn:E.
    + exfalso. apply andb_true_iff in E as [E1 E2]. apply negb_true_iff in E1. apply Z.eqb_eq in E2. tauto.
    + reflexivity.
  - rewrite k_has_dash_app, k_has_dash1. destruct (Z.eqb_spec (RcIdentModel.bz b) 45) as [E|E].
    + destruct (SlotModel.has_dash (firstn j l)); [reflexivity | exfalso; apply Hn; split; [exact E | reflexivity]].
    + apply orb_false_r.
Qed.

Lemma k_tok_le : forall l j, (length (SlotModel.TOK (firstn j l)) <= length (SlotModel.TOK l))%nat.
Proof. intros l j. rewrite (k_tok_split l j), length_app. lia. Qed.

Lemma k_tok_all : forall l, SlotModel.TOK (firstn (length l) l) = SlotModel.TOK l.
Proof. intro l. rewrite firstn_all. reflexivity. Qed.

Lemma k_bz_range : forall b : byte, 0 <= RcIdentModel.bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.

Lemma k_lower_bz : forall b, RcIdentModel.bz (SlotModel.lower b) =
  (if (65 <=? RcIdentModel.bz b) && (RcIdentModel.bz b <=? 90) then RcIdentModel.bz b + 32 else RcIdentModel.bz b)%bool.
Proof.
  intros b. unfold SlotModel.lower.
  destruct ((65 <=? RcIdentModel.bz b) && (RcIdentModel.bz b <=? 90))%bool eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold RcIdentModel.bz at 1, RcIdentModel.zb. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* The two bytes of a string with its NUL: inside the string, and the NUL. *)
Lemma k_nthb_in : forall (l : list byte) i, (i < length l)%nat ->
  RcIdentModel.nthb (l ++ [RcIdentModel.zb 0]) i = nth i l (RcIdentModel.zb 0).
Proof. intros l i Hi. unfold RcIdentModel.nthb. apply app_nth1. exact Hi. Qed.

Lemma k_nthb_end : forall (l : list byte), RcIdentModel.nthb (l ++ [RcIdentModel.zb 0]) (length l) = RcIdentModel.zb 0.
Proof. intros l. unfold RcIdentModel.nthb. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma k_nzl_nth : forall l i, nzl l -> (i < length l)%nat -> RcIdentModel.bz (nth i l (RcIdentModel.zb 0)) <> 0.
Proof.
  intros l i Hl Hi. unfold nzl in Hl. rewrite Forall_forall in Hl. apply Hl. apply nth_In. exact Hi.
Qed.

(* ---- the symbolic state at the loop head ------------------------------------------------------------------- *)
(* x6 (t1) holds the shadow base. Atom 32 is tk + t (the alias of s5 + a2), 33 the byte tk[t], 34 the byte nm[j];
   the regions are nm[j] at a5 and tk[t] at s5 + a2, both read-only. *)
Definition SB_K : Z := 0x7fff8000.
Definition BX_K : sv := SOff 6 0.
Definition Bspan_K : Z * Z := (SB_K, SB_K + 2 ^ 44 - 1).
Definition AF_khead : Z := 0x17f4.
Definition AF_kmid : Z := 0x1894.
Definition tk_regions : smem :=
  [ YP09.mkRegion (Some 15%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))];
    YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition tk_facts : facts :=
  mkFacts [ (6%nat, mkAF SB_K SB_K 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0);
            (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (15%nat, mkAF 4096 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] []
    [ (SAlu ALU_ADD (SOff 21 0) (SOff 12 0), SOff 32 0) ].
Definition ss_tk : sstate := mkSS AF_khead sr_atoms tk_regions None tk_facts.
Definition SH_tk : list shent := [mkSHE 10 0 1; mkSHE 32 0 1].
(* The registers the loop never writes. *)
Definition TK_KEPT : list (bv 5) := [2; 3; 4; 6; 8; 9; 14; 18; 19; 21; 22; 24; 25]%bv.

(* ---- generic facts ------------------------------------------------------------------------------------------ *)
Lemma k_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma k_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma k_U0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. intros E n v H Hv. rewrite (k_U E n v 0 H), Z.add_0_r. apply Z.mod_small. exact Hv. Qed.
Lemma k_Ulit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma k_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
(* The lower-casing 0x81f38 .. 0x81f48: a6 + ((a6 - 65 <u 26) << 5). *)
Lemma k_lower_U : forall E n v, ew E n = w64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff n (-65)) (SLit 26)) (SLit 5))) =
  (if (65 <=? v) && (v <=? 90) then v + 32 else v)%bool.
Proof.
  intros E n v Hn Hv. rewrite !U_SAlu, !U_SLit, (k_U E n v 0 Hn), (k_U E n v (-65) Hn).
  cbn [zalu_raw]. unfold zcanon, M64.
  rewrite (Z.mod_small 26) by lia. rewrite (Z.mod_small 5) by lia. rewrite (Z.mod_small (v + 0)) by lia.
  change (Z.land 5 63) with 5.
  assert (Hs : forall x, (x = 0 \/ x = 1) -> (Z.shiftl x 5) mod 2 ^ 64 = 32 * x)
    by (intros x [-> | ->]; reflexivity).
  destruct ((65 <=? v) && (v <=? 90))%bool eqn:Hc.
  - apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    rewrite (Z.mod_small (v + -65)) by lia.
    destruct (Z.ltb_spec (v + -65) 26) as [_|H3]; [|lia].
    cbv iota. rewrite (Z.mod_small 1) by lia. rewrite (Hs 1) by lia. rewrite Z.mod_small by lia. lia.
  - assert (Hc' : ~ (65 <= v <= 90)).
    { intros [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. rewrite A1, A2 in Hc. discriminate. }
    assert (Hm : 26 <= (v + -65) mod 2 ^ 64).
    { destruct (Z_lt_le_dec v 65) as [H65|H65].
      - rewrite <- (Z.mod_add (v + -65) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    destruct (Z.ltb_spec ((v + -65) mod 2 ^ 64) 26) as [H3|_]; [lia|].
    cbv iota. rewrite (Z.mod_small 0) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma k_agree_ext : forall regsL extra E E',
  env_agree 32 (Ereg regsL extra) E -> env_agree 32 E E' -> env_agree 32 (Ereg regsL extra) E'.
Proof.
  intros regsL extra E E' [H1 H2] [H3 H4]. split.
  - intros n Hn. rewrite (H3 n Hn). exact (H1 n Hn).
  - rewrite H4. exact H2.
Qed.

(* ew of an extended environment at a low atom *)
Ltac kenv := repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ].
(* a register of the state after a run, as the value the boundary asks for: its symbolic value is the atom nn
   of the entry environment (Hb) shifted by cc *)
Ltac kqr Hq nn vv cc Hb :=
  rewrite Hq; apply k_sv;
  lazymatch goal with |- U ?Ev _ = _ => rewrite (k_U Ev nn vv cc ltac:(kenv; exact Hb)) end;
  first [ reflexivity | (rewrite Z.add_0_r; reflexivity) | (f_equal; lia) ].
Ltac kql Hq zz :=
  rewrite Hq; apply k_sv;
  lazymatch goal with |- U ?Ev _ = _ => rewrite (k_Ulit Ev zz ltac:(lia)) end;
  symmetry; apply Z.mod_small; cbn; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition k_env (regs : bvmap 5 word) (tk : Z) (t : nat) (nb tb : byte) : env :=
  Eimg (Ereg regs [w64 (tk + Z.of_nat t); w64 (RcIdentModel.bz tb); w64 (RcIdentModel.bz nb)]).

(* ---- the memory a read-only run leaves -------------------------------------------------------------------- *)
Definition k_same (W : world SEGS) (m m' : word -> option byte) : Prop :=
  forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x.
Lemma k_same_refl : forall W m, k_same W m m.
Proof. intros W m x. reflexivity. Qed.
Lemma k_same_run : forall W E (rs : smem) m0 m1 m2,
  frame_of E rs (rd W m1) (rd W m2) -> k_same W m0 m1 ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> k_same W m0 m2.
Proof.
  intros W E rs m0 m1 m2 HF HK Hro x. rewrite <- (HK x). apply HF. intros (rg & Hin & Hr).
  rewrite forallb_forall in Hro. specialize (Hro rg Hin). apply Z.leb_le in Hro. lia.
Qed.
Lemma k_mbyte_same : forall W m m' a, k_same W m m' -> mbyte SEGS (rd W m') a = mbyte SEGS (rd W m) a.
Proof. intros W m m' a HK. unfold mbyte. rewrite (HK (Z_to_bv 64 a)). reflexivity. Qed.
Lemma k_aview_same : forall W m m' a, k_same W m m' -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W m m' a HK. unfold aview. rewrite (k_mbyte_same W m m' a HK). reflexivity. Qed.
Lemma k_vm_same : forall W m m' a n v, k_same W m m' -> val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v.
Proof. intros W m m' a n v HK Hv k Hk. rewrite (k_mbyte_same W m m' _ HK). exact (Hv k Hk). Qed.
Lemma k_bytes_same : forall W m m' a bs, k_same W m m' -> bytes_at8 W m a bs -> bytes_at8 W m' a bs.
Proof.
  intros W m m' a bs HK Hb j Hj. destruct (Hb j Hj) as [Hv Hr]. split; [|exact Hr].
  exact (k_vm_same W m m' _ _ _ HK Hv).
Qed.
(* A byte of a string with its NUL, as val_mem. *)
Lemma k_byte_at : forall (W : world SEGS) mem a (l : list byte) i, bytes_at8 W mem a l -> (i < length l)%nat ->
  val_mem SEGS (rd W mem) (a + Z.of_nat i) 1 (RcIdentModel.bz (RcIdentModel.nthb l i)).
Proof.
  intros W mem a l i Hb Hi. assert (Hi' : (i < length (map (fun b : byte => bv_unsigned b) l))%nat)
    by (rewrite length_map; exact Hi).
  destruct (Hb i Hi') as [Hv _]. unfold RcIdentModel.nthb, RcIdentModel.bz, RcIdentModel.zb.
  rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) in Hv by exact Hi'.
  rewrite map_nth in Hv. exact Hv.
Qed.

Section c.
(* the Section of LLVMFuzzerTestOneInput_Kcut.v, in the same order *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KLOOP := (k_loop_at B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KMID := (k_mid B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation NM g := (SlotModel.n_EXP_NM (e_pl g)).
#[local] Notation TKL g := (SlotModel.n_TK (e_pl g)).

(* ---- what the loop takes ----------------------------------------------------------------------------------- *)
Hypothesis LAWS : AR_laws SEGS B.
(* cgif ACfh.v:162-164, as LLVMFuzzerTestOneInput.v states it *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ecommon of a state whose memory reads as before and whose frame registers are kept. *)
Lemma k_ecommon_same : forall g pos mf ly S (W : world SEGS) regs mem md regs' mem' md',
  k_same W mem mem' ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 19 = getr regs 19 ->
  m_fds md' = m_fds (e_md g) -> m_fs md' = m_fs (e_md g) ->
  ECOMMON g pos mf ly S W regs mem md -> ECOMMON g pos mf ly S W regs' mem' md'.
Proof.
  intros g pos mf ly S W regs mem md regs' mem' md' HK F2 F9 F8 F3 F4 F19 Hfd Hfs
    (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & R19 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 &
     V12 & V13 & V14 & V15 & V16 & V17 & V18 & HPRE & _ & _ & HPL).
  unfold ecommon. rewrite F2, F9, F8, F3, F4, F19.
  refine (conj R2 (conj R9 (conj R8 (conj Hmf (conj Hmf32 (conj R3 (conj R4 (conj R19 _)))))))).
  repeat (split; [eapply k_vm_same; [exact HK | eassumption] |]).
  split; [exact HPRE|]. split; [intros fd; rewrite Hfd; reflexivity|]. split; [exact Hfs|].
  exact (k_bytes_same W mem mem' _ _ HK HPL).
Qed.

(* Two blocks of the run's list are apart. *)
Lemma k_two_blocks : forall ly S (W : world SEGS) mem md x y l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
  zdisjoint (block_rng x) (block_rng y).
Proof.
  intros ly S W mem md x y l HAR HP.
  assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  apply in_split in Hx as (a1 & a2 & Ea). rewrite Ea in HP.
  assert (HP2 : Permutation (y :: l) (a1 ++ a2))
    by (apply Permutation_cons_app_inv with (a := x); apply Permutation_sym; exact HP).
  assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [exact HP2 | left; reflexivity]).
  apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & ->).
  - assert (Hd : zdisjoint (block_rng y) (block_rng x)).
    { apply (sep_blocks_pos SEGS B LAWS ly S W mem md y x b1 b2 a2 HAR). rewrite Ea. rewrite <- app_assoc. reflexivity. }
    unfold zdisjoint in *. lia.
  - exact (sep_blocks_pos SEGS B LAWS ly S W mem md x y a1 b1 b2 HAR Ea).
Qed.

(* ---- the symbolic state at 0x81f00 -------------------------------------------------------------------------- *)
Lemma k_start : forall g nm tk dp (j t : nat) ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  AR SEGS B ly2 S2 W2 mem2 md2 ->
  hblocks B g ly2 S2 (k_blocks g nm tk dp) ->
  SlotModel.n_r (e_pl g) = 0 -> (j <= length (NM g))%nat -> (t <= length (TKL g))%nat ->
  getr regs2 10 = w64 (nm + Z.of_nat j) -> getr regs2 15 = w64 (nm + Z.of_nat j) ->
  getr regs2 12 = w64 (Z.of_nat t) -> getr regs2 6 = w64 SHADOW_OFF -> getr regs2 21 = w64 tk ->
  bytes_at8 W2 mem2 nm (NM g ++ [RcIdentModel.zb 0]) -> bytes_at8 W2 mem2 tk (TKL g ++ [RcIdentModel.zb 0]) ->
  let E := k_env regs2 tk t (RcIdentModel.nthb (NM g ++ [RcIdentModel.zb 0]) j)
             (RcIdentModel.nthb (TKL g ++ [RcIdentModel.zb 0]) t) in
  st_ok_pi SEGS VAL E ss_tk (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + AF_khead)) mem2 (seg_rom SEGS))) /\
  sh_ok SEGS BX_K SH_tk E (mrestrict (w_H W2) mem2).
Proof.
  intros g nm tk dp j t ly2 S2 W2 regs2 mem2 md2 HAR HB Hr0 Hj Ht R10 R15 R12 R6 R21 BNM BTK E.
  set (nb := RcIdentModel.nthb (NM g ++ [RcIdentModel.zb 0]) j) in *.
  set (tb := RcIdentModel.nthb (TKL g ++ [RcIdentModel.zb 0]) t) in *.
  destruct (k_r0 _ Hr0) as [Hwok Hfit]. destruct (k_fits _ Hfit) as (Fn & Ft & _).
  pose proof (k_n_tk_len (e_pl g)) as HTL. unfold SlotModel.n_ln in Fn.
  destruct HB as [HP _]. unfold k_blocks in HP. cbn [app] in HP.
  assert (Hinn : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  assert (Hint : In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | right; left; reflexivity]).
  pose proof (k_two_blocks _ _ _ _ _ _ _ _ HAR HP) as Hdis. unfold zdisjoint, block_rng in Hdis. cbn [fst snd] in Hdis.
  destruct (al_blocks SEGS B LAWS _ _ _ _ _ _ _ HAR Hinn) as (_ & Hn0 & Hn1 & Hnapp & _).
  destruct (al_blocks SEGS B LAWS _ _ _ _ _ _ _ HAR Hint) as (_ & Ht0 & Ht1 & Htapp & _).
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(lia)) as [Qn1 Qn2].
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(lia)) as [Qt1 Qt2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hjz : Z.of_nat j + 1 <= Z.max (SlotModel.t_cap_name (e_pl g)) 1) by lia.
  assert (Htz : Z.of_nat t + 1 <= Z.max (SlotModel.t_cap_tok (e_pl g)) 1) by lia.
  assert (Hne : nm + Z.of_nat j + 1 <= tk + Z.of_nat t \/ tk + Z.of_nat t + 1 <= nm + Z.of_nat j) by lia.
  pose proof (k_bz_range nb) as Hnb. pose proof (k_bz_range tb) as Htb.
  assert (Mn : val_mem SEGS (rd W2 mem2) (nm + Z.of_nat j) 1 (RcIdentModel.bz nb))
    by (apply k_byte_at; [exact BNM | rewrite length_app; cbn [length]; lia]).
  assert (Mt : val_mem SEGS (rd W2 mem2) (tk + Z.of_nat t) 1 (RcIdentModel.bz tb))
    by (apply k_byte_at; [exact BTK | rewrite length_app; cbn [length]; lia]).
  assert (RAn : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (nm + Z.of_nat j) 1)
    by (apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinn); lia).
  assert (RAt : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (tk + Z.of_nat t) 1)
    by (apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hint); lia).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 [w64 (tk + Z.of_nat t); w64 (RcIdentModel.bz tb);
                 w64 (RcIdentModel.bz nb)]) n)
    by (intros n Hn; subst E; unfold k_env; apply Eimg_low; exact Hn).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
    by (intros n rr Hn; subst E; unfold k_env; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E6 : ew E 6 = w64 SHADOW_OFF) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E10 : ew E 10 = w64 (nm + Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E15 : ew E 15 = w64 (nm + Z.of_nat j)) by (rewrite (EEo 15%nat 15%bv eq_refl); exact R15).
  assert (E12 : ew E 12 = w64 (Z.of_nat t)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E21 : ew E 21 = w64 tk) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E32 : ew E 32 = w64 (tk + Z.of_nat t)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = w64 (RcIdentModel.bz tb)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = w64 (RcIdentModel.bz nb)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply k_unsigned; exact Hv).
  clear EL EEo.
  split.
  - rewrite restrict_mkst_fx. unfold ss_tk. apply pa_entry_st_ok_full.
    + subst E. unfold k_env. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold tk_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 15%nat (nm + Z.of_nat j) E15) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (nm + Z.of_nat j) 0 1 (SOff 34 0) (RcIdentModel.bz nb)).
        -- apply k_sv. rewrite (k_U E 34 _ 0 E34), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. exact Hnb.
        -- cbn. lia.
        -- rewrite Z.add_0_r. exact Mn.
      * rewrite (VB 32%nat (tk + Z.of_nat t) E32) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (tk + Z.of_nat t) 0 1 (SOff 33 0) (RcIdentModel.bz tb)).
        -- apply k_sv. rewrite (k_U E 33 _ 0 E33), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. exact Htb.
        -- cbn. lia.
        -- rewrite Z.add_0_r. exact Mt.
    + apply pairwise_disjoint_of_extents. unfold tk_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 15%nat (nm + Z.of_nat j) E15) by lia. rewrite (VB 32%nat (tk + Z.of_nat t) E32) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hne. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [tk_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E6, E33, E34, E10, E15, E32. rewrite !k_unsigned by (unfold SHADOW_OFF; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB_K, SHADOW_OFF.
        clear - Hnb Htb Hn0 Hn1 Ht0 Ht1 Hjz Htz Qn1 Qn2 Qt1 Qt2 C1. repeat split; lia.
      * cbn [tk_facts f_alias alias_ok]. split; [|exact I].
        apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (k_U0 E 21 tk E21) by lia.
        rewrite (k_U0 E 12 (Z.of_nat t) E12) by lia. rewrite (k_U0 E 32 (tk + Z.of_nat t) E32) by lia.
        unfold zcanon, M64. apply Z.mod_small. lia.
  - assert (UB : U E BX_K = SHADOW_OFF) by (unfold BX_K; apply (k_U0 E 6 SHADOW_OFF E6); unfold SHADOW_OFF; lia).
    unfold sh_ok, SH_tk. repeat apply Forall_cons; try apply Forall_nil.
    + apply (shent_ok_of_range SEGS (w_H W2) mem2 E BX_K 10 (nm + Z.of_nat j) 1 (nm + Z.of_nat j) 0 1 RAn UB).
      * apply (k_U0 E 10 _ E10). lia.
      * lia.
      * lia.
      * intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W2) mem2 E BX_K 32 (tk + Z.of_nat t) 1 (tk + Z.of_nat t) 0 1 RAt UB).
      * apply (k_U0 E 32 _ E32). lia.
      * lia.
      * lia.
      * intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* ---- tactics of the walk ------------------------------------------------------------------------------- *)
(* a register of the current symbolic state, as the denotation of its symbolic value *)
Ltac kreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* after a run whose regions are all read-only: chain k_same *)
Ltac kkeep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), KI : k_same ?Wd ?m0 ?m1 |- _ =>
      let K2 := fresh "KEEPn" in
      assert (K2 : k_same Wd m0 m2)
        by (apply (k_same_run Wd Ex rs m0 m1 m2 HFr KI); vm_compute; reflexivity);
      clear KI; rename K2 into KEEPI
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* membership in the kept-register list *)
Ltac kin := unfold TK_KEPT; cbn [In]; repeat first [ solve [left; reflexivity] | right ].
(* the registers the loop keeps, from the entry registers *)
Ltac krk HAE :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wd) ?msx) |- _ =>
      lazymatch type of HAE with
      | env_agree _ ?A _ =>
          let HAEx := fresh "HAEx" in
          assert (HAEx : env_agree 32 A Ex)
            by (eapply k_agree_ext; [exact HAE | split; [intros nn Hnn; kenv; reflexivity | reflexivity]]);
          pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wd) msx) _ _ TK_KEPT HS HAEx
                        ltac:(vm_compute; reflexivity)) as RK;
          cbn [ms_regs restrict] in RK; clear HAEx
      end
  end.

Section d.
Variable g : ectx.
Variables pos mf nm tk dp : Z.

(* ---- one iteration: 0x81f00 .. the head again, or 0x81fa0 ------------------------------------------------ *)
(* The three paths of one byte. The two that reach the compare (0x81f24) are left open by the bracket and the
   compare runs once, on both: the '-' already dropped (d = true), and a plain byte. *)
Lemma k_step : forall (j t : nat) (d : bool),
  (forall (t' : nat) (d' : bool) W3 c3, KLOOP g pos mf nm tk dp (S j) t' d' W3 c3 ->
     SRr SEGS W3 c3 (KMID g pos mf nm tk dp)) ->
  forall W2 c2, KLOOP g pos mf nm tk dp j t d W2 c2 -> SRr SEGS W2 c2 (KMID g pos mf nm tk dp).
Proof.
  intros j t d IH W2 c2 HC.
  destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & Hk & MLE & MOK & HEC & HP).
  destruct HP as (HB & Hr0 & Hjl & Ht & Hd & R10 & R15 & R12 & R13 & R14 & R6 & R18 & R21 & R22 & R24 & R25 &
                  V136 & V184 & BNM & BTK & BDP).
  pose proof HJ as (HAR & _).
  destruct (k_r0 _ Hr0) as [Hwok Hfit].
  pose proof (k_exp_nm_nz _ Hwok) as HNZ.
  assert (Htt : (t <= length (TKL g))%nat) by (rewrite Ht; unfold SlotModel.n_TK; apply k_tok_le).
  assert (Hz0 : RcIdentModel.bz (RcIdentModel.zb 0) = 0) by (vm_compute; reflexivity).
  destruct (k_start g nm tk dp j t ly2 S2 W2 regs2 mem2 md2 HAR HB Hr0 Hjl Htt R10 R15 R12 R6 R21 BNM BTK)
    as [HS SHOK].
  unfold k_env in HS, SHOK.
  remember (RcIdentModel.nthb (NM g ++ [RcIdentModel.zb 0]) j) as nb eqn:Enb.
  remember (RcIdentModel.nthb (TKL g ++ [RcIdentModel.zb 0]) t) as tb eqn:Etb.
  (* the byte of the name at j: a byte of the name, or its NUL *)
  assert (Hnbn : (j < length (NM g))%nat -> nb = nth j (NM g) (RcIdentModel.zb 0))
    by (intros Hlt; rewrite Enb; apply k_nthb_in; exact Hlt).
  assert (Hnbz : (j < length (NM g))%nat -> RcIdentModel.bz nb <> 0)
    by (intros Hlt; rewrite (Hnbn Hlt); apply k_nzl_nth; [exact HNZ | exact Hlt]).
  assert (Hjeq : j = length (NM g) -> RcIdentModel.bz nb = 0)
    by (intros He; rewrite Enb, He, k_nthb_end; exact Hz0).
  pose proof (k_bz_range nb) as Hnbr. pose proof (k_bz_range tb) as Htbr.
  (* the environment *)
  remember (Eimg (Ereg regs2 [w64 (tk + Z.of_nat t); w64 (RcIdentModel.bz tb); w64 (RcIdentModel.bz nb)]))
    as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat ->
            ew E n = ew (Ereg regs2 [w64 (tk + Z.of_nat t); w64 (RcIdentModel.bz tb);
                                     w64 (RcIdentModel.bz nb)]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
    by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E10 : ew E 10 = w64 (nm + Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E15 : ew E 15 = w64 (nm + Z.of_nat j)) by (rewrite (EEo 15%nat 15%bv eq_refl); exact R15).
  assert (E12 : ew E 12 = w64 (Z.of_nat t)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (if d then 1 else 0)) by (rewrite (EEo 13%nat 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 45) by (rewrite (EEo 14%nat 14%bv eq_refl); exact R14).
  assert (E33 : ew E 33 = w64 (RcIdentModel.bz tb))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = w64 (RcIdentModel.bz nb))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (HAE : env_agree 32 (Ereg regs2
                  [w64 (tk + Z.of_nat t); w64 (RcIdentModel.bz tb); w64 (RcIdentModel.bz nb)]) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  clear HE EL EEo.
  assert (KEEPI : k_same W2 mem2 mem2) by apply k_same_refl.
  unfold cfg_at. change (w64 (BASE + 0x17f4)) with (Z_to_bv 64 (BASE + AF_khead)).
  (* 0x81f00 .. 0x81f14: the shadow test of nm + j, the load of nm[j], beq a6,a4 *)
  paj_run_tok RUN HS HJ SHOK Bspan_K; [awr_ok_tac|]. kkeep.
  psrr_branch_tok RUN BR HS SHOK Bspan_K;
  [ (* nm[j] = '-' *)
    rewrite branch_eq_U in Hc;
    lazymatch type of Hc with (U ?Ev _ =? U ?Ev _) = _ =>
      rewrite (k_U0 Ev 34 (RcIdentModel.bz nb) ltac:(kenv; exact E34) ltac:(lia)) in Hc;
      rewrite (k_U0 Ev 14 45 ltac:(kenv; exact E14) ltac:(lia)) in Hc end;
    apply Z.eqb_eq in Hc; rename Hc into Hb45;
    assert (Hjlt : (j < length (NM g))%nat)
      by (destruct (Nat.lt_ge_cases j (length (NM g))) as [Hlt|Hge];
          [exact Hlt | exfalso; rewrite (Hjeq ltac:(lia)) in Hb45; lia]);
    paj_run_tok RUN HS HJ SHOK Bspan_K; [awr_ok_tac|]; kkeep;
    psrr_branch_tok RUN BR HS SHOK Bspan_K;
    [ (* 0x81f20 beqz a3 taken: the first '-', dropped; the token does not move *)
      rewrite branch_eq_U in Hc;
      lazymatch type of Hc with (U ?Ev _ =? U ?Ev _) = _ =>
        rewrite (k_U0 Ev 13 (if d then 1 else 0) ltac:(kenv; exact E13) ltac:(destruct d; lia)) in Hc;
        rewrite (k_Ulit Ev 0 ltac:(lia)) in Hc end;
      apply Z.eqb_eq in Hc;
      assert (Hdf : d = false) by (destruct d; [cbn in Hc; lia | reflexivity]); clear Hc;
      destruct (k_step_dash (NM g) j Hjlt ltac:(rewrite <- (Hnbn Hjlt); exact Hb45)
                  ltac:(rewrite <- Hd; exact Hdf)) as [HT' HD'];
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_K AF_khead; [awr_ok_tac|]; kkeep;
      krk HAE;
      kreg HS (10%bv : bv 5) Q10; kreg HS (15%bv : bv 5) Q15;
      kreg HS (12%bv : bv 5) Q12; kreg HS (13%bv : bv 5) Q13;
      pmkst HS;
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R ?PC ?M ?ROM) ?MD) _ =>
        destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Hfd Hfs];
        apply (IH t true W2 (mkCfg (mkst R PC M ROM) MD));
        unfold k_loop_at, acut; exists ly2, S2, R, M, MD end;
      split; [reflexivity|]; split; [exact HJ|]; split; [exact HFR|]; split; [exact Hk|];
      split; [exact MLE|]; split; [exact MOK|];
      split;
      [ eapply k_ecommon_same;
        [ exact KEEPI | apply RK; kin | apply RK; kin | apply RK; kin | apply RK; kin | apply RK; kin
        | apply RK; kin | exact Hfd | exact Hfs | exact HEC ] |];
      split; [exact HB|]; split; [exact Hr0|]; split; [lia|];
      split; [rewrite HT'; exact Ht|]; split; [rewrite HD'; reflexivity|];
      split; [kqr Q10 10%nat (nm + Z.of_nat j) 1 E10|];
      split; [kqr Q15 15%nat (nm + Z.of_nat j) 1 E15|];
      split; [kqr Q12 12%nat (Z.of_nat t) 0 E12|];
      split; [kql Q13 1|];
      split; [rewrite (RK 14%bv ltac:(kin)); exact R14|];
      split; [rewrite (RK 6%bv ltac:(kin)); exact R6|];
      split; [rewrite (RK 18%bv ltac:(kin)); exact R18|];
      split; [rewrite (RK 21%bv ltac:(kin)); exact R21|];
      split; [rewrite (RK 22%bv ltac:(kin)); exact R22|];
      split; [rewrite (RK 24%bv ltac:(kin)); exact R24|];
      split; [rewrite (RK 25%bv ltac:(kin)); exact R25|];
      split; [eapply k_vm_same; [exact KEEPI | exact V136]|];
      split; [eapply k_vm_same; [exact KEEPI | exact V184]|];
      split; [eapply k_bytes_same; [exact KEEPI | exact BNM]|];
      split; [eapply k_bytes_same; [exact KEEPI | exact BTK]|];
      eapply k_bytes_same; [exact KEEPI | exact BDP]
    | (* a '-' was dropped before: on to the compare *)
      rewrite branch_eq_U in Hc;
      lazymatch type of Hc with (U ?Ev _ =? U ?Ev _) = _ =>
        rewrite (k_U0 Ev 13 (if d then 1 else 0) ltac:(kenv; exact E13) ltac:(destruct d; lia)) in Hc;
        rewrite (k_Ulit Ev 0 ltac:(lia)) in Hc end;
      apply Z.eqb_neq in Hc;
      assert (Hdt : d = true) by (destruct d; [reflexivity | cbn in Hc; lia]); clear Hc;
      assert (Hnot : ~ (RcIdentModel.bz (nth j (NM g) (RcIdentModel.zb 0)) = 45 /\
                        SlotModel.has_dash (firstn j (NM g)) = false))
        by (intros [_ Hx]; rewrite <- Hd, Hdt in Hx; discriminate) ]
  | (* nm[j] <> '-' *)
    rewrite branch_eq_U in Hc;
    lazymatch type of Hc with (U ?Ev _ =? U ?Ev _) = _ =>
      rewrite (k_U0 Ev 34 (RcIdentModel.bz nb) ltac:(kenv; exact E34) ltac:(lia)) in Hc;
      rewrite (k_U0 Ev 14 45 ltac:(kenv; exact E14) ltac:(lia)) in Hc end;
    apply Z.eqb_neq in Hc; rename Hc into Hb45;
    paj_run_tok RUN HS HJ SHOK Bspan_K; [awr_ok_tac|]; kkeep;
    psrr_branch_tok RUN BR HS SHOK Bspan_K;
    [ (* 0x81f18 beqz a6 taken: the name is done, and so must the token be *)
      rewrite branch_eq_U in Hc;
      lazymatch type of Hc with (U ?Ev _ =? U ?Ev _) = _ =>
        rewrite (k_U0 Ev 34 (RcIdentModel.bz nb) ltac:(kenv; exact E34) ltac:(lia)) in Hc;
        rewrite (k_Ulit Ev 0 ltac:(lia)) in Hc end;
      apply Z.eqb_eq in Hc;
      assert (Hje : j = length (NM g))
        by (destruct (Nat.lt_ge_cases j (length (NM g))) as [Hlt|Hge];
            [exfalso; exact (Hnbz Hlt Hc) | lia]);
      clear Hc;
      assert (Htend : t = length (TKL g))
        by (rewrite Ht, Hje; unfold SlotModel.n_TK; rewrite k_tok_all; reflexivity);
      assert (Htb0 : RcIdentModel.bz tb = 0) by (rewrite Etb, Htend, k_nthb_end; exact Hz0);
      paj_run_tok RUN HS HJ SHOK Bspan_K; [awr_ok_tac|]; kkeep;
      psrr_branch_tok RUN BR HS SHOK Bspan_K;
      [ (* 0x81f9c bnez a0: the token would be longer; refuted *)
        exfalso; rewrite branch_ne_U in Hc;
        lazymatch type of Hc with negb (U ?Ev _ =? U ?Ev _) = _ =>
          rewrite (k_U0 Ev 33 (RcIdentModel.bz tb) ltac:(kenv; exact E33) ltac:(lia)) in Hc;
          rewrite (k_Ulit Ev 0 ltac:(lia)) in Hc end;
        rewrite Htb0 in Hc; cbn in Hc; discriminate Hc
      | clear Hc;
        paj_run_to_tok RUNTO HS HJ SHOK Bspan_K AF_kmid; [awr_ok_tac|]; kkeep;
        krk HAE;
        pmkst HS;
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R ?PC ?M ?ROM) ?MD) _ =>
          destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Hfd Hfs];
          apply SRr_ret; unfold k_mid, acut; exists ly2, S2, R, M, MD end;
        split; [reflexivity|]; split; [exact HJ|]; split; [exact HFR|]; split; [exact Hk|];
        split; [exact MLE|]; split; [exact MOK|];
        split;
        [ eapply k_ecommon_same;
          [ exact KEEPI | apply RK; kin | apply RK; kin | apply RK; kin | apply RK; kin | apply RK; kin
          | apply RK; kin | exact Hfd | exact Hfs | exact HEC ] |];
        split; [exact HB|]; split; [exact Hr0|];
        split; [rewrite (RK 18%bv ltac:(kin)); exact R18|];
        split; [rewrite (RK 21%bv ltac:(kin)); exact R21|];
        split; [rewrite (RK 22%bv ltac:(kin)); exact R22|];
        split; [rewrite (RK 24%bv ltac:(kin)); exact R24|];
        split; [rewrite (RK 25%bv ltac:(kin)); exact R25|];
        split; [eapply k_vm_same; [exact KEEPI | exact V136]|];
        split; [eapply k_vm_same; [exact KEEPI | exact V184]|];
        eapply k_bytes_same; [exact KEEPI | exact BDP] ]
    | (* a plain byte: on to the compare *)
      rewrite branch_eq_U in Hc;
      lazymatch type of Hc with (U ?Ev _ =? U ?Ev _) = _ =>
        rewrite (k_U0 Ev 34 (RcIdentModel.bz nb) ltac:(kenv; exact E34) ltac:(lia)) in Hc;
        rewrite (k_Ulit Ev 0 ltac:(lia)) in Hc end;
      apply Z.eqb_neq in Hc;
      assert (Hjlt : (j < length (NM g))%nat)
        by (destruct (Nat.lt_ge_cases j (length (NM g))) as [Hlt|Hge];
            [exact Hlt | exfalso; apply Hc; apply Hjeq; lia]);
      clear Hc;
      assert (Hnot : ~ (RcIdentModel.bz (nth j (NM g) (RcIdentModel.zb 0)) = 45 /\
                        SlotModel.has_dash (firstn j (NM g)) = false))
        by (intros [Hx _]; apply Hb45; rewrite (Hnbn Hjlt); exact Hx) ] ];
  (* 0x81f24 .. 0x81f5c, on both paths: the load of tk[t], the lower-casing of nm[j], bne a1,a6 (the abort at
     0x822f0, refuted by tk[t] = lower nm[j]), the three counters, and the head again with t + 1. *)
  ( paj_run_tok RUN HS HJ SHOK Bspan_K; [awr_ok_tac|]; kkeep;
  destruct (k_tok_at (NM g) j (nth j (NM g) (RcIdentModel.zb 0)) (skipn (S j) (NM g))
              (k_skipn_nth (NM g) j (RcIdentModel.zb 0) Hjlt) Hnot) as [Htlt Htv];
  assert (Httl : (t < length (TKL g))%nat) by (unfold SlotModel.n_TK; rewrite Ht; exact Htlt);
  assert (Htbv : tb = SlotModel.lower (nth j (NM g) (RcIdentModel.zb 0)))
    by (rewrite Etb, (k_nthb_in (TKL g) t Httl); unfold SlotModel.n_TK; rewrite Ht; exact Htv);
  destruct (k_step_keep (NM g) j Hjlt Hnot) as [HT' HD'];
  psrr_branch_tok RUN BR HS SHOK Bspan_K;
  [ exfalso; rewrite branch_ne_U in Hc;
    lazymatch type of Hc with negb (U ?Ev _ =? U ?Ev _) = _ =>
      rewrite (k_U0 Ev 33 (RcIdentModel.bz tb) ltac:(kenv; exact E33) ltac:(lia)) in Hc;
      rewrite (k_lower_U Ev 34 (RcIdentModel.bz nb) ltac:(kenv; exact E34) ltac:(lia)) in Hc end;
    rewrite <- k_lower_bz in Hc; rewrite Htbv, (Hnbn Hjlt) in Hc;
    rewrite Z.eqb_refl in Hc; cbn in Hc; discriminate Hc
  | clear Hc;
    paj_run_to_tok RUNTO HS HJ SHOK Bspan_K AF_khead; [awr_ok_tac|]; kkeep;
    krk HAE;
    kreg HS (10%bv : bv 5) Q10; kreg HS (15%bv : bv 5) Q15;
    kreg HS (12%bv : bv 5) Q12; kreg HS (13%bv : bv 5) Q13;
    pmkst HS;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R ?PC ?M ?ROM) ?MD) _ =>
      destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Hfd Hfs];
      apply (IH (S t) d W2 (mkCfg (mkst R PC M ROM) MD));
      unfold k_loop_at, acut; exists ly2, S2, R, M, MD end;
    split; [reflexivity|]; split; [exact HJ|]; split; [exact HFR|]; split; [exact Hk|];
    split; [exact MLE|]; split; [exact MOK|];
    split;
    [ eapply k_ecommon_same;
      [ exact KEEPI | apply RK; kin | apply RK; kin | apply RK; kin | apply RK; kin | apply RK; kin
      | apply RK; kin | exact Hfd | exact Hfs | exact HEC ] |];
    split; [exact HB|]; split; [exact Hr0|]; split; [lia|];
    split; [rewrite HT', length_app; cbn [length]; lia|];
    split; [rewrite HD'; exact Hd|];
    split; [kqr Q10 10%nat (nm + Z.of_nat j) 1 E10|];
    split; [kqr Q15 15%nat (nm + Z.of_nat j) 1 E15|];
    split; [kqr Q12 12%nat (Z.of_nat t) 1 E12|];
    split; [kqr Q13 13%nat (if d then 1 else 0) 0 E13|];
    split; [rewrite (RK 14%bv ltac:(kin)); exact R14|];
    split; [rewrite (RK 6%bv ltac:(kin)); exact R6|];
    split; [rewrite (RK 18%bv ltac:(kin)); exact R18|];
    split; [rewrite (RK 21%bv ltac:(kin)); exact R21|];
    split; [rewrite (RK 22%bv ltac:(kin)); exact R22|];
    split; [rewrite (RK 24%bv ltac:(kin)); exact R24|];
    split; [rewrite (RK 25%bv ltac:(kin)); exact R25|];
    split; [eapply k_vm_same; [exact KEEPI | exact V136]|];
    split; [eapply k_vm_same; [exact KEEPI | exact V184]|];
    split; [eapply k_bytes_same; [exact KEEPI | exact BNM]|];
    split; [eapply k_bytes_same; [exact KEEPI | exact BTK]|];
    eapply k_bytes_same; [exact KEEPI | exact BDP] ] ).
Qed.

(* ---- the loop: induction on the bytes of the name still to read ----------------------------------------- *)
Lemma k_loop : forall (n j t : nat) (d : bool), (j + n = length (NM g))%nat ->
  forall W2 c2, KLOOP g pos mf nm tk dp j t d W2 c2 -> SRr SEGS W2 c2 (KMID g pos mf nm tk dp).
Proof.
  induction n as [|n IHn]; intros j t d Hjn W2 c2 HC.
  - apply (k_step j t d); [|exact HC].
    intros t' d' W3 c3 HC'. exfalso.
    destruct HC' as (ly3 & S3 & regs3 & mem3 & md3 & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hjx & _)). lia.
  - apply (k_step j t d); [|exact HC].
    intros t' d' W3 c3 HC'. apply (IHn (S j) t' d'); [lia | exact HC'].
Qed.

End d.

(* The cut of LLVMFuzzerTestOneInput_Kcut.v: the loop from its head 0x81f00 to 0x81fa0. *)
Theorem k_token_loop : k_token_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
  intros g pos mf nm tk dp j t d W2 c2 HC.
  assert (Hjl : (j <= length (SlotModel.n_EXP_NM (e_pl g)))%nat).
  { destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hx & _)). exact Hx. }
  apply (k_loop g pos mf nm tk dp (length (SlotModel.n_EXP_NM (e_pl g)) - j)%nat j t d ltac:(lia) W2 c2 HC).
Qed.

End c.
End b.
End a.
