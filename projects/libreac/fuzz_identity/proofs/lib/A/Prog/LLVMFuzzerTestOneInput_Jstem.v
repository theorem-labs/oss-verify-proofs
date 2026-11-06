(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* The stem copy loop of segment J of LLVMFuzzerTestOneInput's ASan walk, 0x81b00 (BASE + 0x13f4) ..
   0x81b60 (BASE + 0x1454): j_stem_loop_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_Jcut.v.

   One iteration, with i bytes already in exp_nm:
     0x81b00 .. 0x81b0c  the shadow test of a1 = exp_nm + i
     0x81b10             a4 := a2 + s9 = stem + 1 + i
     0x81b14             sb a3,4(a0): the byte a3 = stem[i] at a0 + 4 = exp_nm + i
     0x81b18 .. 0x81b24  the shadow test of a4
     0x81b28             a3 := stem[1 + i]
     0x81b2c .. 0x81b34  a1++, a0++, s9++
     0x81b38             bnez a3: the next byte, else 0x81b3c jumps to 0x81b60
   The two slow paths (0x81b40, 0x81b4c) are the partial-granule shadow tests, which the engine's token layer
   takes; the __asan_report_load1 block at 0x81b5c is unreachable, because the stem's shadow
   (range_addressable) and exp_nm's (zero_shadow) make every byte the loop touches addressable.

   The symbolic state at the head (ss_js) carries two regions: the stem byte at atom 32 = stem + 1 + i, whose
   value is atom 33, and the one byte of exp_nm the iteration writes, at atom 10 + 4 = exp_nm + i. The alias
   (a2 + s9 = atom 32) is what lets the engine read the loaded byte off the first region. SH_js holds one
   window entry for exp_nm's byte with reversed bounds: it carries no shadow range, only the apartness of the
   written byte from the shadow band, which is where `in_app nmA 32` of the statement is used (YCbq's
   shent_app_of_app). The proof is an induction on the bytes the loop has still to copy. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame YC1g YC1h YC45 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the shadow arithmetic of
   this loop needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the loop's symbolic state ------------------------------------------------------------------------- *)
Definition JS_head : Z := 0x13f4.
Definition JS_exit : Z := 0x1454.
(* a7 (atom 17) holds the shadow base through the whole loop. *)
Definition js_Bx : sv := SOff 17 0.
Definition js_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* atom 32 = stem + 1 + i (the byte the iteration loads, atom 33 is its value);
   atom 10 + 4 = exp_nm + i (the byte it writes). *)
Definition js_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
    YP09.mkRegion (Some 10%nat) 4 5 4 5 [] ].
Definition js_facts : facts :=
  mkFacts [ (17%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (13%nat, mkAF 1 255 0); (33%nat, mkAF 0 255 0);
            (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (10%nat, mkAF 4092 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] []
    [ (SAlu ALU_ADD (SOff 12 0) (SOff 25 0), SOff 32 0) ].
Definition ss_js : sstate := mkSS JS_head sr_atoms js_regions None js_facts.
(* The window entry of the written byte: reversed bounds, so it carries only app_apart. *)
Definition SH_js : list shent := [mkSHE 10 5 4].
(* The registers the loop never writes, as the statement lists them. *)
Definition JS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.

(* ---- generic facts ------------------------------------------------------------------------------------- *)
Lemma js_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma js_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma js_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma js_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma js_bz : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma js_byte_of_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold RcIdentModel.bz. apply Z_to_bv_bv_unsigned. Qed.
Lemma js_nth_map : forall (l : list byte) j, nth j (map (fun b : byte => bv_unsigned b) l) 0 = bz (nthb l j).
Proof.
  unfold RcIdentModel.nthb, RcIdentModel.bz.
  intros l; induction l as [|x l IH]; intros [|j]; cbn [map nth]; first [ apply IH | reflexivity ].
Qed.
Lemma js_nth_tail : forall (l : list byte), nthb (l ++ [zb 0]) (length l) = zb 0.
Proof.
  intros l. unfold RcIdentModel.nthb. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma js_nth_head : forall (l : list byte) j, (j < length l)%nat -> nthb (l ++ [zb 0]) j = nthb l j.
Proof. intros l j Hj. unfold RcIdentModel.nthb. apply app_nth1. exact Hj. Qed.
(* A byte of the memory, as the reader and as the engine see it. *)
Lemma js_aview_of : forall (W : world SEGS) m a (b : byte),
  mbyte SEGS (mrestrict (w_H W) m) a = Some b -> aview SEGS (w_H W) m a = Some (bz b).
Proof. intros W m a b H. unfold aview. rewrite H. reflexivity. Qed.
Lemma js_vm1 : forall m a v, 0 <= v < 256 -> val_mem SEGS m a 1 v -> mbyte SEGS m a = Some (Z_to_bv 8 v).
Proof.
  intros m a v Hv H. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0. f_equal.
  rewrite le_byte_small by (first [change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia]).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* A one-byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma js_val1 : forall E ss ms r n off e v,
  st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 8 ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E n) + off) = Some (Z_to_bv 8 v).
Proof.
  intros E ss ms r n off e v HS Hin Hb Hc He Hv.
  pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [base_val] in Hcs.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
  pose proof (val_of_chunk_ok SEGS E (ms_mem ms) _ off 1 e v Hck He Hv ltac:(lia) 0%nat ltac:(cbn; lia)) as Hvm.
  rewrite Z.add_0_r in Hvm. rewrite Hvm. f_equal.
  rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* A shadow byte is never a byte of the application. *)
Lemma js_shadow_ne : forall x a, 0 <= x < 2 ^ 47 -> app_addr a -> shadow_of_addr SHADOW_OFF x <> a.
Proof.
  intros x a Hx Ha. unfold shadow_of_addr.
  assert (Hd : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* What the runs so far kept and the presence they kept. *)
Definition js_kept (W : world SEGS) (Zs : Z -> Prop) (m0 m1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Definition js_grown (W : world SEGS) (m0 m1 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m0 a -> apresent (w_H W) m1 a.
Lemma js_keep_step : forall Ex rs (W : world SEGS) m0 m1 m2 (Zs : Z -> Prop),
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  js_kept W Zs m0 m1 -> js_grown W m0 m1 ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> Zs a) ->
  js_kept W Zs m0 m2 /\ js_grown W m0 m2.
Proof.
  intros Ex rs W m0 m1 m2 Zs HFr HG K1 G1 Hw. split.
  - intros a Ha Hz. rewrite <- (K1 a Ha Hz). exact (kept_of_frame Ex rs (w_H W) m1 m2 Zs HFr Hw a Ha Hz).
  - intros a Hp. exact (apresent_grows _ _ _ a HG (G1 a Hp)).
Qed.
Lemma js_kept_regs : forall E ss ms (regsL : bvmap 5 word) extra,
  st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsL extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) JS_KEPT = true ->
  forall r, In r JS_KEPT -> getr (ms_regs ms) r = getr regsL r.
Proof.
  intros E ss ms regsL extra HS HAE Hl r Hr.
  exact (regs_kept_of_st_ok_pi _ _ _ _ _ JS_KEPT HS HAE Hl r Hr).
Qed.
Lemma js_agree_ext : forall regsL extra E E',
  env_agree 32 (Ereg regsL extra) E -> env_agree 32 E E' -> env_agree 32 (Ereg regsL extra) E'.
Proof.
  intros regsL extra E E' [H1 H2] [H3 H4]. split.
  - intros n Hn. rewrite (H3 n Hn). exact (H1 n Hn).
  - rewrite H4. exact H2.
Qed.
End b.
End a.

(* ---- tactics ------------------------------------------------------------------------------------------- *)
(* Drop the hypotheses lia must not preprocess. *)
Ltac jclean :=
  repeat match goal with
  | H : st_ok_pi _ _ _ _ _ |- _ => clear H
  | H : st_ok _ _ _ _ |- _ => clear H
  | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
  | H : sh_ok _ _ _ _ _ |- _ => clear H
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  | H : img_env _ _ _ |- _ => clear H
  | H : env_agree _ _ _ |- _ => clear H
  | H : AR _ _ _ _ _ _ _ |- _ => clear H
  | H : SRr _ _ _ _ |- _ => clear H
  | H : garr8 _ _ _ _ |- _ => clear H
  | H : forall _ : Z, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  | H : forall _ : word, _ |- _ => clear H
  end.
Ltac jlia := jclean; lia.
Ltac ewo := repeat rewrite ew_ewset_other by lia.
Ltac ewo_in H := repeat rewrite ew_ewset_other in H by lia.
(* A register of the symbolic state, as the symbolic value's denotation. *)
Ltac jsreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* The windows of a run lie in the one byte the iteration writes. *)
Ltac jwins U10 :=
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wl wh aa Hin Hr;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; cbn [base_val] in Hr; ewo_in Hr; rewrite ?U10 in Hr; jclean; lia | ]);
  destruct Hin.
(* After a run: chain its frame onto KEEPI / GROWI. *)
Ltac jkeep U10 :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _,
    KI : js_kept _ _ _ _, GI : js_grown _ _ _ |- _ =>
      let Hw := fresh "Hw" in
      pose proof (js_keep_step _ _ _ _ _ _ _ HFr HG KI GI) as Hw;
      let K2 := fresh "K2" in let G2 := fresh "G2" in
      lazymatch type of Hw with ?P -> _ =>
        let HP := fresh "HP" in assert (HP : P) by (jwins U10);
        destruct (Hw HP) as [K2 G2]; clear HP Hw end;
      clear KI GI HFr HG; rename K2 into KEEPI; rename G2 into GROWI
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* The writable window of a run: the one byte of exp_nm, which the caller's journal allows. *)
Ltac jawr U10 WR :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
    | eapply awr_ok_cons_gen;
        [ reflexivity | cbn [YP09.r_base]; ewo; exact U10
        | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; apply (proj1 (WR a ltac:(jclean; lia)))
        | ] ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Section loop.
Variables (STK sp0 : Z) (FP own : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (W : world SEGS) (k : Z)
  (nmA stemA : Z) (s : list byte).
Hypothesis Hs16 : (length s <= 16)%nat.
Hypothesis Hnz : forall j, (j < length s)%nat -> bz (nthb s j) <> 0.
(* the destination is application memory: this is what keeps it out of the shadow band (SH_js). *)
Hypothesis HAnm : in_app nmA 32.
Hypothesis Hnm0 : 4096 <= nmA.
Hypothesis Hnm1 : nmA + 32 <= alloc_ceiling.
Hypothesis Hnm8 : nmA mod 8 = 0.
Hypothesis Hst0 : 4096 <= stemA.
Hypothesis Hst1 : stemA + Z.of_nat (length s) + 1 <= alloc_ceiling.
Hypothesis Hsep : stemA + Z.of_nat (length s) + 1 <= nmA \/ nmA + 32 <= stemA.

(* The geometry the loop needs, as plain arithmetic. *)
Lemma js_geo : 0 <= Z.of_nat (length s) <= 16 /\ nmA + 32 <= 2 ^ 47 - 1 /\
  stemA + Z.of_nat (length s) + 1 <= 2 ^ 47 - 1.
Proof.
  pose proof asan_consts as (C1 & _). pose proof (Nat2Z.is_nonneg (length s)) as Hn.
  assert (Z.of_nat (length s) <= 16) by lia. lia.
Qed.

(* A byte of the stem, from the array the caller gives. *)
Lemma js_stem_vm : forall m j, (j < length s + 1)%nat ->
  garr8 SEGS m stemA (map (fun b : byte => bv_unsigned b) (s ++ [zb 0])) ->
  val_mem SEGS m (stemA + Z.of_nat j) 1 (bz (nthb (s ++ [zb 0]) j)).
Proof.
  intros m j Hj GA.
  assert (Hl : length (map (fun b : byte => bv_unsigned b) (s ++ [zb 0])) = (length s + 1)%nat)
    by (rewrite length_map, length_app; cbn [length]; lia).
  destruct (GA j ltac:(lia)) as [Hv _]. rewrite js_nth_map in Hv. exact Hv.
Qed.

(* Every byte of exp_nm and every byte of the stem is an application byte, so no shadow cell of either is
   the byte the iteration writes. *)
Lemma js_nm_app : forall a, nmA <= a < nmA + 32 -> app_addr a.
Proof. intros a Ha. exact (in_app_addr nmA 32 a HAnm Ha). Qed.

Definition js_post (regsL : bvmap 5 word) (memL : word -> option byte) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regsF memF mdF,
    c' = cfg_at SEGS (BASE + JS_exit) regsF memF mdF /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k /\
    (forall r : bv 5, In r JS_KEPT -> getr regsF r = getr regsL r) /\
    getr regsF 25 = w64 (Z.of_nat (length s)) /\
    getr regsF 10 = w64 (nmA + Z.of_nat (length s) - 4) /\
    (forall j, (j < length s)%nat -> aview SEGS (w_H W) memF (nmA + Z.of_nat j) = Some (bz (nthb s j))) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (nmA <= a < nmA + Z.of_nat (length s)) ->
       aview SEGS (w_H W) memF a = aview SEGS (w_H W) memL a) /\
    (forall a, apresent (w_H W) memL a -> apresent (w_H W) memF a).

(* ---- the loop: induction on the bytes still to copy ----------------------------------------------------- *)
Lemma js_loop : forall (n i : nat) regsL memL mdL,
  (i + n = length s)%nat -> (0 < n)%nat ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k ->
  getr regsL 17 = w64 SHADOW_OFF ->
  getr regsL 11 = w64 (nmA + Z.of_nat i) ->
  getr regsL 10 = w64 (nmA + Z.of_nat i - 4) ->
  getr regsL 12 = w64 (stemA + 1) ->
  getr regsL 25 = w64 (Z.of_nat i) ->
  getr regsL 13 = w64 (bz (nthb s i)) ->
  garr8 SEGS (mrestrict (w_H W) memL) stemA (map (fun b : byte => bv_unsigned b) (s ++ [zb 0])) ->
  range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF stemA (Z.of_nat (length s) + 1) ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 ->
  jcut_wr B STK sp0 FP ly S lyc Sc own W memL nmA 32 ->
  (forall j, (j < i)%nat -> aview SEGS (w_H W) memL (nmA + Z.of_nat j) = Some (bz (nthb s j))) ->
  SRr SEGS W (cfg_at SEGS (BASE + JS_head) regsL memL mdL) (js_post regsL memL).
Proof.
  induction n as [|n IH]; intros i regsL memL mdL Hin Hn HJ R17 R11 R10 R12 R25 R13 GA RA ZS WR CP; [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct js_geo as (Hs0 & Hgnm & Hgst).
  assert (Hi : (i < length s)%nat) by lia.
  assert (Hiz : 0 <= Z.of_nat i < Z.of_nat (length s)) by lia.
  assert (WRa : forall a, nmA <= a < nmA + 32 ->
            awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memL a)
    by exact WR.
  set (bcur := nthb s i).
  set (bnext := nthb (s ++ [zb 0]) (1 + i)).
  pose proof (js_bz bcur) as Hbc. pose proof (js_bz bnext) as Hbn.
  assert (Hbc0 : bz bcur <> 0) by (subst bcur; apply Hnz; lia).
  remember (Eimg (Ereg regsL [w64 (stemA + 1 + Z.of_nat i); w64 (bz bnext)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall m, (m < A_TEXT)%nat ->
            ew E m = ew (Ereg regsL [w64 (stemA + 1 + Z.of_nat i); w64 (bz bnext)]) m)
    by (intros m Hm; subst E; apply Eimg_low; exact Hm).
  assert (E10 : ew E 10 = w64 (nmA + Z.of_nat i - 4))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E11 : ew E 11 = w64 (nmA + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 11 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = w64 (stemA + 1))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (bz bcur))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 13 13%bv eq_refl); exact R13).
  assert (E17 : ew E 17 = w64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E25 : ew E 25 = w64 (Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = w64 (stemA + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (bz bnext))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (HAE : env_agree 32 (Ereg regsL [w64 (stemA + 1 + Z.of_nat i); w64 (bz bnext)]) E)
    by (split; [intros m Hm; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (U10 : bv_unsigned (ew E 10) = nmA + Z.of_nat i - 4)
    by (rewrite E10; apply js_unsigned; lia).
  assert (U32 : bv_unsigned (ew E 32) = stemA + 1 + Z.of_nat i)
    by (rewrite E32; apply js_unsigned; lia).
  assert (VB : forall m v, ew E m = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
    by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply js_unsigned; exact Hv).
  (* the byte the iteration reads *)
  assert (Mq : mbyte SEGS (mrestrict (w_H W) memL) (stemA + 1 + Z.of_nat i) = Some (Z_to_bv 8 (bz bnext))).
  { apply js_vm1; [lia|].
    replace (stemA + 1 + Z.of_nat i) with (stemA + Z.of_nat (1 + i)) by lia.
    exact (js_stem_vm _ (1 + i)%nat ltac:(lia) GA). }
  (* the state at the head *)
  assert (HS : st_ok_pi SEGS VAL E ss_js
                 (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + JS_head)) memL (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_js. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold js_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      + rewrite (VB 32%nat (stemA + 1 + Z.of_nat i) E32) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (stemA + 1 + Z.of_nat i) 0 1 (SOff 33 0) (bz bnext)).
        * apply js_sv. rewrite (js_U E 33 _ 0 E33), Z.add_0_r. reflexivity.
        * change (2 ^ (8 * Z.of_N 1)) with 256. exact Hbn.
        * cbn. lia.
        * change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
          replace (stemA + 1 + Z.of_nat i) with (stemA + Z.of_nat (1 + i)) by lia.
          exact (js_stem_vm _ (1 + i)%nat ltac:(lia) GA).
      + rewrite (VB 10%nat (nmA + Z.of_nat i - 4) E10) by lia.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS).
        exact (proj2 (WRa (nmA + Z.of_nat i - 4 + o) ltac:(lia))).
    - apply pairwise_disjoint_of_extents. unfold js_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 32%nat (stemA + 1 + Z.of_nat i) E32) by lia.
      rewrite (VB 10%nat (nmA + Z.of_nat i - 4) E10) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. jclean. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [js_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E10, E11, E13, E17, E32, E33. rewrite !js_unsigned by (unfold SHADOW_OFF; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. jclean. unfold SHADOW_OFF. repeat split; lia.
      + cbn [js_facts f_alias alias_ok]. split; [|exact I].
        apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (js_U E 12 (stemA + 1) 0 E12), (js_U E 25 (Z.of_nat i) 0 E25).
        rewrite (js_U E 32 (stemA + 1 + Z.of_nat i) 0 E32). rewrite !Z.add_0_r.
        rewrite (Z.mod_small (stemA + 1)) by lia. rewrite (Z.mod_small (Z.of_nat i)) by lia.
        unfold zcanon, M64. f_equal; lia. }
  assert (SHOK : sh_ok SEGS js_Bx SH_js E (mrestrict (w_H W) memL)).
  { unfold sh_ok, SH_js. apply Forall_cons; [|apply Forall_nil].
    apply (shent_app_of_app SEGS E js_Bx 10%nat (nmA + Z.of_nat i - 4) 4 5).
    - unfold js_Bx. rewrite (js_U E 17 SHADOW_OFF 0 E17), Z.add_0_r.
      apply Z.mod_small. unfold SHADOW_OFF. lia.
    - rewrite (js_U E 10 (nmA + Z.of_nat i - 4) 0 E10), Z.add_0_r. apply Z.mod_small. lia.
    - destruct HAnm as [Ha1 [Ha2 | [Ha2 Ha3]]];
        [left | right]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
    - lia. }
  assert (KEEPI : js_kept W (fun a => a = nmA + Z.of_nat i) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : js_grown W memL memL) by (intros a Ha; exact Ha).
  (* 0x81b00 .. 0x81b38: the two shadow tests, the store, the load, the counters *)
  paj_run_tok RUN HS HJ SHOK js_Bspan;
    [ (* the stem byte is addressable *)
      cbn [ms_mem mkst restrict]; unfold js_Bx;
      rewrite <- (aview_rd_of SEGS (w_H W) memL);
      rewrite (js_U E 17 SHADOW_OFF 0 E17), (js_U E 32 (stemA + 1 + Z.of_nat i) 0 E32), !Z.add_0_r;
      rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia);
      rewrite (Z.mod_small (stemA + 1 + Z.of_nat i)) by lia;
      apply (range_addressable_sub _ _ stemA (Z.of_nat (length s) + 1)); [exact RA | lia | lia]
    | (* the exp_nm byte is addressable *)
      cbn [ms_mem mkst restrict]; unfold js_Bx;
      rewrite <- (aview_rd_of SEGS (w_H W) memL);
      rewrite (js_U E 17 SHADOW_OFF 0 E17), (js_U E 11 (nmA + Z.of_nat i) 0 E11), !Z.add_0_r;
      rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia);
      rewrite (Z.mod_small (nmA + Z.of_nat i)) by lia;
      apply (range_addressable_sub _ _ nmA 32); [apply zero_shadow_range; [exact Hnm8 | reflexivity | exact ZS] | lia | lia]
    | jawr U10 WRa
    | ].
  jkeep U10.
  psrr_branch_tok RUN BR HS SHOK js_Bspan.
  - (* stem[1 + i] <> 0: the next iteration *)
    assert (Hb0 : bz bnext <> 0).
    { rewrite branch_ne_U in Hc. rewrite (js_U _ 33%nat (bz bnext) 0) in Hc by (ewo; exact E33).
      rewrite js_Ulit in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      rewrite Z.add_0_r, (Z.mod_small (bz bnext)) in Hc by lia. lia. }
    clear Hc.
    assert (HSi : (Datatypes.S i < length s)%nat).
    { destruct (Nat.lt_ge_cases (Datatypes.S i) (length s)) as [H | H]; [exact H|].
      exfalso. apply Hb0. subst bnext. replace (1 + i)%nat with (length s) by lia.
      rewrite js_nth_tail. reflexivity. }
    assert (Hbs : bnext = nthb s (Datatypes.S i)) by (subst bnext; rewrite js_nth_head by lia; f_equal; lia).
    paj_run_to_tok RUNTO HS HJ SHOK js_Bspan JS_head; [jawr U10 WRa|].
    jkeep U10.
    pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
      rename ms into msF;
      jsreg HS (10%bv : bv 5) Q10; jsreg HS (11%bv : bv 5) Q11; jsreg HS (12%bv : bv 5) Q12;
      jsreg HS (13%bv : bv 5) Q13; jsreg HS (17%bv : bv 5) Q17; jsreg HS (25%bv : bv 5) Q25;
      pose proof (js_val1 _ _ _ (YP09.mkRegion (Some 10%nat) 4 5 4 5 [YP09.mkChunk 4 (CVal 1 (SOff 13 0))])
                    10%nat 4 (SOff 13 0) (bz bcur) HS
                    ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                    ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                    ltac:(apply js_sv; rewrite (js_U _ 13%nat (bz bcur) 0) by (ewo; exact E13);
                          rewrite Z.add_0_r; reflexivity)
                    ltac:(change (2 ^ 8) with 256; exact Hbc)) as Md;
      cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U10 in Md;
      assert (HAEx : env_agree 32 (Ereg regsL [w64 (stemA + 1 + Z.of_nat i); w64 (bz bnext)]) Ex)
        by (eapply js_agree_ext; [exact HAE | split; [intros nn Hnn; ewo; reflexivity | reflexivity]]);
      pose proof (js_kept_regs _ _ _ regsL _ HS HAEx ltac:(vm_compute; reflexivity)) as RK1
    end.
    assert (MdA : aview SEGS (w_H W) (ms_mem msF) (nmA + Z.of_nat i) = Some (bz bcur)).
    { replace (nmA + Z.of_nat i) with (nmA + Z.of_nat i - 4 + 4) by lia.
      apply js_aview_of. rewrite Md. f_equal. apply js_byte_of_bz. }
    (* the facts the next iteration takes *)
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> nmA + Z.of_nat i ->
              aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memL a)
      by (intros a Ha Hne; apply KEEPI; [exact Ha | exact Hne]).
    assert (KSH : forall x, 0 <= x < 2 ^ 47 ->
              aview SEGS (w_H W) (ms_mem msF) (shadow_of_addr SHADOW_OFF x)
              = aview SEGS (w_H W) memL (shadow_of_addr SHADOW_OFF x)).
    { intros x Hx. apply KA.
      - unfold shadow_of_addr, SHADOW_OFF.
        assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
      - apply js_shadow_ne; [lia | apply js_nm_app; lia]. }
    eapply SRr_mono;
      [ apply (IH (Datatypes.S i) (ms_regs msF) (ms_mem msF) _ ltac:(lia) ltac:(lia)); try assumption | ].
    + rewrite Q17. apply js_sv. rewrite (js_U _ 17%nat SHADOW_OFF 0) by (ewo; exact E17).
      rewrite Z.add_0_r. reflexivity.
    + rewrite Q11. apply js_sv. rewrite (js_U _ 11%nat (nmA + Z.of_nat i) 1) by (ewo; exact E11).
      f_equal; lia.
    + rewrite Q10. apply js_sv. rewrite (js_U _ 10%nat (nmA + Z.of_nat i - 4) 1) by (ewo; exact E10).
      f_equal; lia.
    + rewrite Q12. apply js_sv. rewrite (js_U _ 12%nat (stemA + 1) 0) by (ewo; exact E12).
      f_equal; lia.
    + rewrite Q25. apply js_sv. rewrite (js_U _ 25%nat (Z.of_nat i) 1) by (ewo; exact E25).
      f_equal; lia.
    + rewrite Q13. apply js_sv. rewrite (js_U _ 33%nat (bz bnext) 0) by (ewo; exact E33).
      rewrite Z.add_0_r, Hbs. reflexivity.
    + (* the stem bytes are untouched *)
      intros j Hj.
      assert (Hl : length (map (fun b : byte => bv_unsigned b) (s ++ [zb 0])) = (length s + 1)%nat)
        by (rewrite length_map, length_app; cbn [length]; lia).
      destruct (GA j ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
      intros kk Hkk. assert (kk = 0%nat) as -> by lia.
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memL (ms_mem msF) (stemA + Z.of_nat j + Z.of_nat 0)).
      * exact (Hv 0%nat ltac:(lia)).
      * apply KA; [lia|]. jclean. lia.
    + (* the stem's shadow is untouched *)
      intros x Hx. rewrite (KSH x ltac:(lia)). exact (RA x Hx).
    + (* exp_nm's shadow is untouched *)
      intros j Hj.
      replace (shadow_of_addr SHADOW_OFF nmA + j) with (shadow_of_addr SHADOW_OFF (nmA + 8 * j))
        by (rewrite (shadow_of_addr_aligned_off SHADOW_OFF nmA (8 * j) Hnm8); unfold shadow_of_addr;
            rewrite Z.mul_comm, Z.div_mul by lia; lia).
      rewrite (KSH (nmA + 8 * j) ltac:(lia)).
      replace (shadow_of_addr SHADOW_OFF (nmA + 8 * j)) with (shadow_of_addr SHADOW_OFF nmA + j)
        by (rewrite (shadow_of_addr_aligned_off SHADOW_OFF nmA (8 * j) Hnm8); unfold shadow_of_addr;
            rewrite Z.mul_comm, Z.div_mul by lia; lia).
      exact (ZS j Hj).
    + (* the journal still allows the destination, and its bytes are still there *)
      intros a Ha. split; [exact (proj1 (WRa a Ha)) | apply GROWI; exact (proj2 (WRa a Ha))].
    + (* the bytes copied so far *)
      intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne]; [exact MdA|].
      rewrite (KA (nmA + Z.of_nat j) ltac:(lia) ltac:(jclean; lia)). apply CP. lia.
    + (* the post of the next iteration is this one's *)
      intros W' c' _ (-> & regsF & memF & mdF & -> & HJF & RKF & R25F & R10F & BYF & KPF & GRF).
      split; [reflexivity|]. exists regsF, memF, mdF.
      split; [reflexivity|]. split; [exact HJF|].
      split; [intros r Hr; rewrite (RKF r Hr); exact (RK1 r Hr)|].
      split; [exact R25F|]. split; [exact R10F|]. split; [exact BYF|].
      split.
      * intros a Ha Hna. rewrite (KPF a Ha Hna). apply KA; [exact Ha | jclean; lia].
      * intros a Hp. apply GRF. apply GROWI. exact Hp.
  - (* stem[1 + i] = 0: the loop is done *)
    assert (Hb0 : bz bnext = 0).
    { rewrite branch_ne_U in Hc. rewrite (js_U _ 33%nat (bz bnext) 0) in Hc by (ewo; exact E33).
      rewrite js_Ulit in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      rewrite Z.add_0_r, (Z.mod_small (bz bnext)) in Hc by lia. lia. }
    clear Hc.
    assert (HSi : (Datatypes.S i = length s)%nat).
    { destruct (Nat.lt_ge_cases (Datatypes.S i) (length s)) as [H | H]; [|lia].
      exfalso. apply (Hnz (Datatypes.S i) H). subst bnext.
      rewrite js_nth_head in Hb0 by lia.
      replace (1 + i)%nat with (Datatypes.S i) in Hb0 by lia. exact Hb0. }
    paj_run_to_tok RUNTO HS HJ SHOK js_Bspan JS_exit; [jawr U10 WRa|].
    jkeep U10.
    pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
      rename ms into msF;
      jsreg HS (10%bv : bv 5) Q10; jsreg HS (25%bv : bv 5) Q25;
      pose proof (js_val1 _ _ _ (YP09.mkRegion (Some 10%nat) 4 5 4 5 [YP09.mkChunk 4 (CVal 1 (SOff 13 0))])
                    10%nat 4 (SOff 13 0) (bz bcur) HS
                    ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                    ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                    ltac:(apply js_sv; rewrite (js_U _ 13%nat (bz bcur) 0) by (ewo; exact E13);
                          rewrite Z.add_0_r; reflexivity)
                    ltac:(change (2 ^ 8) with 256; exact Hbc)) as Md;
      cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U10 in Md;
      assert (HAEx : env_agree 32 (Ereg regsL [w64 (stemA + 1 + Z.of_nat i); w64 (bz bnext)]) Ex)
        by (eapply js_agree_ext; [exact HAE | split; [intros nn Hnn; ewo; reflexivity | reflexivity]]);
      pose proof (js_kept_regs _ _ _ regsL _ HS HAEx ltac:(vm_compute; reflexivity)) as RK1
    end.
    assert (MdA : aview SEGS (w_H W) (ms_mem msF) (nmA + Z.of_nat i) = Some (bz bcur)).
    { replace (nmA + Z.of_nat i) with (nmA + Z.of_nat i - 4 + 4) by lia.
      apply js_aview_of. rewrite Md. f_equal. apply js_byte_of_bz. }
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> nmA + Z.of_nat i ->
              aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memL a)
      by (intros a Ha Hne; apply KEEPI; [exact Ha | exact Hne]).
    apply SRr_ret. split; [reflexivity|].
    eexists (ms_regs msF), (ms_mem msF), _.
    split; [reflexivity|].
    split; [exact HJ|].
    split; [exact RK1|].
    split.
    { rewrite Q25. apply js_sv. rewrite (js_U _ 25%nat (Z.of_nat i) 1) by (ewo; exact E25).
      f_equal; lia. }
    split.
    { rewrite Q10. apply js_sv. rewrite (js_U _ 10%nat (nmA + Z.of_nat i - 4) 1) by (ewo; exact E10).
      f_equal; lia. }
    split.
    { intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne]; [exact MdA|].
      rewrite (KA (nmA + Z.of_nat j) ltac:(lia) ltac:(jclean; lia)). apply CP. lia. }
    split.
    { intros a Ha Hna. apply KA; [exact Ha | jclean; lia]. }
    { intros a Hp. apply GROWI. exact Hp. }
Qed.
End loop.

(* ---- the cut's statement --------------------------------------------------------------------------------- *)
Theorem j_stem_loop : j_stem_loop_stmt B.
Proof.
  unfold j_stem_loop_stmt.
  intros STK sp0 FP own ly S W0 mem0 md0 lyc Sc W k nmA stemA s i regsL memL mdL
    HJ R3 R4 R17 R11 R10 R12 R25 R13 Hi Hs16 Hnz GA RA TP ZS WR CP HAnm HAst Hnm0 Hnm1 Hnm8 Hst0 Hst1 Hsep.
  exact (js_loop STK sp0 FP own ly S W0 mem0 md0 lyc Sc W k nmA stemA s Hs16 Hnz HAnm
           Hnm0 Hnm1 Hnm8 Hst0 Hst1 Hsep (length s - i)%nat i regsL memL mdL
           ltac:(lia) ltac:(lia) HJ R17 R11 R10 R12 R25 R13 GA RA ZS WR CP).
Qed.
End f.
End e.
End d.
