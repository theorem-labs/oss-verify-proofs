(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* The exp_nm -> exp_dp copy loop of segment J of LLVMFuzzerTestOneInput's ASan walk, 0x81c48 (BASE + 0x153c)
   .. 0x81ca0 (BASE + 0x1594): j_dp_loop_stmt of LLVMFuzzerTestOneInput_Jcut.v.
     0x81c48 a1 := s8 + a2 = dp + ld + j     0x81c4c .. 0x81c58 the shadow test of a1 (slow path 0x81c88)
     0x81c5c sb a4,0(a1)                      0x81c60 .. 0x81c6c the shadow test of a0 = nm + 1 + j (slow path 0x81c94)
     0x81c70 a4 := exp_nm[1 + j]              0x81c74 .. 0x81c7c a0++, a3++, a2++
     0x81c80 bnez a4: the next byte (0x81c48), else 0x81c84 j 0x81ca0
   One iteration is one run of the engine from the head to the bnez, the branch, and one run to the head or to
   the exit. The shadow test of the destination is covered by the shadow entry of atom 32 (the destination, an
   application byte by in_app dpA 64, so the store never writes a shadow cell); the test of the source leaves the
   obligation range_addressable nm + 1 + j, which zero_shadow of exp_nm gives. The loop is an induction on the
   bytes still to copy. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame YC1g YC1h YC45 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow-cell arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the symbolic state at the loop head 0x81c48 ------------------------------------------------------------ *)
(* a7 (atom 17) holds the shadow base. Atom 32 is the destination dp + ld + j (the alias says it is s8 + a2),
   atom 33 the source byte exp_nm[1 + j] that a3 (atom 13) points at, a4 (atom 14) the byte being stored. *)
Definition SB_D : Z := 0x7fff8000.
Definition Bx_D : sv := SOff 17 0.
Definition Bspan_D : Z * Z := (SB_D, SB_D + 2 ^ 44 - 1).
Definition jd_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition jd_facts : facts :=
  mkFacts [ (17%nat, mkAF SB_D SB_D 0); (10%nat, mkAF 4096 (2 ^ 47 - 64) 0); (13%nat, mkAF 4096 (2 ^ 47 - 64) 0);
            (12%nat, mkAF 0 63 0); (24%nat, mkAF 4096 (2 ^ 47 - 128) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 64) 0); (14%nat, mkAF 1 255 0); (33%nat, mkAF 0 255 0) ] []
    [ (SAlu ALU_ADD (SOff 24 0) (SOff 12 0), SOff 32 0) ].
Definition ss_jd : sstate := mkSS 0x153c sr_atoms jd_regions None jd_facts.
Definition SH_jd : list shent := [mkSHE 32 0 1].
(* The registers the loop does not write. *)
Definition JD_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- tactics ------------------------------------------------------------------------------------------------- *)
(* Drop the hypotheses lia must not preprocess (the symbolic states, the journals, the quantified facts). *)
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
  | H : SRr _ _ _ _ |- _ => clear H
  | H : forall _ : Z, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  | H : forall _ : word, _ |- _ => clear H
  | H : forall _ : bv 5, _ |- _ => clear H
  end.
Ltac jlia := jclean; lia.
Ltac jewo := repeat rewrite ew_ewset_other by lia.
Ltac jewo_in H := repeat rewrite ew_ewset_other in H by lia.
(* A register of the symbolic state, kept as the symbolic value's denotation. *)
Ltac jd_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

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

(* ---- generic facts ------------------------------------------------------------------------------------------- *)
Lemma jd_w64 : forall z, w64 z = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma jd_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H, jd_w64, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma jd_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma jd_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H, jd_w64, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma jd_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. rewrite jd_w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma jd_bz : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma jd_byte_of_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold RcIdentModel.bz. apply Z_to_bv_bv_unsigned. Qed.
Lemma jd_nthb_app : forall (s : list byte) j, (j <= length s)%nat -> nthb (s ++ [zb 0]) j = nthb s j.
Proof.
  intros s j Hj. unfold RcIdentModel.nthb. destruct (Nat.lt_ge_cases j (length s)) as [Hl | Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (j = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
    cbn [nth]. rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma jd_nthb_end : forall (s : list byte), bz (nthb s (length s)) = 0.
Proof. intros s. unfold RcIdentModel.nthb. rewrite nth_overflow by lia. reflexivity. Qed.
(* The byte garr8 of the NUL-terminated string gives at index i <= |s|. *)
Lemma jd_nth_src : forall (s : list byte) i, (i <= length s)%nat ->
  nth i (map bv_unsigned (s ++ [zb 0])) 0 = bz (nthb s i).
Proof.
  intros s i Hi. rewrite <- (jd_nthb_app s i Hi). clear Hi. unfold RcIdentModel.nthb, RcIdentModel.bz.
  generalize (s ++ [zb 0]). intros l. revert l.
  induction i as [|i IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.
Lemma jd_in17 : In (17%bv : bv 5) JD_KEPT.
Proof. unfold JD_KEPT. do 5 right. left. reflexivity. Qed.
Lemma jd_in24 : In (24%bv : bv 5) JD_KEPT.
Proof. unfold JD_KEPT. do 12 right. left. reflexivity. Qed.
(* A one-byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma jd_val1 : forall E ss ms r n off e v,
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
Lemma jd_garr8_moved : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W) m' (a + k) = aview SEGS (w_H W) m (a + k)) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
  intros W m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
  intros i Hi. replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hk. cbn in Hi. lia.
Qed.
Lemma jd_zs_moved : forall (W : world SEGS) (m m' : word -> option byte) a n,
  (forall i, 0 <= i < n / 8 -> aview SEGS (w_H W) m' (shadow_of_addr SHADOW_OFF a + i) =
                              aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF a + i)) ->
  zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> zero_shadow (aview SEGS (w_H W) m') SHADOW_OFF a n.
Proof. intros W m m' a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
(* What the runs so far kept (KEEPI) and the presence they kept (GROWI). *)
Definition jd_kept (W : world SEGS) (d : Z) (m0 m1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> a <> d -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Definition jd_grown (W : world SEGS) (m0 m1 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m0 a -> apresent (w_H W) m1 a.
Lemma jd_keep_step : forall Ex rs (W : world SEGS) m0 m1 m2 d,
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  jd_kept W d m0 m1 -> jd_grown W m0 m1 ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> a = d) ->
  jd_kept W d m0 m2 /\ jd_grown W m0 m2.
Proof.
  intros Ex rs W m0 m1 m2 d HFr HG K1 G1 Hw. split.
  - intros a Ha Hd. rewrite <- (K1 a Ha Hd).
    exact (kept_of_frame Ex rs (w_H W) m1 m2 (fun x => x = d) HFr Hw a Ha Hd).
  - intros a Hp. exact (apresent_grows _ _ _ a HG (G1 a Hp)).
Qed.
Lemma jd_agree_ext : forall regsL extra E E',
  env_agree 32 (Ereg regsL extra) E -> env_agree 32 E E' -> env_agree 32 (Ereg regsL extra) E'.
Proof.
  intros regsL extra E E' [H1 H2] [H3 H4]. split.
  - intros n Hn. rewrite (H3 n Hn). exact (H1 n Hn).
  - rewrite H4. exact H2.
Qed.
Lemma jd_kept_regs : forall E ss ms (regsL : bvmap 5 word) extra,
  st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsL extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) JD_KEPT = true ->
  forall r, In r JD_KEPT -> getr (ms_regs ms) r = getr regsL r.
Proof. intros E ss ms regsL extra HS HAE Hl. exact (regs_kept_of_st_ok_pi E ss ms regsL extra JD_KEPT HS HAE Hl). Qed.

End b.
End a.

(* After a run: chain its frame onto KEEPI / GROWI; every window of the loop is the destination byte. *)
Ltac jd_keep U32 :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _,
    KI : jd_kept _ _ _ _, GI : jd_grown _ _ _ |- _ =>
      let Hw := fresh "Hw" in
      pose proof (jd_keep_step _ _ _ _ _ _ _ HFr HG KI GI) as Hw;
      let K2 := fresh "K2" in let G2 := fresh "G2" in
      lazymatch type of Hw with ?P -> _ =>
        let HP := fresh "HP" in
        assert (HP : P);
        [ let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
          let Hin := fresh "Hin" in let Hr := fresh "Hr" in
          intros bb wl wh aa Hin Hr;
          lazymatch type of Hin with In _ (windows ?rs) =>
            let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
          repeat (destruct Hin as [Hin | Hin];
                  [ injection Hin as <- <- <-; cbn [base_val] in Hr; jewo_in Hr; rewrite ?U32 in Hr; jlia | ]);
          destruct Hin
        | destruct (Hw HP) as [K2 G2]; clear HP Hw ] end;
      clear KI GI HFr HG; rename K2 into KEEPI; rename G2 into GROWI
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

Section a2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b2.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
Section c2.
Variable B : asyms.
(* The engine's soundness: the allocator laws of the contract. *)
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Section loop.
(* The loop's fixed data: the caller's journal, the two buffers, the string, and the memory and registers at the
   first head (m0, regs0). *)
Variables (STK sp0 : Z) (FP own : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (W : world SEGS) (k : Z)
  (nmA dpA ld0 : Z) (s : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte).
Hypothesis R17 : getr regs0 17 = w64 SHADOW_OFF.
Hypothesis R24 : getr regs0 24 = w64 dpA.
Hypothesis HL : (length s <= 21)%nat.
Hypothesis HNZ : forall m, (m < length s)%nat -> bz (nthb s m) <> 0.
Hypothesis HNM : garr8 SEGS (mrestrict (w_H W) m0) nmA (map bv_unsigned (s ++ [zb 0])).
Hypothesis Hld0 : 0 <= ld0.
Hypothesis Hld1 : ld0 + Z.of_nat (length s) <= 63.
Hypothesis ZNM : zero_shadow (aview SEGS (w_H W) m0) SHADOW_OFF nmA 32.
Hypothesis ZDP : zero_shadow (aview SEGS (w_H W) m0) SHADOW_OFF dpA 64.
Hypothesis WR : jcut_wr B STK sp0 FP ly S lyc Sc own W m0 dpA 64.
Hypothesis APN : in_app nmA 32.
Hypothesis APD : in_app dpA 64.
Hypothesis Hn0 : 4096 <= nmA.
Hypothesis Hn1 : nmA + 32 <= alloc_ceiling.
Hypothesis Hn8 : nmA mod 8 = 0.
Hypothesis Hd0 : 4096 <= dpA.
Hypothesis Hd1 : dpA + 64 <= alloc_ceiling.
Hypothesis Hd8 : dpA mod 8 = 0.
Hypothesis Hnd : nmA + 32 <= dpA \/ dpA + 64 <= nmA.

Definition jd_post : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regsF memF mdF,
  c' = cfg_at SEGS (BASE + 0x1594) regsF memF mdF /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
     getr regsF r = getr regs0 r) /\
  getr regsF 12 = w64 (ld0 + Z.of_nat (length s)) /\
  (forall m, (m < length s)%nat -> aview SEGS (w_H W) memF (dpA + ld0 + Z.of_nat m) = Some (bz (nthb s m))) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dpA + ld0 <= a < dpA + ld0 + Z.of_nat (length s)) ->
     aview SEGS (w_H W) memF a = aview SEGS (w_H W) m0 a) /\
  (forall a, apresent (w_H W) m0 a -> apresent (w_H W) memF a).

(* The state at the head of iteration j. *)
Definition jd_inv (j : nat) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k /\
  (forall r, In r JD_KEPT -> getr regsL r = getr regs0 r) /\
  getr regsL 10 = w64 (nmA + 1 + Z.of_nat j) /\ getr regsL 13 = w64 (nmA + 1 + Z.of_nat j) /\
  getr regsL 12 = w64 (ld0 + Z.of_nat j) /\ getr regsL 14 = w64 (bz (nthb s j)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dpA + ld0 <= a < dpA + ld0 + Z.of_nat j) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) m0 a) /\
  (forall a, apresent (w_H W) m0 a -> apresent (w_H W) memL a) /\
  (forall m, (m < j)%nat -> aview SEGS (w_H W) memL (dpA + ld0 + Z.of_nat m) = Some (bz (nthb s m))).

Definition jd_extra (j : nat) : list word := [w64 (dpA + ld0 + Z.of_nat j); w64 (bz (nthb s (Datatypes.S j)))].

Lemma jd_consts : alloc_ceiling <= 0x7fffff800000 /\ SHADOW_OFF = SB_D.
Proof. pose proof asan_consts as (C1 & _). unfold SHADOW_OFF, SB_D. lia. Qed.

(* A byte of the shadow band is not a byte of exp_dp: exp_dp is application memory (in_app). *)
Lemma jd_cell_not_dp : forall c, SB_D <= c < SB_D + 2 ^ 44 -> ~ (dpA <= c < dpA + 64).
Proof.
  intros c Hc Hd. destruct APD as (H0 & H1).
  unfold YG0f.kLowShadowBeg, YG0f.kHighMemBeg in H1. unfold SB_D in Hc. lia.
Qed.

(* The facts of m0 the loop reads, at a memory that differs from m0 only in exp_dp. *)
Lemma jd_mem : forall memL,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dpA <= a < dpA + 64) -> aview SEGS (w_H W) memL a = aview SEGS (w_H W) m0 a) ->
  garr8 SEGS (mrestrict (w_H W) memL) nmA (map bv_unsigned (s ++ [zb 0])) /\
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 /\
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF dpA 64.
Proof.
  intros memL KL. pose proof jd_consts as (C1 & C2).
  split; [|split].
  - apply (jd_garr8_moved W m0 memL nmA); [|exact HNM].
    intros kk Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk.
    apply KL; [lia | lia].
  - apply (jd_zs_moved W m0 memL nmA 32); [|exact ZNM].
    intros i Hi. change (32 / 8) with 4 in Hi. unfold shadow_of_addr. rewrite C2.
    apply KL; [unfold SB_D; lia | apply jd_cell_not_dp; unfold SB_D; lia].
  - apply (jd_zs_moved W m0 memL dpA 64); [|exact ZDP].
    intros i Hi. change (64 / 8) with 8 in Hi. unfold shadow_of_addr. rewrite C2.
    apply KL; [unfold SB_D; lia | apply jd_cell_not_dp; unfold SB_D; lia].
Qed.

(* ---- the state at the loop head --------------------------------------------------------------------------- *)
Lemma jd_head_ok : forall (j : nat) regsL memL mdL,
  (j < length s)%nat -> jd_inv j regsL memL mdL ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsL (jd_extra j))) ss_jd
    (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x153c)) memL (seg_rom SEGS))) /\
  sh_ok SEGS Bx_D SH_jd (Eimg (Ereg regsL (jd_extra j))) (mrestrict (w_H W) memL).
Proof.
  intros j regsL memL mdL Hj (HJ & RK & R10 & R13 & R12 & R14 & KL & GL & WL).
  pose proof jd_consts as (C1 & C2).
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (dpA <= a < dpA + 64) ->
            aview SEGS (w_H W) memL a = aview SEGS (w_H W) m0 a) by (intros a Ha Hn; apply KL; jlia).
  destruct (jd_mem memL KD) as (GN & ZN & ZD).
  pose proof (jd_bz (nthb s j)) as Hb0. pose proof (jd_bz (nthb s (Datatypes.S j))) as Hb1.
  pose proof (HNZ j Hj) as Hnz.
  remember (Eimg (Ereg regsL (jd_extra j))) as E eqn:HE.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (jd_extra j)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E10 : ew E 10 = w64 (nmA + 1 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 (ld0 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (nmA + 1 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 (bz (nthb s j)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 14 14%bv eq_refl); exact R14).
  assert (E17 : ew E 17 = w64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl);
        rewrite (RK 17%bv jd_in17); exact R17).
  assert (E24 : ew E 24 = w64 dpA)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 24 24%bv eq_refl);
        rewrite (RK 24%bv jd_in24); exact R24).
  assert (E32 : ew E 32 = w64 (dpA + ld0 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (bz (nthb s (Datatypes.S j))))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply jd_unsigned; exact Hv).
  assert (Hsrc : val_mem SEGS (mrestrict (w_H W) memL) (nmA + 1 + Z.of_nat j) 1 (bz (nthb s (Datatypes.S j)))).
  { assert (Hlt : (Datatypes.S j < length (map bv_unsigned (s ++ [zb 0])))%nat)
      by (rewrite length_map, length_app; cbn [length]; lia).
    destruct (GN (Datatypes.S j) Hlt) as [Hv _].
    rewrite (jd_nth_src s (Datatypes.S j)) in Hv by lia.
    replace (nmA + 1 + Z.of_nat j) with (nmA + Z.of_nat (Datatypes.S j)) by lia. exact Hv. }
  split.
  - rewrite restrict_mkst_fx. unfold ss_jd. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold jd_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 32%nat (dpA + ld0 + Z.of_nat j) E32) by jlia.
        split; [jlia|]. split; [jlia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply GL.
        apply (proj2 (WR (dpA + ld0 + Z.of_nat j + o) ltac:(jlia))).
      * rewrite (VB 13%nat (nmA + 1 + Z.of_nat j) E13) by jlia.
        split; [jlia|]. split; [jlia|]. split; [intros o Ho; jlia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (nmA + 1 + Z.of_nat j) 0 1 (SOff 33 0) (bz (nthb s (Datatypes.S j)))).
        -- apply jd_sv. rewrite (jd_U E 33 _ 0 E33), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. exact Hb1.
        -- cbn. lia.
        -- rewrite Z.add_0_r. exact Hsrc.
    + apply pairwise_disjoint_of_extents. unfold jd_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 32%nat (dpA + ld0 + Z.of_nat j) E32) by jlia.
      rewrite (VB 13%nat (nmA + 1 + Z.of_nat j) E13) by jlia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. jclean. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [jd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E17, E10, E13, E12, E24, E32, E14, E33.
        rewrite !jd_unsigned by (rewrite ?C2; unfold SB_D; jlia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite C2. jclean. unfold SB_D. repeat split; lia.
      * cbn [jd_facts f_alias alias_ok]. split; [|exact I].
        rewrite (jd_sv E (SOff 32 0) (dpA + ld0 + Z.of_nat j)) by (rewrite (jd_U E 32 _ 0 E32), Z.add_0_r; reflexivity).
        apply jd_sv. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (jd_U E 24 dpA 0 E24), (jd_U E 12 _ 0 E12), !Z.add_0_r. unfold zcanon, M64.
        rewrite <- Zplus_mod. f_equal. lia.
  - assert (UB : U E Bx_D = SHADOW_OFF).
    { unfold Bx_D. rewrite (jd_U E 17 SHADOW_OFF 0 E17), Z.add_0_r. apply Z.mod_small. rewrite C2. unfold SB_D. lia. }
    unfold sh_ok, SH_jd. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) memL E Bx_D 32 dpA 64 (dpA + ld0 + Z.of_nat j) 0 1).
    + apply zero_shadow_range; [exact Hd8 | reflexivity | exact ZD].
    + exact UB.
    + rewrite (jd_U E 32 _ 0 E32), Z.add_0_r. apply Z.mod_small. jlia.
    + jlia.
    + jlia.
    + intros x Hx Hb. rewrite C2 in Hb. apply (jd_cell_not_dp x); [unfold SB_D in *; lia | jlia].
Qed.

(* After a run: the destination byte of iteration j is the only window. *)
Ltac jd_awr U32 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  eapply awr_ok_cons_gen; [reflexivity | jewo; exact U32 | |];
  [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; apply (proj1 (WR a ltac:(jlia)))
  | apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil ].

(* ---- the copy loop: induction on the bytes still to copy -------------------------------------------------- *)
Lemma jd_loop : forall (n j : nat) regsL memL mdL,
  (j + n = length s)%nat -> (0 < n)%nat -> jd_inv j regsL memL mdL ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x153c) regsL memL mdL) jd_post.
Proof.
  induction n as [|n IH]; intros j regsL memL mdL Hjn Hn HI; [lia|].
  assert (Hj : (j < length s)%nat) by lia.
  destruct (jd_head_ok j regsL memL mdL Hj HI) as [HS SHOK].
  pose proof HI as (HJ & RK & R10 & R13 & R12 & R14 & KL & GL & WL).
  pose proof jd_consts as (C1 & C2).
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (dpA <= a < dpA + 64) ->
            aview SEGS (w_H W) memL a = aview SEGS (w_H W) m0 a) by (intros a Ha Hnn; apply KL; jlia).
  destruct (jd_mem memL KD) as (_ & ZN & _).
  pose proof (jd_bz (nthb s j)) as Hb0. pose proof (jd_bz (nthb s (Datatypes.S j))) as Hb1.
  remember (Eimg (Ereg regsL (jd_extra j))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regsL (jd_extra j)) nn)
    by (intros nn Hnn; subst E; apply Eimg_low; exact Hnn).
  assert (E10 : ew E 10 = w64 (nmA + 1 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 (ld0 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (nmA + 1 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 (bz (nthb s j)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 14 14%bv eq_refl); exact R14).
  assert (E17 : ew E 17 = w64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl);
        rewrite (RK 17%bv jd_in17); exact R17).
  assert (E32 : ew E 32 = w64 (dpA + ld0 + Z.of_nat j))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (bz (nthb s (Datatypes.S j))))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (HAE : env_agree 32 (Ereg regsL (jd_extra j)) E)
    by (split; [intros nn Hnn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  clear HE EL.
  assert (U32 : bv_unsigned (ew E 32) = dpA + ld0 + Z.of_nat j) by (rewrite E32; apply jd_unsigned; jlia).
  assert (KEEPI : jd_kept W (dpA + ld0 + Z.of_nat j) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : jd_grown W memL memL) by (intros a Ha; exact Ha).
  unfold cfg_at. rewrite jd_w64.
  (* 0x81c48 .. 0x81c80: the two shadow tests, the store, the load of exp_nm[1 + j], the counters *)
  paj_run_tok RUN HS HJ SHOK Bspan_D.
  - (* the source's shadow test: zero_shadow of exp_nm *)
    cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS).
    unfold Bx_D. rewrite (jd_U E 17 SHADOW_OFF 0 E17), (jd_U E 10 _ 0 E10), !Z.add_0_r.
    rewrite (Z.mod_small SHADOW_OFF) by (rewrite C2; unfold SB_D; lia).
    rewrite Z.mod_small by jlia.
    apply (range_addressable_sub _ _ nmA 32); [apply zero_shadow_range; [exact Hn8 | reflexivity | exact ZN] | jlia | jlia].
  - jd_awr U32.
  - jd_keep U32.
    psrr_branch_tok RUN BR HS SHOK Bspan_D.
    + (* exp_nm[1 + j] <> 0: back to the head *)
      assert (Hc1 : bz (nthb s (Datatypes.S j)) <> 0).
      { rewrite branch_ne_U in Hc. rewrite (jd_U _ 33%nat (bz (nthb s (Datatypes.S j))) 0) in Hc by (jewo; exact E33).
        rewrite jd_Ulit in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by jlia.
        exact Hc. }
      clear Hc.
      assert (HSj : (Datatypes.S j < length s)%nat).
      { destruct (Nat.eq_dec (Datatypes.S j) (length s)) as [He | He]; [|lia].
        exfalso. apply Hc1. rewrite He. apply jd_nthb_end. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_D 0x153c; [jd_awr U32|].
      jd_keep U32.
      pmkst HS.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
        assert (HAE' : env_agree 32 (Ereg regsL (jd_extra j)) Ex)
          by (eapply jd_agree_ext; [exact HAE | split; [intros nn Hnn; jewo; reflexivity | reflexivity]]);
        pose proof (jd_kept_regs _ _ _ _ _ HS HAE' ltac:(vm_compute; reflexivity)) as RCS;
        cbn [ms_regs restrict] in RCS;
        jd_reg HS (10%bv : bv 5) Q10; jd_reg HS (12%bv : bv 5) Q12; jd_reg HS (13%bv : bv 5) Q13;
        jd_reg HS (14%bv : bv 5) Q14;
        pose proof (jd_val1 _ _ _ (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 14 0))])
                      32%nat 0 (SOff 14 0) (bz (nthb s j)) HS
                      ltac:(cbn [ss_mem In]; left; reflexivity) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply jd_sv; rewrite (jd_U _ 14%nat (bz (nthb s j)) 0) by (jewo; exact E14);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply jd_bz)) as Md;
        cbn [ms_mem restrict] in Md; jewo_in Md; rewrite U32, Z.add_0_r, jd_byte_of_bz in Md;
        apply (IH (Datatypes.S j) (ms_regs msF) (ms_mem msF) _)
      end.
      * lia.
      * lia.
      * split; [exact HJ|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        -- intros r Hr. rewrite (RCS r Hr). exact (RK r Hr).
        -- rewrite Q10. apply jd_sv. rewrite (jd_U _ 10%nat _ 1) by (jewo; exact E10). f_equal; lia.
        -- rewrite Q13. apply jd_sv. rewrite (jd_U _ 13%nat _ 1) by (jewo; exact E13). f_equal; lia.
        -- rewrite Q12. apply jd_sv. rewrite (jd_U _ 12%nat _ 1) by (jewo; exact E12). f_equal; lia.
        -- rewrite Q14. apply jd_sv. rewrite (jd_U _ 33%nat _ 0) by (jewo; exact E33). f_equal; lia.
        -- intros a Ha Hna. rewrite (KEEPI a Ha ltac:(jlia)). apply KL; [exact Ha | jlia].
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
        -- intros m Hm. destruct (Nat.eq_dec m j) as [-> | Hmj].
           ++ unfold aview. rewrite Md. reflexivity.
           ++ rewrite (KEEPI (dpA + ld0 + Z.of_nat m) ltac:(jlia) ltac:(jlia)). apply WL. lia.
    + (* exp_nm[1 + j] = 0: j + 1 = |s|, to the exit *)
      assert (Hc1 : bz (nthb s (Datatypes.S j)) = 0).
      { rewrite branch_ne_U in Hc. rewrite (jd_U _ 33%nat (bz (nthb s (Datatypes.S j))) 0) in Hc by (jewo; exact E33).
        rewrite jd_Ulit in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by jlia.
        exact Hc. }
      clear Hc.
      assert (HSj : Datatypes.S j = length s).
      { destruct (Nat.lt_ge_cases (Datatypes.S j) (length s)) as [Hlt | Hge]; [|lia].
        exfalso. exact (HNZ _ Hlt Hc1). }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_D 0x1594; [jd_awr U32|].
      jd_keep U32.
      pmkst HS.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
        assert (HAE' : env_agree 32 (Ereg regsL (jd_extra j)) Ex)
          by (eapply jd_agree_ext; [exact HAE | split; [intros nn Hnn; jewo; reflexivity | reflexivity]]);
        pose proof (jd_kept_regs _ _ _ _ _ HS HAE' ltac:(vm_compute; reflexivity)) as RCS;
        cbn [ms_regs restrict] in RCS;
        jd_reg HS (12%bv : bv 5) Q12;
        pose proof (jd_val1 _ _ _ (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 14 0))])
                      32%nat 0 (SOff 14 0) (bz (nthb s j)) HS
                      ltac:(cbn [ss_mem In]; left; reflexivity) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply jd_sv; rewrite (jd_U _ 14%nat (bz (nthb s j)) 0) by (jewo; exact E14);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply jd_bz)) as Md;
        cbn [ms_mem restrict] in Md; jewo_in Md; rewrite U32, Z.add_0_r, jd_byte_of_bz in Md;
        apply SRr_ret; split; [reflexivity|];
        exists (ms_regs msF), (ms_mem msF)
      end.
      eexists. split; [unfold cfg_at; reflexivity|].
      split; [exact HJ|]. split; [|split; [|split; [|split]]].
      * intros r Hr. change [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv with JD_KEPT in Hr.
        rewrite (RCS r Hr). exact (RK r Hr).
      * rewrite Q12. apply jd_sv. rewrite (jd_U _ 12%nat _ 1) by (jewo; exact E12). f_equal; lia.
      * intros m Hm. destruct (Nat.eq_dec m j) as [-> | Hmj].
        -- unfold aview. rewrite Md. reflexivity.
        -- rewrite (KEEPI (dpA + ld0 + Z.of_nat m) ltac:(jlia) ltac:(jlia)). apply WL. lia.
      * intros a Ha Hna. rewrite (KEEPI a Ha ltac:(jlia)). apply KL; [exact Ha | jlia].
      * intros a Hpa. apply GROWI. apply GL. exact Hpa.
Qed.
End loop.

Theorem j_dp_loop : j_dp_loop_stmt B.
Proof.
  unfold j_dp_loop_stmt.
  intros STK sp0 FP own ly S W0 mem0 md0 lyc Sc W k nmA dpA ld0 s j regsL memL mdL
    HJ R3 R4 R17 R10 R13 R12 R14 R24 Hj HL HNZ HNM Hld0 Hld1 ZNM ZDP WR WL APN APD Hn0 Hn1 Hn8 Hd0 Hd1 Hd8 Hnd.
  apply (jd_loop STK sp0 FP own ly S W0 mem0 md0 lyc Sc W k nmA dpA ld0 s regsL memL)
    with (n := (length s - j)%nat) (j := j); try assumption; try lia.
  split; [exact HJ|]. split; [intros r _; reflexivity|].
  split; [exact R10|]. split; [exact R13|]. split; [exact R12|]. split; [exact R14|].
  split; [intros a _ _; reflexivity|]. split; [intros a Ha; exact Ha|]. exact WL.
Qed.

End c2.
End b2.
End a2.
