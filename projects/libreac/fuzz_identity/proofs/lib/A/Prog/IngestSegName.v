(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build (lib/A).
   The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* The model-name arm of reac_identity_ingest (fuzz_identity.asan): ting_seg_name of lib/A/Prog/IngestSeg.v.
   The arm runs 0x83b50 .. 0x83b78 (n := min(len - 1, 16), the pointers a1 = a7 = p + 1, a2 = t1 = a4 = id + 3,
   the counter a5 = 0 and t0 = -n), the copy loop at 0x83b7c .. 0x83bbc (one byte per iteration; it stops at a 0
   byte or after n bytes), the NUL store at 0x83be8 .. 0x83c04, the flag store at 0x83ca0 .. 0x83cb8 and the tail
   at 0x83cbc (ing_tail of reac_identity_ingest.v). A 0 byte at p[1] leaves through 0x83b48 (result 0).
   The loop is proved by induction on the iterations still to run (name_loop), one symbolic iteration per step,
   as the plain proof's name_loop (lib/Prog/reac_identity_ingest.v) does; the model is RcIdentLib's ING_name,
   ING_name_zero, name_len_hit and name_len_full. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ YC4b YC1h
reac_identity_ingest IngestSeg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel RcIdentLib reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation bz := RcIdentModel.bz.
(* The loop head 0x83b7c and the NUL store 0x83be8, as listing offsets. *)
Definition AF_name_head : Z := AF_reac_identity_ingest + 0x280.
Definition AF_name_exit : Z := AF_reac_identity_ingest + 0x2ec.
(* a6 holds the shadow base in the whole arm: the shadow tests are stated against its atom. *)
Definition BXN : sv := SOff 16 0.
(* 0x83b50 .. 0x83b78: no memory access. *)
Definition ss_name_ent : sstate := mkSS AF_ing_name sr_atoms [] None (mkFacts [] [] []).
(* One iteration from 0x83b7c: a7 (atom 17) points at the payload byte p[1 + i] (atom 32), t1 (atom 6) at the
   record byte id + 3 + i (atom 33 is the byte it holds now); a1 (11) and a2 (12) are the shadow-tested copies. *)
Definition name_loop_regions : smem :=
  [ YP09.mkRegion (Some 17%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 6%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition name_loop_facts : facts :=
  mkFacts [ (16%nat, mkAF SB_ING SB_ING 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0);
            (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (12%nat, mkAF 4096 (2 ^ 47 - 19) 0);
            (6%nat, mkAF 4096 (2 ^ 47 - 19) 0) ] [] [].
Definition ss_name_loop : sstate := mkSS AF_name_head sr_atoms name_loop_regions None name_loop_facts.
Definition SH_name_loop : list shent := [mkSHE 11 0 1; mkSHE 12 0 1; mkSHE 6 0 1].
(* 0x83be8 .. 0x83cbc: a1 := a4 + a3 is the NUL's address (atom 32, by the alias); a0 + 20 the flag. *)
Definition name_exit_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 1 []; YP09.mkRegion (Some 10%nat) 20 21 20 21 [] ].
Definition name_exit_facts : facts :=
  mkFacts [ (16%nat, mkAF SB_ING SB_ING 0); (32%nat, mkAF 4096 (2 ^ 47 - 19) 0);
            (10%nat, mkAF 4096 (2 ^ 47 - 38) 0) ] []
    [ (SAlu ALU_ADD (SOff 14 0) (SOff 13 0), SOff 32 0) ].
Definition ss_name_exit : sstate := mkSS AF_name_exit sr_atoms name_exit_regions None name_exit_facts.
Definition SH_name_exit : list shent := [mkSHE 32 0 1; mkSHE 10 20 21].
(* The callee-saved registers but sp: the arm writes none of them. *)
Definition NM_KEPT : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition nm_lextra (b cb : byte) : list word := [w64 (bz b); w64 (bz cb)].
(* The bytes a run may write, for the memory bookkeeping. *)
Definition nm_none (a : Z) : Prop := False.
Definition nm_win (d a : Z) : Prop := d <= a < d + 1.
Definition nx_win (e f a : Z) : Prop := a = e \/ a = f.
(* ---- generic facts --------------------------------------------------------------------------- *)
Lemma nm_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma nm_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma nm_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma nm_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma nm_negmod : forall x, 0 < x < 2 ^ 64 -> (- x) mod 2 ^ 64 = 2 ^ 64 - x.
Proof.
  intros x Hx. rewrite <- (Z.mod_add (- x) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma nm_bz : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma nm_byte_of_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold RcIdentModel.bz. apply Z_to_bv_bv_unsigned. Qed.
Lemma nm_aview_pt : forall H (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hx. apply (aview_eq_of SEGS). unfold mrestrict. rewrite Hx. reflexivity. Qed.
Lemma nm_mbyte_pt : forall H (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' a Hx. unfold mbyte, mrestrict. rewrite Hx. reflexivity. Qed.
Lemma nm_apresent_pt : forall H (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a Hx (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hx. exact Hb. Qed.
Lemma nm_aview_of_mbyte : forall H (m m' : word -> option byte) a,
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview. rewrite E. reflexivity. Qed.
Lemma nm_val_mem_kept : forall H (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> aview SEGS H m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv j Hj. rewrite (mbyte_of_aview SEGS H H m m' _ (Hk j Hj)). exact (Hv j Hj). Qed.
Lemma nm_ra_kept : forall (rd rd' : Z -> option Z) Bs a n,
  range_addressable rd Bs a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr Bs x) = rd (shadow_of_addr Bs x)) ->
  range_addressable rd' Bs a n.
Proof.
  intros rd rd' Bs a n H Hs x Hx. destruct (H x Hx) as (s & Hs1 & Hs2). exists s.
  rewrite (Hs x Hx). split; assumption.
Qed.
(* A one-byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma nm_val1 : forall E ss ms r n off e v,
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
(* What the runs so far kept (KEEPI) and the presence they kept (GROWI). *)
Definition nm_kept (W : world SEGS) (Zs : Z -> Prop) (m0 m1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Definition nm_grown (W : world SEGS) (m0 m1 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m0 a -> apresent (w_H W) m1 a.
(* What a run keeps, chained onto what the runs before it kept. *)
Lemma nm_keep_step : forall Ex rs (W : world SEGS) m0 m1 m2 (Zs : Z -> Prop),
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nm_kept W Zs m0 m1 -> nm_grown W m0 m1 ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> Zs a) ->
  nm_kept W Zs m0 m2 /\ nm_grown W m0 m2.
Proof.
  intros Ex rs W m0 m1 m2 Zs HFr HG K1 G1 Hw. split.
  - intros a Ha Hz. rewrite <- (K1 a Ha Hz). exact (kept_of_frame Ex rs (w_H W) m1 m2 Zs HFr Hw a Ha Hz).
  - intros a Hp. exact (apresent_grows _ _ _ a HG (G1 a Hp)).
Qed.
Lemma nm_in_kept : forall (l : list (bv 5)) q, 0 <= q < 32 ->
  existsb (fun r : bv 5 => Z.eqb (bv_unsigned r) q) l = true -> In (Z_to_bv 5 q) l.
Proof.
  intros l q Hq H. apply existsb_exists in H as (r & Hin & Hr). apply Z.eqb_eq in Hr.
  replace (Z_to_bv 5 q) with r; [exact Hin|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma nm_cs_of : forall E ss ms (regsL : bvmap 5 word) extra,
  st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsL extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NM_KEPT = true ->
  forall q, acallee_saved q -> q <> 2 -> getr (ms_regs ms) (Z_to_bv 5 q) = getr regsL (Z_to_bv 5 q).
Proof.
  intros E ss ms regsL extra HS HAE Hl q Hq Hq2.
  eapply (regs_kept_of_st_ok_pi _ _ _ _ _ NM_KEPT HS HAE Hl).
  apply nm_in_kept; [unfold acallee_saved in Hq; lia|].
  assert (Hc : q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
               \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
    by (unfold acallee_saved in Hq; lia).
  clear - Hc.
  repeat (destruct Hc as [Hc | Hc]; [subst q; vm_compute; reflexivity |]).
  subst q; vm_compute; reflexivity.
Qed.
Lemma nm_agree_ext : forall regsL extra E E',
  env_agree 32 (Ereg regsL extra) E -> env_agree 32 E E' -> env_agree 32 (Ereg regsL extra) E'.
Proof.
  intros regsL extra E E' [H1 H2] [H3 H4]. split.
  - intros n Hn. rewrite (H3 n Hn). exact (H1 n Hn).
  - rewrite H4. exact H2.
Qed.
End f.
End d.
(* ---- tactics ---------------------------------------------------------------------------------- *)
(* Drop the hypotheses lia must not preprocess (the symbolic states, the journals, the quantified facts). *)
Ltac nclean :=
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
  | H : forall _ : Z, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  | H : forall _ : word, _ |- _ => clear H
  end.
Ltac nlia := nclean; lia.
(* ew of an extended environment at a low atom. *)
Ltac ewo := repeat rewrite ew_ewset_other by lia.
Ltac ewo_in H := repeat rewrite ew_ewset_other in H by lia.
(* A register of the symbolic state, kept as the symbolic value's denotation. *)
Ltac nreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* The windows of a run lie in the bytes Zs names. *)
Ltac nm_wins fin :=
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wl wh aa Hin Hr;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; cbn [base_val] in Hr; ewo_in Hr;
            first [ nclean; lia | fin Hr ] | ]);
  destruct Hin.
(* After a run: chain its frame onto KEEPI / GROWI. *)
Ltac nm_keep fin :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _,
    KI : nm_kept _ _ _ _, GI : nm_grown _ _ _ |- _ =>
      let Hw := fresh "Hw" in
      pose proof (nm_keep_step _ _ _ _ _ _ _ HFr HG KI GI) as Hw;
      let K2 := fresh "K2" in let G2 := fresh "G2" in
      lazymatch type of Hw with ?P -> _ =>
        let HP := fresh "HP" in assert (HP : P) by (nm_wins fin);
        destruct (Hw HP) as [K2 G2]; clear HP Hw end;
      clear KI GI HFr HG; rename K2 into KEEPI; rename G2 into GROWI
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* The writable windows of a run: each lies in the caller's record (RW). *)
Ltac nm_awr Ucl RW :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
    | eapply awr_ok_cons_gen;
        [ reflexivity | ewo; Ucl
        | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; apply (proj1 (RW a ltac:(nlia)))
        | ] ].
(* The callee-saved registers of a stopped state equal those of the state its environment was built from. *)
Ltac nm_cs HS HAE :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  lazymatch type of HAE with env_agree _ ?A _ =>
    let HAE' := fresh "HAE'" in
    assert (HAE' : env_agree 32 A Ex)
      by (eapply nm_agree_ext; [exact HAE | split; [intros nn Hnn; ewo; reflexivity | reflexivity]]);
    let RC := fresh "RCS'" in
    pose proof (nm_cs_of _ _ _ _ _ HS HAE' ltac:(vm_compute; reflexivity)) as RC;
    cbn [ms_regs restrict] in RC; clear HAE'
  end end.
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation bz := RcIdentModel.bz.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Section arm.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (id ad p len : Z) (idb pb : list byte)
  (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model).
Hypothesis HARM : ing_arm_at B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
  regsT memT mdT.
Hypothesis Had : ad = 4096.
Hypothesis Hlen2 : 2 <= len.
Let POST := treac_identity_ingest_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb.
(* n of the C code, the most bytes the loop copies. *)
Let NN : nat := Nat.min (length pb - 1) 16.
Ltac nm_arm :=
  pose proof HARM as (HJc & Hra & Hra4 & Hid & Had' & Hp & Hlen & Hal16 & Hlo & Hhi & Hpl & HNR & HREC & HPAY &
                      Hev & Hlive & HJT & T10 & T12 & T13 & T16 & T2 & T1 & TCS & V8 & V16 & V24 & KEEPT & GROWT).
(* The layout facts the arm needs: the stack, the record and the payload, and where they lie. *)
Lemma nm_lay :
  2 ^ 46 + INGEST_STK <= spZ regs <= 2 ^ 47 /\ alloc_ceiling + INGEST_STK <= spZ regs /\
  4096 <= id /\ id + 38 <= 2 ^ 47 /\ 4096 <= p /\ p + len <= alloc_ceiling /\
  (p + len <= id \/ id + 38 <= p) /\ (spZ regs <= id \/ id + 38 <= spZ regs - INGEST_STK) /\
  (id + 38 <= IMG_LO \/ IMG_TOP <= id) /\
  (forall a, id <= a < id + 38 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  (forall a, p <= a < p + len -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  AR SEGS B lyc Sc W memc mdc /\ alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_hi lyc <= 2 ^ 47.
Proof.
  nm_arm.
  pose proof (ing_sp B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hsp.
  pose proof (ing_sp_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hceil.
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & Hstatc & _).
  pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstatc as (Hsp0al & Hstk0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
  assert (Hslo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil0).
  assert (Hshi : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H470).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (ing_zones B LAWS STK sp0 FP ly S own lyc Sc W memc mdc (spZ regs) id idb p len pb
              HARc Hceil Hslo Hshi HREC HPAY ltac:(lia))
    as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & bi & Li & Hbin & Hb1 & Hb2).
  assert (RAPP : forall a, id <= a < id + 38 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
  { intros a Ha. pose proof HREC as (_ & HL & _).
    destruct HL as [(cid & pos & Hfin & Hr) | Hs].
    - pose proof (Hr a Ha) as Hra'. unfold frame_rng, in_zr in Hra'. cbn [fst snd] in Hra'.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hfin) as (_ & _ & Happ).
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
    - unfold SHADOW_OFF. lia. }
  assert (PAPP : forall a, p <= a < p + len -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
  { intros a Ha.
    destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc bi Li HARc Hbin) as (_ & _ & _ & Happ & _).
    assert (HrqL : Li <= req_size Li)
      by (unfold req_size; destruct (Li =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia).
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  exact (conj Hsp (conj Hceil (conj Z4 (conj Z5 (conj Z6 (conj Z7 (conj Z3 (conj Z8 (conj Z1
          (conj RAPP (conj PAPP (conj HARc (conj Hslo Hshi))))))))))))).
Qed.
(* The call-time facts of the record and the payload. *)
Lemma nm_cfacts :
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF id 38 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p len /\
  (forall a, id <= a < id + 38 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  mbytes_at SEGS (mrestrict (w_H W) memc) id idb /\ length idb = 38%nat /\
  mbytes_at SEGS (mrestrict (w_H W) memc) p pb.
Proof.
  nm_arm. destruct nm_lay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HARc & _).
  pose proof HREC as (_ & _ & _ & HW & HRA & HL & HMB).
  pose proof HPAY as (HB & HMP).
  destruct (HB ltac:(lia)) as (bi & Li & Hbin & Hb1 & Hb2).
  assert (HrqL : Li <= req_size Li)
    by (unfold req_size; destruct (Li =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia).
  split; [exact HRA|].
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc bi Li p len HARc Hbin Hb1 ltac:(lia))|].
  split; [exact HW|]. split; [exact HMB|]. split; [exact HL | exact HMP].
Qed.
(* Shadow bytes of the record and the payload are kept by a memory that changed only in the record. *)
Lemma nm_shadow : forall m,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id + 38) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memT a) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF id 38 /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p len.
Proof.
  intros m Hm. nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & Himg & RAPP & PAPP & _).
  destruct nm_cfacts as (RAr & RAp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs : forall x, 4096 <= x < 2 ^ 47 ->
            aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. unfold shadow_of_addr.
    assert (Hd : 512 <= x / 8 < 2 ^ 44)
      by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
    rewrite Hm; [| unfold SHADOW_OFF; lia | intros Hin; apply (RAPP _ Hin); unfold SHADOW_OFF; lia].
    apply KEEPT; unfold SHADOW_OFF, INGEST_STK, ESTACK in *; lia. }
  split; (eapply nm_ra_kept; [eassumption | intros x Hx; apply Hs; lia]).
Qed.
(* A record byte the arm has not written, and a payload byte. *)
Lemma nm_idb_byte : forall m j, (j < 38)%nat ->
  aview SEGS (w_H W) m (id + Z.of_nat j) = aview SEGS (w_H W) memT (id + Z.of_nat j) ->
  mbyte SEGS (mrestrict (w_H W) m) (id + Z.of_nat j) = Some (nthb idb j).
Proof.
  intros m j Hj Ha. nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & _).
  destruct nm_cfacts as (_ & _ & _ & MBr & Hlidb & _).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memT m _ Ha).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc memT (id + Z.of_nat j)
             (KEEPT (id + Z.of_nat j) ltac:(nlia) ltac:(unfold INGEST_STK, ESTACK in *; nlia))).
  rewrite (MBr j ltac:(lia)). unfold RcIdentModel.nthb. apply nth_error_nth'. lia.
Qed.
Lemma nm_pb_byte : forall m j, (j < length pb)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = aview SEGS (w_H W) memT (p + Z.of_nat j) ->
  mbyte SEGS (mrestrict (w_H W) m) (p + Z.of_nat j) = Some (nthb pb j).
Proof.
  intros m j Hj Ha. nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & _).
  destruct nm_cfacts as (_ & _ & _ & _ & _ & MBp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memT m _ Ha).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc memT (p + Z.of_nat j)
             (KEEPT (p + Z.of_nat j) ltac:(nlia) ltac:(unfold INGEST_STK, ESTACK in *; nlia))).
  rewrite (MBp j Hj). unfold RcIdentModel.nthb. apply nth_error_nth'. exact Hj.
Qed.
(* The machine state the loop and the exit carry. *)
Definition nm_regs (regsL : bvmap 5 word) : Prop :=
  getr regsL 10 = w64 id /\ getr regsL 16 = w64 SB_ING /\ getr regsL 2 = w64 (spZ regs - 32) /\
  (forall q, acallee_saved q -> q <> 2 -> getr regsL (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)).
Definition nm_mem (i : nat) (memL : word -> option byte) (mdL : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id + 3 <= a < id + 3 + Z.of_nat i) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memT a) /\
  (forall j, (j < i)%nat ->
     mbyte SEGS (mrestrict (w_H W) memL) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j))) /\
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) memL a).
(* ---- the tail: 0x83cbc with a4 = the result ------------------------------------------------- *)
Lemma name_fin : forall regsF memF mdF r,
  getr regsF 2 = w64 (spZ regs - 32) ->
  (forall q, acallee_saved q -> q <> 2 -> getr regsF (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k ->
  getr regsF 14 = w64 r -> 0 <= r < 2 ^ 64 ->
  r = fst (RcIdentModel.ING idb 4096 pb) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id + 38) -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) memF a) ->
  mbytes_at SEGS (mrestrict (w_H W) memF) id (snd (RcIdentModel.ING idb 4096 pb)) ->
  SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + AF_ing_tail)) memF (seg_rom SEGS)) mdF) POST.
Proof.
  intros regsF memF mdF r F2 FCS HJF F14 Hr Hret KF GF MBF.
  nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & Himg & RAPP & PAPP & HARc & Hslo & Hshi).
  assert (KFr : forall o j, (o = 8 \/ o = 16 \/ o = 24) -> (j < 8)%nat ->
            aview SEGS (w_H W) memF (spZ regs - o + Z.of_nat j) = aview SEGS (w_H W) memT (spZ regs - o + Z.of_nat j)).
  { intros o j Ho Hj. apply KF; unfold INGEST_STK, ESTACK in *; nlia. }
  eapply SRr_mono.
  { eapply (ing_tail B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k regs regsF r
              HJF Hra Hal16 Hlo Hhi F2 F14 Hr).
    - intros q Hq H2 H8 H9. exact (FCS q Hq H2).
    - eapply nm_val_mem_kept; [|exact V8]. intros j Hj. apply KFr; [auto | exact Hj].
    - eapply nm_val_mem_kept; [|exact V16]. intros j Hj. apply KFr; [auto | exact Hj].
    - eapply nm_val_mem_kept; [|exact V24]. intros j Hj. apply KFr; [auto | exact Hj]. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10 & HM2).
  unfold POST, treac_identity_ingest_post. split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|].
  split; [unfold EV_INGEST; rewrite Z.add_0_r; exact HJ2|].
  split; [exact HP2|].
  split; [rewrite R10; unfold reac_identity_ingest_c.ingest_ret; rewrite HNR, Had, <- Hret; reflexivity|].
  split.
  - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
    eapply (ing_kept_of B LAWS _ _ _ _ _ _ (spZ regs) _ HARc Hceil ltac:(nlia)).
    + intros a Ha Hw HE. rewrite (nm_aview_pt _ memF mem2 a HM2).
      assert (Hnr : ~ (id <= a < id + 38)) by (intros Hin; apply HE; split; [exact HNR | exact Hin]).
      rewrite (KF a Ha Hnr). exact (KEEPT a Ha Hw).
    + intros a Hpc. apply (nm_apresent_pt _ memF mem2 a HM2). apply GF. apply GROWT. exact Hpc.
    + intros a Ha. apply HpF. unfold INGEST_STK, ESTACK in *; nlia.
    + intros a Hi (_ & Ha). pose proof (pa_img_range a Hi). nlia.
  - intros _. rewrite Had. intros j Hj. rewrite (nm_mbyte_pt _ memF mem2 _ HM2). exact (MBF j Hj).
Qed.
(* ---- the record the arm leaves ------------------------------------------------------------- *)
Lemma nm_rec_bytes : forall (c : nat) (m : word -> option byte),
  (1 <= c <= 16)%nat -> (c <= length pb - 1)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id + 3 <= a < id + 3 + Z.of_nat c) -> a <> id + 3 + Z.of_nat c -> a <> id + 20 ->
     aview SEGS (w_H W) m a = aview SEGS (w_H W) memT a) ->
  (forall j, (j < c)%nat -> mbyte SEGS (mrestrict (w_H W) m) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j))) ->
  mbyte SEGS (mrestrict (w_H W) m) (id + 3 + Z.of_nat c) = Some (RcIdentModel.zb 0) ->
  mbyte SEGS (mrestrict (w_H W) m) (id + 20) = Some (RcIdentModel.zb 1) ->
  mbytes_at SEGS (mrestrict (w_H W) m) id
    (RcIdentModel.upd (RcIdentModel.upd idb 3 (firstn c (skipn 1 pb) ++ [RcIdentModel.zb 0])) 20 [RcIdentModel.zb 1]).
Proof.
  intros c m Hc Hcp KM NBm M0 M1.
  destruct nm_cfacts as (_ & _ & _ & _ & Hlidb & _).
  destruct nm_lay as (_ & _ & Hid0 & Hid1 & _).
  pose proof HARM as (_ & _ & _ & Hid & _).
  set (X := firstn c (skipn 1 pb) ++ [RcIdentModel.zb 0]).
  assert (HX : length X = (c + 1)%nat) by (subst X; rewrite length_app, length_firstn, length_skipn; cbn [length]; lia).
  assert (L1 : length (RcIdentModel.upd idb 3 X) = 38%nat)
    by (rewrite RcIdentModel.upd_length; [exact Hlidb | lia]).
  assert (L2 : length (RcIdentModel.upd (RcIdentModel.upd idb 3 X) 20 [RcIdentModel.zb 1]) = 38%nat)
    by (rewrite RcIdentModel.upd_length; [exact L1 | cbn [length]; lia]).
  intros j Hj. rewrite L2 in Hj.
  rewrite (nth_error_nth' _ (RcIdentModel.zb 0)) by lia. fold (nthb (RcIdentModel.upd (RcIdentModel.upd idb 3 X) 20 [RcIdentModel.zb 1]) j).
  assert (Hkept : forall j', (j' < 38)%nat -> (j' < 3 \/ 3 + c < j' < 20 \/ 20 < j')%nat ->
            mbyte SEGS (mrestrict (w_H W) m) (id + Z.of_nat j') = Some (nthb idb j')).
  { intros j' Hj' Hr. apply nm_idb_byte; [exact Hj'|]. apply KM; nlia. }
  destruct (Nat.lt_ge_cases j 3) as [Hj3 | Hj3].
  - rewrite RcIdentLib.nthb_upd_lt by lia. rewrite RcIdentLib.nthb_upd_lt by lia. apply Hkept; lia.
  - destruct (Nat.lt_ge_cases j (3 + c)) as [Hjc | Hjc].
    + rewrite RcIdentLib.nthb_upd_lt by lia. rewrite RcIdentLib.nthb_upd_in by lia.
      subst X. rewrite RcIdentLib.nthb_name_in by lia.
      replace (id + Z.of_nat j) with (id + 3 + Z.of_nat (j - 3)) by lia.
      exact (NBm (j - 3)%nat ltac:(lia)).
    + destruct (Nat.eq_dec j (3 + c)) as [Hje | Hje].
      * rewrite RcIdentLib.nthb_upd_lt by lia. rewrite RcIdentLib.nthb_upd_in by lia.
        subst X. replace (j - 3)%nat with c by lia. rewrite RcIdentLib.nthb_name_end by lia.
        replace (id + Z.of_nat j) with (id + 3 + Z.of_nat c) by lia. exact M0.
      * destruct (Nat.lt_ge_cases j 20) as [Hj20 | Hj20].
        -- rewrite RcIdentLib.nthb_upd_lt by lia. rewrite RcIdentLib.nthb_upd_ge by lia. apply Hkept; lia.
        -- destruct (Nat.eq_dec j 20) as [-> | Hj20'].
           ++ rewrite RcIdentLib.nthb_upd_in by (cbn [length]; lia). exact M1.
           ++ rewrite RcIdentLib.nthb_upd_ge by (cbn [length]; lia). rewrite RcIdentLib.nthb_upd_ge by lia.
              apply Hkept; lia.
Qed.
(* ---- 0x83be8 .. 0x83cbc: the NUL after c name bytes, the flag, then the tail -------------------- *)
Lemma name_exit : forall (c : nat) regsX memX mdX,
  (1 <= c <= NN)%nat -> RcIdentModel.name_len pb = c ->
  nm_regs regsX -> nm_mem c memX mdX ->
  getr regsX 14 = w64 (id + 3) -> getr regsX 13 = w64 (Z.of_nat c) ->
  SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (BASE + AF_name_exit)) memX (seg_rom SEGS)) mdX) POST.
Proof.
  intros c regsX memX mdX Hc HNL (X10 & X16 & X2 & XCS) (HJ & KL & NB & GL) X14 X13.
  nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & Himg & RAPP & PAPP & HARc & Hslo & Hshi).
  destruct nm_cfacts as (_ & _ & RW & MBr & Hlidb & MBp).
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (Hc16 : (c <= 16)%nat /\ (c <= length pb - 1)%nat) by (rewrite HNN in Hc; lia).
  destruct Hc16 as [Hc16 Hcp].
  pose proof (Nat2Z.is_nonneg c) as Hc0.
  assert (Hcz : 1 <= Z.of_nat c <= 16) by lia.
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id + 38) ->
            aview SEGS (w_H W) memX a = aview SEGS (w_H W) memT a)
    by (intros a Ha Hn; apply KL; [exact Ha | nlia]).
  destruct (nm_shadow memX KR) as [RAr RAp].
  remember (Eimg (Ereg regsX [w64 (id + 3 + Z.of_nat c)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsX [w64 (id + 3 + Z.of_nat c)]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = w64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 2 2%bv eq_refl); exact X2).
  assert (E10 : ew E 10 = w64 id)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 10 10%bv eq_refl); exact X10).
  assert (E13 : ew E 13 = w64 (Z.of_nat c))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 13 13%bv eq_refl); exact X13).
  assert (E14 : ew E 14 = w64 (id + 3))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 14 14%bv eq_refl); exact X14).
  assert (E16 : ew E 16 = w64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsX _ 16 16%bv eq_refl); exact X16).
  assert (E32 : ew E 32 = w64 (id + 3 + Z.of_nat c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 0)).
  assert (HAE : env_agree 32 (Ereg regsX [w64 (id + 3 + Z.of_nat c)]) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (U10 : bv_unsigned (ew E 10) = id) by (rewrite E10; apply nm_unsigned; lia).
  assert (U32 : bv_unsigned (ew E 32) = (id + 3 + Z.of_nat c)) by (rewrite E32; apply nm_unsigned; lia).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply nm_unsigned; exact Hv).
  assert (HS : st_ok_pi SEGS VAL E ss_name_exit
                 (restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + AF_name_exit)) memX (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_name_exit. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold name_exit_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      + rewrite (VB 32%nat (id + 3 + Z.of_nat c) E32) by (lia). split; [lia|]. split; [lia|].
        split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply GL. apply GROWT.
        apply (proj2 (RW (id + 3 + Z.of_nat c + o) ltac:(nlia))).
      + rewrite (VB 10%nat id E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply GL. apply GROWT. apply (proj2 (RW (id + o) ltac:(nlia))).
    - apply pairwise_disjoint_of_extents. unfold name_exit_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 32%nat (id + 3 + Z.of_nat c) E32) by (lia). rewrite (VB 10%nat id E10) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. nclean. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [name_exit_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E16, E32, E10. rewrite !nm_unsigned by (unfold SB_ING; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. nclean. unfold SB_ING. repeat split; lia.
      + cbn [name_exit_facts f_alias alias_ok]. split; [|exact I].
        apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (nm_U E 14 (id + 3) 0 E14), (nm_U E 13 (Z.of_nat c) 0 E13).
        rewrite (nm_U E 32 (id + 3 + Z.of_nat c) 0 E32). rewrite !Z.add_0_r.
        rewrite (Z.mod_small (id + 3)) by lia. rewrite (Z.mod_small (Z.of_nat c)) by lia.
        unfold zcanon, M64. f_equal; lia. }
  assert (SHOK : sh_ok SEGS BXN SH_name_exit E (mrestrict (w_H W) memX)).
  { assert (UB : U E BXN = SHADOW_OFF) by (unfold BXN; rewrite (nm_U E 16 SB_ING 0 E16); reflexivity).
    unfold sh_ok, SH_name_exit. repeat apply Forall_cons; try apply Forall_nil.
    - apply (shent_ok_of_range SEGS (w_H W) memX E BXN 32 id 38 (id + 3 + Z.of_nat c) 0 1 RAr UB).
      + rewrite (nm_U E 32 (id + 3 + Z.of_nat c) 0 E32), Z.add_0_r. apply Z.mod_small. lia.
      + lia.
      + lia.
      + intros x Hx. apply RAPP. nlia.
    - apply (shent_ok_of_range SEGS (w_H W) memX E BXN 10 id 38 id 20 21 RAr UB).
      + rewrite (nm_U E 10 id 0 E10), Z.add_0_r. apply Z.mod_small. lia.
      + lia.
      + lia.
      + intros x Hx. apply RAPP. nlia. }
  clear HE EL.
  assert (KEEPI : nm_kept W (nx_win (id + 3 + Z.of_nat c) (id + 20)) memX memX) by (intros a _ _; reflexivity).
  assert (GROWI : nm_grown W memX memX) by (intros a Ha; exact Ha).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING AF_ing_tail;
    [ nm_awr ltac:(first [exact U32 | exact U10]) RW |].
  nm_keep ltac:(fun Hr => rewrite ?U32, ?U10 in Hr; unfold nx_win; nlia).
  pmkst HS.
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
    nreg HS (14%bv : bv 5) R14; nreg HS (2%bv : bv 5) R2;
    assert (HAE' : env_agree 32 (Ereg regsX [w64 (id + 3 + Z.of_nat c)]) Ex)
      by (eapply nm_agree_ext; [exact HAE | split; [intros nn Hnn; ewo; reflexivity | reflexivity]]);
    pose proof (nm_cs_of _ _ _ regsX _ HS HAE' ltac:(vm_compute; reflexivity)) as RCS;
    cbn [ms_regs restrict] in RCS;
    pose proof (nm_val1 _ _ _ (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
                  32%nat 0 (SLit 0) 0 HS ltac:(cbn [ss_mem In]; left; reflexivity) eq_refl
                  ltac:(cbn [YP09.r_chunks In]; left; reflexivity) eq_refl ltac:(lia)) as M0;
    pose proof (nm_val1 _ _ _ (YP09.mkRegion (Some 10%nat) 20 21 20 21 [YP09.mkChunk 20 (CVal 1 (SLit 1))])
                  10%nat 20 (SLit 1) 1 HS ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                  ltac:(cbn [YP09.r_chunks In]; left; reflexivity) eq_refl ltac:(lia)) as M1;
    cbn [ms_mem restrict] in M0, M1; ewo_in M0; ewo_in M1; rewrite U32, Z.add_0_r in M0; rewrite U10 in M1;
    apply (name_fin (ms_regs ms) (ms_mem ms) _ 1)
  end.
  - rewrite R2. apply nm_sv. rewrite (nm_U _ 2 (spZ regs - 32) 0) by (ewo; exact E2). rewrite Z.add_0_r. reflexivity.
  - intros q Hq Hq2. rewrite (RCS q Hq Hq2). exact (XCS q Hq Hq2).
  - exact HJ.
  - rewrite R14. reflexivity.
  - lia.
  - rewrite (RcIdentLib.ING_name idb pb) by (rewrite ?HNL; lia). reflexivity.
  - intros a Ha Hn. rewrite (KEEPI a Ha ltac:(unfold nx_win; nlia)). apply KL; [exact Ha | nlia].
  - intros a Hpa. apply GROWI. apply GL. exact Hpa.
  - rewrite (RcIdentLib.ING_name idb pb) by (rewrite ?HNL; lia). rewrite HNL. cbn [snd].
    apply (nm_rec_bytes c (ms_mem ms)); [lia | lia | | | exact M0 | exact M1].
    + intros a Ha Hn He Hf. rewrite (KEEPI a Ha ltac:(unfold nx_win; nlia)). apply KL; [exact Ha | exact Hn].
    + intros j Hj. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memX (ms_mem ms) (id + 3 + Z.of_nat j)
                              (KEEPI (id + 3 + Z.of_nat j) ltac:(nlia) ltac:(unfold nx_win; nlia))).
      exact (NB j Hj).
Qed.
(* ---- the loop's memory bookkeeping ----------------------------------------------------------- *)
(* The record byte at id + 3 + i is unchanged: the bytes written so far are still i. *)
Lemma nm_kl_same : forall (i : nat) memL mF, (i <= 15)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id + 3 <= a < id + 3 + Z.of_nat i) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memT a) ->
  nm_kept W (nm_win (id + 3 + Z.of_nat i)) memL mF ->
  mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat i) = Some (nthb idb (3 + i)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (id + 3 <= a < id + 3 + Z.of_nat i) ->
    aview SEGS (w_H W) mF a = aview SEGS (w_H W) memT a.
Proof.
  intros i memL mF Hi KL KI Hd a Ha Hn.
  destruct (Z.eq_dec a (id + 3 + Z.of_nat i)) as [-> | Hne].
  - apply nm_aview_of_mbyte. rewrite Hd. symmetry.
    replace (id + 3 + Z.of_nat i) with (id + Z.of_nat (3 + i)) by nlia.
    apply nm_idb_byte; [nlia | reflexivity].
  - rewrite (KI a Ha ltac:(unfold nm_win; nlia)). apply KL; assumption.
Qed.
(* The byte p[1 + i] was stored at id + 3 + i: the bytes written so far are i + 1. *)
Lemma nm_kl_step : forall (i : nat) memL mF,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id + 3 <= a < id + 3 + Z.of_nat i) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memT a) ->
  nm_kept W (nm_win (id + 3 + Z.of_nat i)) memL mF ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (id + 3 <= a < id + 3 + Z.of_nat (Datatypes.S i)) ->
    aview SEGS (w_H W) mF a = aview SEGS (w_H W) memT a.
Proof.
  intros i memL mF KL KI a Ha Hn.
  rewrite (KI a Ha ltac:(unfold nm_win; nlia)). apply KL; [exact Ha | nlia].
Qed.
Lemma nm_nb_same : forall (i : nat) memL mF, (i <= 16)%nat ->
  (forall j, (j < i)%nat -> mbyte SEGS (mrestrict (w_H W) memL) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j))) ->
  nm_kept W (nm_win (id + 3 + Z.of_nat i)) memL mF ->
  forall j, (j < i)%nat -> mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j)).
Proof.
  intros i memL mF Hi16 NB KI j Hj.
  pose proof (nm_lay) as (_ & _ & Hid0 & Hid1 & _).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memL mF (id + 3 + Z.of_nat j)
             (KI (id + 3 + Z.of_nat j) ltac:(nlia) ltac:(unfold nm_win; nlia))).
  exact (NB j Hj).
Qed.
Lemma nm_nb_step : forall (i : nat) memL mF, (i <= 16)%nat ->
  (forall j, (j < i)%nat -> mbyte SEGS (mrestrict (w_H W) memL) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j))) ->
  nm_kept W (nm_win (id + 3 + Z.of_nat i)) memL mF ->
  mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat i) = Some (nthb pb (1 + i)) ->
  forall j, (j < Datatypes.S i)%nat ->
    mbyte SEGS (mrestrict (w_H W) mF) (id + 3 + Z.of_nat j) = Some (nthb pb (1 + j)).
Proof.
  intros i memL mF Hi16 NB KI Hd j Hj.
  destruct (Nat.eq_dec j i) as [-> | Hne]; [exact Hd|].
  exact (nm_nb_same i memL mF Hi16 NB KI j ltac:(nlia)).
Qed.
(* ---- the state at the loop head --------------------------------------------------------------- *)
Lemma nm_loop_ok : forall (i : nat) regsL memL mdL,
  (i < NN)%nat -> nm_regs regsL -> nm_mem i memL mdL ->
  getr regsL 11 = w64 (p + 1 + Z.of_nat i) -> getr regsL 17 = w64 (p + 1 + Z.of_nat i) ->
  getr regsL 12 = w64 (id + 3 + Z.of_nat i) -> getr regsL 6 = w64 (id + 3 + Z.of_nat i) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i))))) ss_name_loop
    (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + AF_name_head)) memL (seg_rom SEGS))) /\
  sh_ok SEGS BXN SH_name_loop (Eimg (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i)))))
    (mrestrict (w_H W) memL).
Proof.
  intros i regsL memL mdL Hi (R10 & R16 & R2 & RCS) (HJ & KL & NB & GL) R11 R17 R12 R6.
  nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & Himg & RAPP & PAPP & HARc & Hslo & Hshi).
  destruct nm_cfacts as (_ & _ & RW & MBr & Hlidb & MBp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (Hiz : 0 <= Z.of_nat i <= 15 /\ Z.of_nat i + 2 <= len) by (rewrite HNN in Hi; nlia).
  destruct Hiz as [Hi15 Hil].
  pose proof (nm_bz (nthb pb (1 + i))) as Hbz. pose proof (nm_bz (nthb idb (3 + i))) as Hcbz.
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id + 38) ->
            aview SEGS (w_H W) memL a = aview SEGS (w_H W) memT a)
    by (intros a Ha Hn; apply KL; [exact Ha | nlia]).
  destruct (nm_shadow memL KR) as [RAr RAp].
  remember (Eimg (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i))))) as E eqn:HE.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i)))) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E6 : ew E 6 = w64 (id + 3 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 6 6%bv eq_refl); exact R6).
  assert (E11 : ew E 11 = w64 (p + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 11 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = w64 (id + 3 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E16 : ew E 16 = w64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 16 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 (p + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E32 : ew E 32 = w64 (bz (nthb pb (1 + i))))
    by (rewrite EL by (unfold A_TEXT; nlia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (bz (nthb idb (3 + i))))
    by (rewrite EL by (unfold A_TEXT; nlia); exact (ew_Ereg_extra regsL _ 1)).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply nm_unsigned; exact Hv).
  assert (Mq : mbyte SEGS (mrestrict (w_H W) memL) (p + 1 + Z.of_nat i) = Some (nthb pb (1 + i))).
  { replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (1 + i)) by nlia.
    apply nm_pb_byte; [nlia|]. apply KL; nlia. }
  assert (Md : mbyte SEGS (mrestrict (w_H W) memL) (id + 3 + Z.of_nat i) = Some (nthb idb (3 + i))).
  { replace (id + 3 + Z.of_nat i) with (id + Z.of_nat (3 + i)) by nlia.
    apply nm_idb_byte; [nlia|]. apply KL; nlia. }
  split.
  - rewrite restrict_mkst_fx. unfold ss_name_loop. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold name_loop_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 17%nat (p + 1 + Z.of_nat i) E17) by nlia.
        split; [nlia|]. split; [nlia|]. split; [intros o Ho; nlia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (p + 1 + Z.of_nat i) 0 1 (SOff 32 0) (bz (nthb pb (1 + i)))).
        -- apply nm_sv. rewrite (nm_U E 32 _ 0 E32), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. exact Hbz.
        -- cbn. nlia.
        -- intros kk Hk. cbn in Hk. assert (kk = 0%nat) as -> by nlia.
           replace (p + 1 + Z.of_nat i + 0 + Z.of_nat 0) with (p + 1 + Z.of_nat i) by nlia.
           rewrite Mq. f_equal. rewrite le_byte_small by (first [change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256; exact Hbz | cbn; nlia]). change (8 * Z.of_nat 0) with 0.
           rewrite Z.shiftr_0_r. symmetry. apply nm_byte_of_bz.
      * rewrite (VB 6%nat (id + 3 + Z.of_nat i) E6) by nlia.
        split; [nlia|]. split; [nlia|]. split.
        -- intros o Ho. apply (apresent_writable SEGS). apply GL. apply GROWT.
           apply (proj2 (RW (id + 3 + Z.of_nat i + o) ltac:(nlia))).
        -- constructor; [|constructor].
           apply (chunk_ok_val SEGS E _ (id + 3 + Z.of_nat i) 0 1 (SOff 33 0) (bz (nthb idb (3 + i)))).
           ++ apply nm_sv. rewrite (nm_U E 33 _ 0 E33), Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 1)) with 256. exact Hcbz.
           ++ cbn. nlia.
           ++ intros kk Hk. cbn in Hk. assert (kk = 0%nat) as -> by nlia.
              replace (id + 3 + Z.of_nat i + 0 + Z.of_nat 0) with (id + 3 + Z.of_nat i) by nlia.
              rewrite Md. f_equal. rewrite le_byte_small by (first [change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256; exact Hcbz | cbn; nlia]). change (8 * Z.of_nat 0) with 0.
              rewrite Z.shiftr_0_r. symmetry. apply nm_byte_of_bz.
    + apply pairwise_disjoint_of_extents. unfold name_loop_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 17%nat (p + 1 + Z.of_nat i) E17) by nlia. rewrite (VB 6%nat (id + 3 + Z.of_nat i) E6) by nlia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. nclean. repeat split; nlia.
    + split; [|split; exact I].
      cbn [name_loop_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E16, E32, E33, E11, E12, E6. rewrite !nm_unsigned by (unfold SB_ING; nlia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. nclean. unfold SB_ING. repeat split; nlia.
  - assert (UB : U E BXN = SHADOW_OFF) by (unfold BXN; rewrite (nm_U E 16 SB_ING 0 E16); reflexivity).
    unfold sh_ok, SH_name_loop. repeat apply Forall_cons; try apply Forall_nil.
    + apply (shent_ok_of_range SEGS (w_H W) memL E BXN 11 p len (p + 1 + Z.of_nat i) 0 1 RAp UB).
      * rewrite (nm_U E 11 _ 0 E11), Z.add_0_r. apply Z.mod_small. nlia.
      * nlia.
      * nlia.
      * intros x Hx. apply PAPP. nlia.
    + apply (shent_ok_of_range SEGS (w_H W) memL E BXN 12 id 38 (id + 3 + Z.of_nat i) 0 1 RAr UB).
      * rewrite (nm_U E 12 _ 0 E12), Z.add_0_r. apply Z.mod_small. nlia.
      * nlia.
      * nlia.
      * intros x Hx. apply RAPP. nlia.
    + apply (shent_ok_of_range SEGS (w_H W) memL E BXN 6 id 38 (id + 3 + Z.of_nat i) 0 1 RAr UB).
      * rewrite (nm_U E 6 _ 0 E6), Z.add_0_r. apply Z.mod_small. nlia.
      * nlia.
      * nlia.
      * intros x Hx. apply RAPP. nlia.
Qed.
(* ---- the copy loop: 0x83b7c .. 0x83bbc, induction on the iterations still to run --------------- *)
Lemma name_loop : forall (n i : nat) regsL memL mdL,
  (i + n = NN)%nat -> (0 < n)%nat -> (forall j, (j < i)%nat -> bz (nthb pb (1 + j)) <> 0) ->
  nm_regs regsL -> nm_mem i memL mdL ->
  getr regsL 11 = w64 (p + 1 + Z.of_nat i) -> getr regsL 17 = w64 (p + 1 + Z.of_nat i) ->
  getr regsL 12 = w64 (id + 3 + Z.of_nat i) -> getr regsL 6 = w64 (id + 3 + Z.of_nat i) ->
  getr regsL 14 = w64 (id + 3) -> getr regsL 15 = w64 (- Z.of_nat i) ->
  getr regsL 5 = w64 (- Z.of_nat NN) -> getr regsL 13 = w64 (Z.of_nat NN) ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + AF_name_head)) memL (seg_rom SEGS)) mdL) POST.
Proof.
  induction n as [|n IH]; intros i regsL memL mdL Hin Hn Hnz HRG HM R11 R17 R12 R6 R14 R15 R5 R13; [nlia|].
  assert (Hi : (i < NN)%nat) by nlia.
  destruct (nm_loop_ok i regsL memL mdL Hi HRG HM R11 R17 R12 R6) as [HS SHOK].
  pose proof HRG as (R10 & R16 & R2 & RCS). pose proof HM as (HJ & KL & NB & GL).
  nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & Himg & RAPP & PAPP & HARc & Hslo & Hshi).
  destruct nm_cfacts as (_ & _ & RW & MBr & Hlidb & MBp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (Hiz : 0 <= Z.of_nat i <= 15 /\ Z.of_nat i + 2 <= len /\ 1 <= Z.of_nat NN <= 16 /\
                (Z.of_nat NN <= len - 1)%Z) by (rewrite HNN in *; nlia).
  destruct Hiz as (Hi15 & Hil & HN16 & HNl).
  pose proof (nm_bz (nthb pb (1 + i))) as Hbz. pose proof (nm_bz (nthb idb (3 + i))) as Hcbz.
  remember (Eimg (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i)))) n)
    by (intros nn Hnn; subst E; apply Eimg_low; exact Hnn).
  assert (E2 : ew E 2 = w64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 2 2%bv eq_refl); exact R2).
  assert (E5 : ew E 5 = w64 (- Z.of_nat NN))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 5 5%bv eq_refl); exact R5).
  assert (E6 : ew E 6 = w64 (id + 3 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 6 6%bv eq_refl); exact R6).
  assert (E10 : ew E 10 = w64 id)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E11 : ew E 11 = w64 (p + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 11 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = w64 (id + 3 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (Z.of_nat NN))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 (id + 3))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 14 14%bv eq_refl); exact R14).
  assert (E15 : ew E 15 = w64 (- Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 15 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 16 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 (p + 1 + Z.of_nat i))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E32 : ew E 32 = w64 (bz (nthb pb (1 + i))))
    by (rewrite EL by (unfold A_TEXT; nlia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (bz (nthb idb (3 + i))))
    by (rewrite EL by (unfold A_TEXT; nlia); exact (ew_Ereg_extra regsL _ 1)).
  assert (HAE : env_agree 32 (Ereg regsL (nm_lextra (nthb pb (1 + i)) (nthb idb (3 + i)))) E)
    by (split; [intros nn Hnn; apply EL; unfold A_TEXT; nlia | subst E; reflexivity]).
  clear HE EL.
  assert (U6 : bv_unsigned (ew E 6) = id + 3 + Z.of_nat i) by (rewrite E6; apply nm_unsigned; nlia).
  assert (KEEPI : nm_kept W (nm_win (id + 3 + Z.of_nat i)) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : nm_grown W memL memL) by (intros a Ha; exact Ha).
  (* 0x83b7c .. 0x83b90: the shadow test of p[1 + i], the load, beqz t2 *)
  paj_run_tok RUN HS HJ SHOK Bspan_ING; [nm_awr ltac:(exact U6) RW|].
  nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  - (* p[1 + i] = 0 *)
    assert (Hb0 : bz (nthb pb (1 + i)) = 0).
    { rewrite branch_eq_U in Hc. rewrite (nm_U _ 32%nat (bz (nthb pb (1 + i))) 0) in Hc by (ewo; exact E32).
      rewrite nm_Ulit in Hc. apply Z.eqb_eq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by nlia. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan_ING; [nm_awr ltac:(exact U6) RW|].
    nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
    psrr_branch_tok RUN BR HS SHOK Bspan_ING.
    + (* i = 0: 0x83b48 a4 := 0, then the tail *)
      assert (Hi0 : i = 0%nat).
      { rewrite branch_eq_U, nm_Ulit in Hc. rewrite (nm_U _ 15%nat (- Z.of_nat i) 0) in Hc by (ewo; exact E15).
        rewrite Z.add_0_r in Hc. apply Z.eqb_eq in Hc. destruct (Nat.eq_dec i 0) as [Hi0 | Hi0]; [exact Hi0|].
        rewrite nm_negmod in Hc by nlia. change (0 mod 2 ^ 64) with 0 in Hc. nlia. }
      clear Hc. subst i.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING AF_ing_tail; [nm_awr ltac:(exact U6) RW|].
      nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
      pmkst HS.
      nm_cs HS HAE.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
        nreg HS (14%bv : bv 5) Q14; nreg HS (2%bv : bv 5) Q2;
        pose proof (nm_val1 _ _ _ (YP09.mkRegion (Some 6%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))])
                      6%nat 0 (SOff 33 0) (bz (nthb idb (3 + 0))) HS
                      ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 33%nat (bz (nthb idb (3 + 0))) 0) by (ewo; exact E33);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U6, Z.add_0_r, nm_byte_of_bz in Md;
        assert (HNL0 : RcIdentModel.name_len pb = 0%nat)
          by (apply RcIdentLib.name_len_hit; [nlia | nlia | exact Hb0 | intros j Hj; nlia]);
        apply (name_fin (ms_regs msF) (ms_mem msF) _ 0)
      end.
      * rewrite Q2. apply nm_sv. rewrite (nm_U _ 2%nat (spZ regs - 32) 0) by (ewo; exact E2). rewrite Z.add_0_r. reflexivity.
      * intros q Hq Hq2. rewrite (RCS' q Hq Hq2). exact (RCS q Hq Hq2).
      * exact HJ.
      * rewrite Q14. reflexivity.
      * nlia.
      * rewrite RcIdentLib.ING_name_zero by (right; exact HNL0). reflexivity.
      * intros a Ha Hnr. apply (nm_kl_same 0 memL (ms_mem msF) ltac:(nlia) KL KEEPI Md a Ha). nlia.
      * intros a Hpa. apply GROWI. apply GL. exact Hpa.
      * rewrite RcIdentLib.ING_name_zero by (right; exact HNL0). cbn [snd].
        intros j Hj. rewrite Hlidb in Hj.
        rewrite (nth_error_nth' _ (RcIdentModel.zb 0)) by nlia. fold (nthb idb j).
        apply nm_idb_byte; [exact Hj|].
        apply (nm_kl_same 0 memL (ms_mem msF) ltac:(nlia) KL KEEPI Md); nlia.
    + (* i > 0: 0x83be4 a3 := -a5 = i, then the NUL store *)
      assert (Hi0 : (0 < i)%nat).
      { rewrite branch_eq_U, nm_Ulit in Hc. rewrite (nm_U _ 15%nat (- Z.of_nat i) 0) in Hc by (ewo; exact E15).
        rewrite Z.add_0_r in Hc. apply Z.eqb_neq in Hc. destruct (Nat.eq_dec i 0) as [Hi0 | Hi0]; [|nlia].
        exfalso. apply Hc. subst i. reflexivity. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING AF_name_exit; [nm_awr ltac:(exact U6) RW|].
      nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
      pmkst HS.
      nm_cs HS HAE.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
        nreg HS (10%bv : bv 5) Q10; nreg HS (16%bv : bv 5) Q16; nreg HS (2%bv : bv 5) Q2;
        nreg HS (14%bv : bv 5) Q14; nreg HS (13%bv : bv 5) Q13;
        pose proof (nm_val1 _ _ _ (YP09.mkRegion (Some 6%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))])
                      6%nat 0 (SOff 33 0) (bz (nthb idb (3 + i))) HS
                      ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 33%nat (bz (nthb idb (3 + i))) 0) by (ewo; exact E33);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U6, Z.add_0_r, nm_byte_of_bz in Md;
        apply (name_exit i (ms_regs msF) (ms_mem msF) _)
      end.
      * nlia.
      * apply RcIdentLib.name_len_hit; [nlia | nlia | exact Hb0 | exact Hnz].
      * split; [|split; [|split]].
        -- rewrite Q10. apply nm_sv. rewrite (nm_U _ 10%nat id 0) by (ewo; exact E10). rewrite Z.add_0_r. reflexivity.
        -- rewrite Q16. apply nm_sv. rewrite (nm_U _ 16%nat SB_ING 0) by (ewo; exact E16). rewrite Z.add_0_r. reflexivity.
        -- rewrite Q2. apply nm_sv. rewrite (nm_U _ 2%nat (spZ regs - 32) 0) by (ewo; exact E2). rewrite Z.add_0_r. reflexivity.
        -- intros q Hq Hq2. rewrite (RCS' q Hq Hq2). exact (RCS q Hq Hq2).
      * split; [exact HJ|]. split; [|split].
        -- exact (nm_kl_same i memL (ms_mem msF) ltac:(nlia) KL KEEPI Md).
        -- exact (nm_nb_same i memL (ms_mem msF) ltac:(nlia) NB KEEPI).
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
      * rewrite Q14. apply nm_sv. rewrite (nm_U _ 14%nat (id + 3) 0) by (ewo; exact E14). rewrite Z.add_0_r. reflexivity.
      * rewrite Q13. apply nm_sv. rewrite U_SAlu. cbn [zalu_raw].
        rewrite nm_Ulit, (nm_U _ 15%nat (- Z.of_nat i) 0) by (ewo; exact E15).
        unfold zcanon, M64. rewrite Z.add_0_r, Zminus_mod_idemp_r. change (0 mod 2 ^ 64) with 0.
        f_equal; nlia.
  - (* p[1 + i] <> 0: 0x83b94 .. 0x83bbc, the store, the counters, bne t0,a5 *)
    assert (Hb0 : bz (nthb pb (1 + i)) <> 0).
    { rewrite branch_eq_U in Hc. rewrite (nm_U _ 32%nat (bz (nthb pb (1 + i))) 0) in Hc by (ewo; exact E32).
      rewrite nm_Ulit in Hc. apply Z.eqb_neq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by nlia. exact Hc. }
    clear Hc.
    assert (Hnz' : forall j, (j < Datatypes.S i)%nat -> bz (nthb pb (1 + j)) <> 0).
    { intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hji]; [exact Hb0 | apply Hnz; nlia]. }
    paj_run_tok RUN HS HJ SHOK Bspan_ING; [nm_awr ltac:(exact U6) RW|].
    nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
    psrr_branch_tok RUN BR HS SHOK Bspan_ING.
    + (* t0 <> a5: the next iteration *)
      assert (HnN : Datatypes.S i <> NN).
      { rewrite branch_ne_U in Hc. rewrite (nm_U _ 5%nat (- Z.of_nat NN) 0) in Hc by (ewo; exact E5).
        rewrite (nm_U _ 15%nat (- Z.of_nat i) (-1)) in Hc by (ewo; exact E15).
        replace (- Z.of_nat NN + 0) with (- Z.of_nat NN) in Hc by nlia.
        replace (- Z.of_nat i + -1) with (- (Z.of_nat i + 1)) in Hc by nlia.
        rewrite !nm_negmod in Hc by nlia. apply negb_true_iff, Z.eqb_neq in Hc. nlia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING AF_name_head; [nm_awr ltac:(exact U6) RW|].
      nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
      pmkst HS.
      nm_cs HS HAE.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
        nreg HS (10%bv : bv 5) Q10; nreg HS (16%bv : bv 5) Q16; nreg HS (2%bv : bv 5) Q2;
        nreg HS (11%bv : bv 5) Q11; nreg HS (17%bv : bv 5) Q17; nreg HS (12%bv : bv 5) Q12;
        nreg HS (6%bv : bv 5) Q6; nreg HS (14%bv : bv 5) Q14; nreg HS (15%bv : bv 5) Q15;
        nreg HS (5%bv : bv 5) Q5; nreg HS (13%bv : bv 5) Q13;
        pose proof (nm_val1 _ _ _ (YP09.mkRegion (Some 6%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))])
                      6%nat 0 (SOff 32 0) (bz (nthb pb (1 + i))) HS
                      ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 32%nat (bz (nthb pb (1 + i))) 0) by (ewo; exact E32);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U6, Z.add_0_r, nm_byte_of_bz in Md;
        apply (IH (Datatypes.S i) (ms_regs msF) (ms_mem msF) _)
      end.
      * nlia.
      * nlia.
      * exact Hnz'.
      * split; [|split; [|split]].
        -- rewrite Q10. apply nm_sv. rewrite (nm_U _ 10%nat id 0) by (ewo; exact E10). rewrite Z.add_0_r. reflexivity.
        -- rewrite Q16. apply nm_sv. rewrite (nm_U _ 16%nat SB_ING 0) by (ewo; exact E16). rewrite Z.add_0_r. reflexivity.
        -- rewrite Q2. apply nm_sv. rewrite (nm_U _ 2%nat (spZ regs - 32) 0) by (ewo; exact E2). rewrite Z.add_0_r. reflexivity.
        -- intros q Hq Hq2. rewrite (RCS' q Hq Hq2). exact (RCS q Hq Hq2).
      * split; [exact HJ|]. split; [|split].
        -- exact (nm_kl_step i memL (ms_mem msF) KL KEEPI).
        -- exact (nm_nb_step i memL (ms_mem msF) ltac:(nlia) NB KEEPI Md).
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
      * rewrite Q11. apply nm_sv. rewrite (nm_U _ 11%nat (p + 1 + Z.of_nat i) 1) by (ewo; exact E11). f_equal; nlia.
      * rewrite Q17. apply nm_sv. rewrite (nm_U _ 17%nat (p + 1 + Z.of_nat i) 1) by (ewo; exact E17). f_equal; nlia.
      * rewrite Q12. apply nm_sv. rewrite (nm_U _ 12%nat (id + 3 + Z.of_nat i) 1) by (ewo; exact E12). f_equal; nlia.
      * rewrite Q6. apply nm_sv. rewrite (nm_U _ 6%nat (id + 3 + Z.of_nat i) 1) by (ewo; exact E6). f_equal; nlia.
      * rewrite Q14. apply nm_sv. rewrite (nm_U _ 14%nat (id + 3) 0) by (ewo; exact E14). f_equal; nlia.
      * rewrite Q15. apply nm_sv. rewrite (nm_U _ 15%nat (- Z.of_nat i) (-1)) by (ewo; exact E15). f_equal; nlia.
      * rewrite Q5. apply nm_sv. rewrite (nm_U _ 5%nat (- Z.of_nat NN) 0) by (ewo; exact E5). f_equal; nlia.
      * rewrite Q13. apply nm_sv. rewrite (nm_U _ 13%nat (Z.of_nat NN) 0) by (ewo; exact E13). f_equal; nlia.
    + (* t0 = a5: n bytes copied; 0x83bc0 j 0x83be8, the NUL store *)
      assert (HnN : Datatypes.S i = NN).
      { rewrite branch_ne_U in Hc. rewrite (nm_U _ 5%nat (- Z.of_nat NN) 0) in Hc by (ewo; exact E5).
        rewrite (nm_U _ 15%nat (- Z.of_nat i) (-1)) in Hc by (ewo; exact E15).
        replace (- Z.of_nat NN + 0) with (- Z.of_nat NN) in Hc by nlia.
        replace (- Z.of_nat i + -1) with (- (Z.of_nat i + 1)) in Hc by nlia.
        rewrite !nm_negmod in Hc by nlia. apply negb_false_iff, Z.eqb_eq in Hc. nlia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING AF_name_exit; [nm_awr ltac:(exact U6) RW|].
      nm_keep ltac:(fun Hr => rewrite ?U6 in Hr; unfold nm_win; nlia).
      pmkst HS.
      nm_cs HS HAE.
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
        nreg HS (10%bv : bv 5) Q10; nreg HS (16%bv : bv 5) Q16; nreg HS (2%bv : bv 5) Q2;
        nreg HS (14%bv : bv 5) Q14; nreg HS (13%bv : bv 5) Q13;
        pose proof (nm_val1 _ _ _ (YP09.mkRegion (Some 6%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))])
                      6%nat 0 (SOff 32 0) (bz (nthb pb (1 + i))) HS
                      ltac:(cbn [ss_mem In]; right; left; reflexivity) eq_refl
                      ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
                      ltac:(apply nm_sv; rewrite (nm_U _ 32%nat (bz (nthb pb (1 + i))) 0) by (ewo; exact E32);
                            rewrite Z.add_0_r; reflexivity)
                      ltac:(change (2 ^ 8) with 256; apply nm_bz)) as Md;
        cbn [ms_mem restrict] in Md; ewo_in Md; rewrite U6, Z.add_0_r, nm_byte_of_bz in Md;
        apply (name_exit (Datatypes.S i) (ms_regs msF) (ms_mem msF) _)
      end.
      * nlia.
      * rewrite HnN, HNN. apply RcIdentLib.name_len_full; [nlia|]. rewrite <- HNN, <- HnN. exact Hnz'.
      * split; [|split; [|split]].
        -- rewrite Q10. apply nm_sv. rewrite (nm_U _ 10%nat id 0) by (ewo; exact E10). rewrite Z.add_0_r. reflexivity.
        -- rewrite Q16. apply nm_sv. rewrite (nm_U _ 16%nat SB_ING 0) by (ewo; exact E16). rewrite Z.add_0_r. reflexivity.
        -- rewrite Q2. apply nm_sv. rewrite (nm_U _ 2%nat (spZ regs - 32) 0) by (ewo; exact E2). rewrite Z.add_0_r. reflexivity.
        -- intros q Hq Hq2. rewrite (RCS' q Hq Hq2). exact (RCS q Hq Hq2).
      * split; [exact HJ|]. split; [|split].
        -- exact (nm_kl_step i memL (ms_mem msF) KL KEEPI).
        -- exact (nm_nb_step i memL (ms_mem msF) ltac:(nlia) NB KEEPI Md).
        -- intros a Hpa. apply GROWI. apply GL. exact Hpa.
      * rewrite Q14. apply nm_sv. rewrite (nm_U _ 14%nat (id + 3) 0) by (ewo; exact E14). f_equal; nlia.
      * rewrite Q13. apply nm_sv. rewrite (nm_U _ 13%nat (Z.of_nat NN) 0) by (ewo; exact E13). f_equal; nlia.
Qed.
(* ---- 0x83b50 .. 0x83b78: n := min(len - 1, 16), the pointers and the counters ------------------ *)
Lemma name_arm :
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_ing_name)) memT (seg_rom SEGS)) mdT) POST.
Proof.
  nm_arm.
  destruct nm_lay as (Hsp & Hceil & Hid0 & Hid1 & Hp0 & Hp1 & Hpi & Hspi & Himg & RAPP & PAPP & HARc & Hslo & Hshi).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNN : NN = Nat.min (length pb - 1) 16) by reflexivity.
  assert (HN1 : (1 <= NN)%nat) by (rewrite HNN; nlia).
  remember (Eimg (Ereg regsT [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsT []) n)
    by (intros nn Hnn; subst E; apply Eimg_low; exact Hnn).
  assert (E2 : ew E 2 = w64 (spZ regs - 32))
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsT _ 2 2%bv eq_refl); exact T2).
  assert (E10 : ew E 10 = w64 id)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsT _ 10 10%bv eq_refl); exact T10).
  assert (E12 : ew E 12 = w64 p)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsT _ 12 12%bv eq_refl); exact T12).
  assert (E13 : ew E 13 = w64 len)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsT _ 13 13%bv eq_refl); exact T13).
  assert (E16 : ew E 16 = w64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; nlia); rewrite (ew_Ereg_nat regsT _ 16 16%bv eq_refl); exact T16).
  assert (HAE : env_agree 32 (Ereg regsT []) E)
    by (split; [intros nn Hnn; apply EL; unfold A_TEXT; nlia | subst E; reflexivity]).
  assert (HS : st_ok_pi SEGS VAL E ss_name_ent
                 (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + AF_ing_name)) memT (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_name_ent. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn. exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS BXN [] E (mrestrict (w_H W) memT)) by apply Forall_nil.
  clear HE EL.
  assert (KEEPI : nm_kept W nm_none memT memT) by (intros a _ _; reflexivity).
  assert (GROWI : nm_grown W memT memT) by (intros a Ha; exact Ha).
  paj_run_tok RUN HS HJT SHOK Bspan_ING; [awr_ok_tac|].
  nm_keep ltac:(fun Hr => nlia).
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  all: rewrite branch_ltu_U in Hc; rewrite (nm_U _ 13%nat len (-1)) in Hc by (ewo; exact E13);
       rewrite nm_Ulit in Hc; rewrite !Z.mod_small in Hc by nlia.
  1: apply Z.ltb_lt in Hc; assert (HNz : Z.of_nat NN = len - 1) by (rewrite HNN; nlia).
  2: apply Z.ltb_ge in Hc; assert (HN16 : NN = 16%nat) by (rewrite HNN; nlia).
  all: clear Hc.
  all: paj_run_to_tok RUNTO HS HJT SHOK Bspan_ING AF_name_head; [awr_ok_tac|].
  all: nm_keep ltac:(fun Hr => nlia).
  all: pmkst HS.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
        rename ms into msF;
    let HAE' := fresh "HAE'" in
    assert (HAE' : env_agree 32 (Ereg regsT []) Ex)
      by (eapply nm_agree_ext; [exact HAE | split; [intros nn Hnn; ewo; reflexivity | reflexivity]]);
    pose proof (nm_cs_of _ _ _ regsT _ HS HAE' ltac:(vm_compute; reflexivity)) as RCS';
    cbn [ms_regs restrict] in RCS';
    nreg HS (10%bv : bv 5) Q10; nreg HS (16%bv : bv 5) Q16; nreg HS (2%bv : bv 5) Q2;
    nreg HS (11%bv : bv 5) Q11; nreg HS (17%bv : bv 5) Q17; nreg HS (12%bv : bv 5) Q12;
    nreg HS (6%bv : bv 5) Q6; nreg HS (14%bv : bv 5) Q14; nreg HS (15%bv : bv 5) Q15;
    nreg HS (5%bv : bv 5) Q5; nreg HS (13%bv : bv 5) Q13;
    apply (name_loop NN 0 (ms_regs msF) (ms_mem msF) _)
  end.
  all: try nlia.
  all: try (intros j Hj; nlia).
  all: try (split; [|split; [|split]];
       [ rewrite Q10; apply nm_sv; rewrite (nm_U _ 10%nat id 0) by (ewo; exact E10); rewrite Z.add_0_r; reflexivity
       | rewrite Q16; apply nm_sv; rewrite (nm_U _ 16%nat SB_ING 0) by (ewo; exact E16); rewrite Z.add_0_r; reflexivity
       | rewrite Q2; apply nm_sv; rewrite (nm_U _ 2%nat (spZ regs - 32) 0) by (ewo; exact E2); rewrite Z.add_0_r; reflexivity
       | intros q Hq Hq2; rewrite (RCS' q Hq Hq2); exact (TCS q Hq Hq2) ]).
  all: try (split; [exact HJT|]; split; [|split];
       [ intros a Ha _; exact (KEEPI a Ha ltac:(unfold nm_none; tauto))
       | intros j Hj; nlia
       | intros a Hpa; apply GROWI; exact Hpa ]).
  all: try (rewrite Q11; apply nm_sv; rewrite (nm_U _ 12%nat p 1) by (ewo; exact E12); f_equal; nlia).
  all: try (rewrite Q17; apply nm_sv; rewrite (nm_U _ 12%nat p 1) by (ewo; exact E12); f_equal; nlia).
  all: try (rewrite Q12; apply nm_sv; rewrite (nm_U _ 10%nat id 3) by (ewo; exact E10); f_equal; nlia).
  all: try (rewrite Q6; apply nm_sv; rewrite (nm_U _ 10%nat id 3) by (ewo; exact E10); f_equal; nlia).
  all: try (rewrite Q14; apply nm_sv; rewrite (nm_U _ 10%nat id 3) by (ewo; exact E10); f_equal; nlia).
  all: try (rewrite Q15; reflexivity).
  all: try (rewrite Q13; apply nm_sv; rewrite (nm_U _ 13%nat len (-1)) by (ewo; exact E13); f_equal; nlia).
  all: try (rewrite Q13; apply nm_sv; rewrite nm_Ulit; rewrite HN16; reflexivity).
  all: try (rewrite Q5; apply nm_sv; rewrite U_SAlu; cbn [zalu_raw];
            rewrite nm_Ulit, (nm_U _ 13%nat len (-1)) by (ewo; exact E13);
            unfold zcanon, M64; rewrite Zminus_mod_idemp_r; change (0 mod 2 ^ 64) with 0; f_equal; nlia).
  all: try (rewrite Q5; apply nm_sv; rewrite nm_Ulit; rewrite HN16; reflexivity).
Qed.
End arm.
(* The model-name arm, as IngestSeg.v states it. *)
Theorem pb_ting_seg_name : ting_seg_name B.
Proof.
  unfold ting_seg_name.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb regsT memT mdT HARM Had H2.
  eapply name_arm; eassumption.
Qed.
End h.
End f2.
End d2.
