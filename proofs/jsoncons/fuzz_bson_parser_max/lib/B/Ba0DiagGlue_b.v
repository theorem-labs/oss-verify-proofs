(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0DiagWritev_b Ba0DiagKit_b Ba0DiagChk_b Ba0DiagMemcpy_b Ba0DiagStrnlen_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DG.

Import DK. Import DSN.

Ltac alia := first [ lia | match goal with H : _ \/ _ |- _ => destruct H; lia end ].
Ltac sc := first [ assumption | reflexivity | dk_rk | dk_gmem | (dk_arith_goal; alia) ].

(* [comment removed for export] *)
Definition diag_cells (M : word -> option byte) (can : Z) : Prop :=
  L5.u8_at RSEGS M 1313048 1 /\ L5.u8_at RSEGS M 1313049 1 /\ L5.u8_at RSEGS M 1906620 1 /\ L5.u64_at RSEGS M 1309752 2147450880
  /\ L5.u64_at RSEGS M 1282896 1184024 /\ L5.u64_at RSEGS M 1283272 1218816 /\ L5.u64_at RSEGS M 6896960 can
  (* [comment removed for export] *)
  /\ L5.u32_at RSEGS M 1293512 5 /\ L5.u64_at RSEGS M 1293608 0 /\ L5.u64_at RSEGS M 1293600 6898968 /\ L5.u32_at RSEGS M 1293648 0
  /\ L5.u32_at RSEGS M 1293652 4294967295 /\ L5.u32_at RSEGS M 1293656 4294967295 /\ L5.u64_at RSEGS M 1293584 1180112 /\ L5.u32_at RSEGS M 1293632 2
  /\ L5.writable RSEGS M 1293512 152.

Lemma cstr_rd1 M p bs t8 : cstr M p bs t8 -> rdn RSEGS M (Z_to_bv 64 p) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]).
Proof.
  intros [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS M _ _ _ (length bs + 1) A) by lia. f_equal.
  rewrite firstn_app. rewrite firstn_all2 by lia. replace (length bs + 1 - length bs)%nat with 1%nat by lia. reflexivity.
Qed.
Lemma chk_pre_intro (M : word -> option byte) p n s : 0 <= n <= 131071 -> 140735332552704 <= p -> p + n + 1 + 16 <= 2 ^ 47 ->
  140735332552704 <= s - 72 -> s <= 2 ^ 47 -> L5.writable RSEGS M (s - 72) 72 -> rt_layout_globs M ->
  (forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0)) -> chk_pre M p (n + 1) s.
Proof.
  intros Hn Hp Hpn Hs1 Hs2 W G Z0. unfold chk_pre. replace (p + (n + 1) - 1) with (p + n) by lia.
  assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). unfold SB in *.
  split; [lia|]. split; [right; unfold HIGHBEG, HIGHEND; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply (store_ok_of_writable M (s - 72) 72); [exact W | reflexivity]|]. split; [exact G | exact Z0].
Qed.
(* [comment removed for export] *)
Ltac rkb K :=
  lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    let z := eval vm_compute in (Z.of_nat k) in
    rewrite (DK.keeps_but_reg _ _ _ k (@BV 5 z I) K eq_refl) by (first [cbv; tauto | cbv; intuition discriminate]) end.
Ltac rkc K :=
  lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (DK.keeps_cs_reg _ _ k K) by (cbn; tauto) end.

(* [comment removed for export] *)
Definition filew (z : Z) : Prop :=      (* [comment removed for export] *)
  1293512 <= z < 1293516 \/ 1293520 <= z < 1293536 \/ 1293544 <= z < 1293560 \/ 1293568 <= z < 1293576 \/ 1293600 <= z < 1293616 \/ 1293648 <= z < 1293652.
Definition agree0 (M M' : word -> option byte) (S : Z) : Prop :=
  forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M' x = M x.
Ltac flia := unfold filew; lia.
Ltac scc := first [ sc | dk_cell ltac:(unfold filew; dk_qlia) ].
Ltac xf0 Ms AG := dk_xf Ms AG ltac:(unfold filew; alia).
Lemma sn_cells_agree M M' S : 140735332552704 <= S - 5440 -> agree0 M M' S -> sn_cells M -> sn_cells M'.
Proof.
  intros HS AG (C1 & C2 & C3 & (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & C5 & C6).
  assert (X : forall (w : word) k bs, (bv_unsigned w + Z.of_nat k <= 1293512 \/ 1293664 <= bv_unsigned w) -> bv_unsigned w + Z.of_nat k <= 0x1000000 ->
              rdn RSEGS M w k = Some bs -> rdn RSEGS M' w k = Some bs).
  { intros w k bs Hw Hw2 H. rewrite <- H. pose proof (bv_unsigned_in_range _ w) as Rw. apply rdn_ext; [lia|]. intros x Hx. apply AG; unfold filew; lia. }
  unfold sn_cells, rt_layout_globs.
  repeat split; first [ (eapply u8_ext; [intros x Hx; apply AG; unfold filew; lia | lia | lia | eassumption])
                      | (eapply u64_ext; [intros x Hx; apply AG; unfold filew; lia | lia | lia | eassumption])
                      | (apply X; [vm_compute; (left + right); intros Q; discriminate Q | vm_compute; intros Q; discriminate Q | assumption]) ].
Qed.
Lemma mc_globs_agree M M' S : 140735332552704 <= S - 5440 -> agree0 M M' S -> mc_icpt_globs M -> mc_icpt_globs M'.
Proof.
  intros HS AG (G1 & G2 & G3).
  assert (X : forall (w : word) k bs, (bv_unsigned w + Z.of_nat k <= 1293512 \/ 1293664 <= bv_unsigned w) -> bv_unsigned w + Z.of_nat k <= 0x1000000 ->
              rdn RSEGS M w k = Some bs -> rdn RSEGS M' w k = Some bs).
  { intros w k bs Hw Hw2 H. rewrite <- H. pose proof (bv_unsigned_in_range _ w) as Rw. apply rdn_ext; [lia|]. intros x Hx. apply AG; unfold filew; lia. }
  unfold mc_icpt_globs. repeat split; (apply X; [vm_compute; (left + right); intros Q; discriminate Q | vm_compute; intros Q; discriminate Q | assumption]).
Qed.
Lemma cstr_nul M p bs t8 : 0 <= p -> p + Z.of_nat (length bs) + 9 <= 2 ^ 64 -> cstr M p bs t8 -> L5.u8_at RSEGS M (p + Z.of_nat (length bs)) 0.
Proof.
  intros Hp Hn [A _ _]. unfold L5.u8_at.
  pose proof (Ba0DiagStrlen_b.rdn_byte_at M p _ _ (length bs) A ltac:(lia) Hp ltac:(lia)) as B.
  rewrite app_nth2 in B by lia. replace (length bs - length bs)%nat with 0%nat in B by lia. exact B.
Qed.
Lemma u8_of_u32_5 M a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a 5 -> L5.u8_at RSEGS M a 5.
Proof.
  intros Ha Hb C. unfold L5.u32_at in C. unfold L5.u8_at.
  pose proof (Ba0DiagStrlen_b.rdn_byte_at M a _ _ 0%nat C ltac:(lia) Ha ltac:(lia)) as B. rewrite Z.add_0_r in B. rewrite B. repeat f_equal; try (apply bv_eq; vm_compute; reflexivity).
Qed.

(* [comment removed for export] *)
Ltac shz :=
  lazymatch goal with |- L5KA.zeros_at ?M ((?S - ?c) / 8 + ?d) ?l =>
    let q := eval vm_compute in (c / 8) in
    replace ((S - c) / 8) with (S / 8 - q) by (replace (S - c) with (S + (- q) * 8) by (clear; lia); rewrite Z_div_plus_full by (clear; lia); clear; lia);
    unfold SB in *; dk_gmem end.


(* [comment removed for export] *)
Definition PRE7 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 90394) 7 with Some l => l | None => [] end.
Definition SUF7 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 90403) 7 with Some l => l | None => [] end.
Lemma pre7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 90394) 7 = Some PRE7.  Proof. vm_compute. reflexivity. Qed.
Lemma suf7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 90403) 7 = Some SUF7.  Proof. vm_compute. reflexivity. Qed.
Lemma list_bv_eq (l1 l2 : list byte) : map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate H; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma PRE7_eq : PRE7 = [Z_to_bv 8 117; Z_to_bv 8 115; Z_to_bv 8 97; Z_to_bv 8 103; Z_to_bv 8 101; Z_to_bv 8 58; Z_to_bv 8 32].
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Lemma SUF7_eq : SUF7 = word_to_le_bytes 4 (Z_to_bv 64 1347307808) ++ [Z_to_bv 8 85; Z_to_bv 8 84; Z_to_bv 8 10].
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma rdn_43 (M : word -> option byte) a w b4 b5 b6 : 0 <= a -> a + 7 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a w -> L5.u8_at RSEGS M (a + 4) b4 -> L5.u8_at RSEGS M (a + 5) b5 -> L5.u8_at RSEGS M (a + 6) b6 ->
  rdn RSEGS M (Z_to_bv 64 a) 7 = Some (word_to_le_bytes 4 (Z_to_bv 64 w) ++ [Z_to_bv 8 b4; Z_to_bv 8 b5; Z_to_bv 8 b6]).
Proof.
  unfold L5.u32_at, L5.u8_at. intros Ha Hb C0 C4 C5 C6. change 7%nat with (4 + 3)%nat.
  apply rdn_app_Z; [lia | cbn; lia | exact C0|]. change (Z.of_nat 4) with 4.
  apply rdn_cons; [lia | cbn; lia | exact C4|]. replace (a + 4 + 1) with (a + 5) by lia.
  apply rdn_cons; [lia | cbn; lia | exact C5|]. replace (a + 5 + 1) with (a + 6) by lia. exact C6.
Qed.
(* [comment removed for export] *)
Lemma rdn_7 (M : word -> option byte) a b0 b1 b2 b3 b4 b5 b6 : 0 <= a -> a + 7 <= 2 ^ 64 ->
  L5.u8_at RSEGS M a b0 -> L5.u8_at RSEGS M (a + 1) b1 -> L5.u8_at RSEGS M (a + 2) b2 -> L5.u8_at RSEGS M (a + 3) b3 ->
  L5.u8_at RSEGS M (a + 4) b4 -> L5.u8_at RSEGS M (a + 5) b5 -> L5.u8_at RSEGS M (a + 6) b6 ->
  rdn RSEGS M (Z_to_bv 64 a) 7 = Some [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2; Z_to_bv 8 b3; Z_to_bv 8 b4; Z_to_bv 8 b5; Z_to_bv 8 b6].
Proof.
  unfold L5.u8_at. intros Ha Hb C0 C1 C2 C3 C4 C5 C6.
  apply rdn_cons; [lia | cbn; lia | exact C0|]. apply rdn_cons; [lia | cbn; lia | exact C1|].
  replace (a + 1 + 1) with (a + 2) by lia. apply rdn_cons; [lia | cbn; lia | exact C2|].
  replace (a + 2 + 1) with (a + 3) by lia. apply rdn_cons; [lia | cbn; lia | exact C3|].
  replace (a + 3 + 1) with (a + 4) by lia. apply rdn_cons; [lia | cbn; lia | exact C4|].
  replace (a + 4 + 1) with (a + 5) by lia. apply rdn_cons; [lia | cbn; lia | exact C5|].
  replace (a + 5 + 1) with (a + 6) by lia. exact C6.
Qed.
Lemma PRE7_len : length PRE7 = 7%nat.  Proof. reflexivity. Qed.
Lemma SUF7_len : length SUF7 = 7%nat.  Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stk_zsh (M : word -> option byte) S pd n : S mod 16 = 0 -> 140735332552704 + 5440 <= S <= 140737488355328 ->
  L5KA.zeros_at M (SB + S / 8 - 680) 688 -> S - 5376 <= pd -> 0 <= n -> pd + n <= S -> zsh M pd n.
Proof.
  intros Hal HS Z0 H1 Hn H2. apply zsh_of_hull. intros x Hx. unfold SB in *.
  assert (E : S = 8 * (S / 8)).
  { pose proof (Z.div_mod S 16 ltac:(lia)) as D16. rewrite Hal in D16.
    assert (Q : S / 8 = 2 * (S / 16)) by (symmetry; apply (Z.div_unique S 8 (2 * (S / 16)) 0); lia). lia. }
  assert (L1 : S / 8 - 672 <= pd / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (pd + n - 1) / 8 <= S / 8) by (apply Z.div_le_upper_bound; lia).
  assert (R8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  specialize (Z0 (bv_unsigned x - (2147450880 + S / 8 - 680)) ltac:(lia)).
  replace (2147450880 + S / 8 - 680 + (bv_unsigned x - (2147450880 + S / 8 - 680))) with (bv_unsigned x) in Z0 by lia.
  rewrite Z_to_bv_bv_unsigned in Z0. exact Z0.
Qed.

Lemma memcpy_stage fx (R : bvmap 5 word) (M : word -> option byte) (s pd ps n : Z) (bs : list byte) :
  getr R (reg 1) = Z_to_bv 64 1182924 -> getr R (reg 2) = Z_to_bv 64 s -> getr R (reg 10) = Z_to_bv 64 pd -> getr R (reg 11) = Z_to_bv 64 ps -> getr R (reg 12) = Z_to_bv 64 n ->
  n = Z.of_nat (length bs) -> n <= 2 ^ 40 ->
  140735332552704 <= s - 2232 -> s <= 2 ^ 47 -> in_app8 ps n -> in_app8 pd n -> 0 < ps -> 0 < pd ->
  (ps + n <= s - 2232 \/ s <= ps) -> (pd + n <= s - 2232 \/ s <= pd) -> (pd + n <= ps \/ ps + n <= pd) ->
  L5.writable RSEGS M (s - 2232) 2232 -> L5.writable RSEGS M pd n -> rdn RSEGS M (Z_to_bv 64 ps) (length bs) = Some bs ->
  rt_layout_globs M -> mc_icpt_globs M -> zsh M ps n -> zsh M pd n ->
  exists R' M',
    msteps RSEGS (st fx R 0x77c90 M) (st fx R' 1182924 M')
    /\ getr R' (reg 10) = Z_to_bv 64 pd
    /\ (forall k, In k [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k))
    /\ (forall x : word, bv_unsigned x < s - 2232 \/ s <= bv_unsigned x -> ~ (pd <= bv_unsigned x < pd + n) -> M' x = M x)
    /\ mem_grows M M'
    /\ rdn RSEGS M' (Z_to_bv 64 pd) (length bs) = Some bs.
Proof.
  intros G1 G2 G10 G11 G12 En Hn Hs1 Hs2 HappS HappD Hps0 Hpd0 DJS DJD OV W1 W2 RD HG HI ZS ZD.
  assert (Hps : 0 <= ps /\ ps + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
  assert (Hpd : 0 <= pd /\ pd + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
  dk_fpreg_in G1. dk_fpreg_in G2. dk_fpreg_in G10. dk_fpreg_in G11. dk_fpreg_in G12.
  assert (RET : ret_ok (Z_to_bv 64 1182924)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Dps : 0 <= (ps + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHBEG, HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Dpd : 0 <= (pd + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHBEG, HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (@diag_memcpy fx M s pd ps n bs (Z_to_bv 64 1182924) R) as (R' & Mj & RUN & V10 & KCS & OUT & GR).
  - lia.
  - exact HappS.
  - exact HappD.
  - lia.
  - lia.
  - unfold SB. lia.
  - unfold SB. lia.
  - intros _. exact DJS.
  - intros _. exact DJD.
  - exact OV.
  - apply (store_ok_of_writable M (s - 2232) 2232); [exact W1 | reflexivity].
  - apply (store_ok_of_writable M pd n); [exact W2 | rewrite En; rewrite Nat2Z.id; reflexivity].
  - rewrite En, Nat2Z.id. exact RD.
  - exact RET.
  - exact HG.
  - exact HI.
  - exact ZS.
  - exact ZD.
  - exact G1.
  - exact G2.
  - exact G10.
  - exact G11.
  - exact G12.
  - exists R', (wbytes Mj (Z_to_bv 64 pd) bs). unfold HIGHBEG, HIGHEND in *.
    split. { replace (0x77c90%bv : word) with (Z_to_bv 64 0x77c90) in RUN by (apply bv_eq; reflexivity). exact RUN. }
    split. { rewrite (getr_reg R' 10 10%bv eq_refl). exact V10. }
    split. { intros k Hk. apply (keeps_cs_reg R R' k KCS Hk). }
    split. { intros x Hx Hd. rewrite MemSplit.wbytes_outside; [apply OUT; exact Hx | rewrite L5.unsigned_lit by lia; lia | rewrite L5.unsigned_lit by lia; lia]. }
    split. { eapply mem_grows_trans; [exact GR | apply wbytes_grows]. }
    apply SeqExec.rdn_wbytes_hit. rewrite L5.unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma wv_entry_stage fx (R : bvmap 5 word) (M : word -> option byte) (f sp buf len wpos wbase fd : Z) :
  getr R (reg 9) = Z_to_bv 64 f -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 buf -> getr R (reg 8) = Z_to_bv 64 len ->
  0 <= sp -> sp + 40 < 2 ^ 63 -> 0 <= f -> (f + 124 <= sp + 8 \/ sp + 40 <= f) -> f + 124 < 2 ^ 63 ->
  0 <= wbase <= wpos -> wpos < 2 ^ 63 -> 0 <= len < 2 ^ 62 -> 0 <= buf < 2 ^ 64 -> 0 <= fd < 2 ^ 31 ->
  L5.u64_at RSEGS M (f + 40) wpos -> L5.u64_at RSEGS M (f + 56) wbase -> L5.u32_at RSEGS M (f + 120) fd -> L5.writable RSEGS M (sp + 8) 32 ->
  exists R' M',
    msteps RSEGS (st fx R 0x12020c M) (st fx R' 0x120258 M')
    /\ getr R' (reg 17) = Z_to_bv 64 66 /\ getr R' (reg 10) = Z_to_bv 64 fd
    /\ getr R' (reg 11) = Z_to_bv 64 (if Z.eqb wpos wbase then sp + 24 else sp + 8) /\ getr R' (reg 12) = Z_to_bv 64 (if Z.eqb wpos wbase then 1 else 2)
    /\ getr R' (reg 18) = Z_to_bv 64 (if Z.eqb wpos wbase then 1 else 2) /\ getr R' (reg 19) = Z_to_bv 64 (if Z.eqb wpos wbase then sp + 24 else sp + 8)
    /\ getr R' (reg 22) = Z_to_bv 64 (wpos - wbase + len)
    /\ (forall k, In k [1; 2; 3; 4; 8; 9; 20; 21; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k))
    /\ L5.u64_at RSEGS M' (sp + 8) wbase /\ L5.u64_at RSEGS M' (sp + 16) (wpos - wbase) /\ L5.u64_at RSEGS M' (sp + 24) buf /\ L5.u64_at RSEGS M' (sp + 32) len
    /\ (forall x : word, ~ (sp + 8 <= bv_unsigned x < sp + 40) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros G9 G2 G11 G8 Hs0 Hs1 Hf0 Hfs Hf1 Hw0 Hw1 Hlen Hbuf Hfd C40 C56 C120 W.
  dk_fpreg_in G9. dk_fpreg_in G2. dk_fpreg_in G11. dk_fpreg_in G8.
  destruct (@wv_entry fx M (seg_rom RSEGS) f sp buf len wpos wbase fd (conj Hs0 Hs1) (conj Hf0 (conj Hfs Hf1)) (conj Hw0 Hw1) Hlen Hfd C40 C56 C120
              (store_ok_of_writable M (sp + 8) 32 32 W eq_refl) R G9 G2 G11 G8) as (R' & RUN & V17 & V10 & V11 & V12 & V18 & V19 & V22 & K).
  exists R', (wve_mem M sp buf len wpos wbase).
  replace (0x12020c%bv : word) with (Z_to_bv 64 0x12020c) in RUN by (apply bv_eq; reflexivity).
  replace (0x120258%bv : word) with (Z_to_bv 64 0x120258) in RUN by (apply bv_eq; reflexivity).
  unfold wve_iov, wve_cnt in *.
  split; [exact RUN|].
  split. { rewrite (getr_reg R' 17 17%bv eq_refl). exact V17. } split. { rewrite (getr_reg R' 10 10%bv eq_refl). exact V10. }
  split. { rewrite (getr_reg R' 11 11%bv eq_refl). exact V11. } split. { rewrite (getr_reg R' 12 12%bv eq_refl). exact V12. }
  split. { rewrite (getr_reg R' 18 18%bv eq_refl). exact V18. } split. { rewrite (getr_reg R' 19 19%bv eq_refl). exact V19. }
  split. { rewrite (getr_reg R' 22 22%bv eq_refl). exact V22. }
  split. { intros k Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [dk_kb K|]). destruct Hk. }
  unfold wve_mem, W64.
  assert (X : forall a v Mx, 0 <= a -> a + 8 < 2 ^ 63 -> L5.u64_at RSEGS (wbytes Mx (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))) a v).
  { intros a v Mx Ha Hb. unfold L5.u64_at. apply SeqExec.rdn_wbytes_hit8. rewrite L5.unsigned_lit by lia. lia. }
  assert (Y : forall a b v w Mx, 0 <= a -> a + 8 < 2 ^ 63 -> 0 <= b -> b + 8 < 2 ^ 63 -> (a + 8 <= b \/ b + 8 <= a) -> L5.u64_at RSEGS Mx a v ->
              L5.u64_at RSEGS (wbytes Mx (Z_to_bv 64 b) (word_to_le_bytes 8 (Z_to_bv 64 w))) a v).
  { intros a b v w Mx Ha Ha' Hb Hb' D C. unfold L5.u64_at in *. rewrite rdn_wbytes_out; [exact C | | |];
      rewrite ?length_N_to_le_bytes; rewrite !L5.unsigned_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia. }
  split. { apply Y; try lia. apply Y; try lia. apply Y; try lia. apply X; lia. }
  split. { apply Y; try lia. apply Y; try lia. apply X; lia. }
  split. { apply Y; try lia. apply X; lia. }
  split. { apply X; lia. }
  split. { intros x Hx. rewrite !MemSplit.wbytes_outside; try reflexivity; rewrite ?length_N_to_le_bytes; rewrite ?L5.unsigned_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia. }
  repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.
End DG.
