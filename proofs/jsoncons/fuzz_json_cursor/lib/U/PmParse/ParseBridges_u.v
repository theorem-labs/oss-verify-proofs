(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PB.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

Lemma uv_range : forall E e, 0 <= uv E e < 2 ^ 64.
Proof. intros. unfold uv. pose proof (u64_range (edenot E e)) as H. unfold two64 in H. exact H. Qed.
Lemma uv_eaddz : forall E e z, uv E (APC.eaddz e z) = (uv E e + z) mod 2 ^ 64.
Proof.
  intros. unfold uv, APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma uv_eadd : forall E a b, uv E (APC.eadd a b) = (uv E a + uv E b) mod 2 ^ 64.
Proof. intros. unfold uv, APC.eadd. rewrite mkAlu_denot, u_add64. reflexivity. Qed.
Lemma uv_esub : forall E a b, uv E (APC.esub a b) = (uv E a - uv E b) mod 2 ^ 64.
Proof. intros. unfold uv, APC.esub. rewrite mkAlu_denot, u_sub64. reflexivity. Qed.
Lemma uv_escale : forall E c e, uv E (APC.escale c e) = (c * uv E e) mod 2 ^ 64.
Proof.
  intros. unfold uv, APC.escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma bytes_of_defined : forall (M : mem) (n : nat) (p : Z), 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> L5.defined M p (Z.of_nat n) ->
  exists s : list Z, length s = n /\ L5.bytes_at RSEGS M p s.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hb Hd.
  - exists []. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (s & Hl & Hs).
    { intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Hd. lia. }
    pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:Hb0; [|contradiction].
    exists (bv_unsigned b :: s). split; [cbn [length]; rewrite Hl; reflexivity|].
    intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. unfold rd1. rewrite Hb0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hs. cbn [length] in Hi. lia.
Qed.

Lemma defined_of_u64 : forall (M : mem) a v, L5.u64_at RSEGS M a v -> 0xf8000 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof.
  intros M a v Hu Ha H8 i Hi. unfold L5.u64_at in Hu.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) 8 _ Hu).
  - rewrite !u64_of_Z by lia. cbn. lia.
  - rewrite u64_of_Z by lia. unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma defined_str_obj : forall (M : mem) o w0 sz p, L5.u64_at RSEGS M o w0 -> L5.u64_at RSEGS M (o + 8) sz -> L5.u64_at RSEGS M (o + 16) p -> 0xf8000 <= o -> o + 24 <= 2 ^ 64 ->
  L5.defined M o 24.
Proof.
  intros M o w0 sz p H0 H8 H16 Ho Hb i Hi. destruct (Z_lt_dec i 8); [|destruct (Z_lt_dec i 16)].
  - exact (defined_of_u64 M o _ H0 ltac:(lia) ltac:(lia) i ltac:(lia)).
  - replace (o + i) with (o + 8 + (i - 8)) by lia. exact (defined_of_u64 M (o + 8) _ H8 ltac:(lia) ltac:(lia) (i - 8) ltac:(lia)).
  - replace (o + i) with (o + 16 + (i - 16)) by lia. exact (defined_of_u64 M (o + 16) _ H16 ltac:(lia) ltac:(lia) (i - 16) ltac:(lia)).
Qed.

Definition has := CC.has_cell.
Lemma has_ok : forall E (M : mem) cells X, know_ok RSEGS E M cells -> has cells X = true -> kentry_ok RSEGS E M X.
Proof. intros E M cells X HK H. apply CC.has_cell_In in H. exact (proj1 (Forall_forall _ _) HK X H). Qed.
Lemma fact_ok' : forall E (M : mem) cells X, know_ok RSEGS E M cells -> APC.fact_ok cells X = true -> kentry_ok RSEGS E M X.
Proof. intros E M cells X HK H. exact (APS.fact_ok_sound RSEGS E M cells X HK H). Qed.

Definition prove (cells : list kentry) (X : kentry) : bool := PPV.prove3 cells X.
Lemma prove_ok : forall E (M : mem) cells X, know_ok RSEGS E M cells -> prove cells X = true -> kentry_ok RSEGS E M X.
Proof. intros E M cells X HK H. exact (PPV.prove3_sound RSEGS E M cells X HK H). Qed.

Definition str_pat (cells : list kentry) (ob : expr) (ok : Z) (pe ce se : expr) (kmin2 smax : Z) : bool :=
  (has cells (KWord (SA ob ok) 8 (APC.eaddz ce 1)) && has cells (KWord (SA ob (ok + 8)) 8 se) && has cells (KWord (SA ob (ok + 16)) 8 pe)
   && has cells (KWord (SA (APC.eadd se pe) 0) 1 (ELit 0)) && has cells (KUnk (SA pe 0) ce) && has cells (KAlign ce 8)
   && prove cells (KRange ce kmin2 134217728) && prove cells (KRange se 0 smax) && Z.leb smax 67108864 && prove cells (KRange pe 4096 140737488355328)
   && has cells (KRange (APC.esub (APC.eaddz ce (-1)) se) 0 140737488355328))%bool.

Lemma mod_neg_wrap : forall x, - 2 ^ 63 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros x Hx. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.

Lemma str_view : forall E (M : mem) cells ob ok pe ce se kmin2 smax,
  know_ok RSEGS E M cells -> str_pat cells ob ok pe ce se kmin2 smax = true -> 24 <= kmin2 ->
  0 <= estart E (SA ob ok) -> estart E (SA ob ok) + 24 <= 2 ^ 64 ->
  let o := estart E (SA ob ok) in let p := uv E pe in let cap := uv E ce in let size := uv E se in
  exists s : list Z, PML.str_at M o (PML.SLong cap p s) /\ Z.of_nat (length s) = size /\ kmin2 <= cap <= 2 ^ 27 /\ size < cap /\ size <= smax /\ cap mod 8 = 0
                     /\ 4096 <= p <= 2 ^ 47 /\ L5.defined M p cap.
Proof.
  intros E M cells ob ok pe ce se kmin2 smax HK HP Hk Ho0 Ho1. cbv zeta. unfold str_pat in HP.
  apply andb_prop in HP as [HP P10]. apply andb_prop in HP as [HP P9]. apply andb_prop in HP as [HP P8b]. apply Z.leb_le in P8b. apply andb_prop in HP as [HP P8]. apply andb_prop in HP as [HP P7].
  apply andb_prop in HP as [HP P6]. apply andb_prop in HP as [HP P5]. apply andb_prop in HP as [HP P4]. apply andb_prop in HP as [HP P3].
  apply andb_prop in HP as [P1 P2].
  pose proof (has_ok E M _ _ HK P1) as C1. pose proof (has_ok E M _ _ HK P2) as C2. pose proof (has_ok E M _ _ HK P3) as C3.
  pose proof (has_ok E M _ _ HK P4) as C4. pose proof (has_ok E M _ _ HK P5) as C5. pose proof (has_ok E M _ _ HK P6) as C6.
  pose proof (prove_ok E M _ _ HK P7) as C7. pose proof (prove_ok E M _ _ HK P8) as C8. pose proof (prove_ok E M _ _ HK P9) as C9.
  pose proof (has_ok E M _ _ HK P10) as C10.
  cbn [kentry_ok] in C6, C7, C8, C9, C10. fold (uv E ce) in C6, C7. fold (uv E se) in C8. fold (uv E pe) in C9.
  fold (uv E (APC.esub (APC.eaddz ce (-1)) se)) in C10. rewrite uv_esub, uv_eaddz in C10.
  set (cap := uv E ce) in *. set (size := uv E se) in *. set (p := uv E pe) in *. set (o := estart E (SA ob ok)) in *.
  destruct C6 as [_ Hal].
  assert (Hc1 : (cap + -1) mod 2 ^ 64 = cap - 1) by (rewrite Z.mod_small by lia; lia). rewrite Hc1 in C10.
  assert (Hlt : size < cap).
  { destruct (Z_lt_dec (cap - 1 - size) 0) as [N|N]; [|lia]. rewrite (mod_neg_wrap (cap - 1 - size)) in C10 by lia. lia. }
  assert (Hdef : L5.defined M p cap).
  { apply (CL5.kunk_elim RSEGS E M _ _ p cap C5); [unfold estart; cbn [a_base a_off]; fold (uv E pe); fold p; lia | reflexivity]. }
  destruct (bytes_of_defined M (Z.to_nat size) p ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (s & Hls & Hbs).
  { intros i Hi. apply Hdef. rewrite Z2Nat.id in Hi by lia. lia. }
  exists s. assert (Hlen : Z.of_nat (length s) = size) by (rewrite Hls; apply Z2Nat.id; lia).
  split; [|repeat split; try lia; exact Hdef].
  unfold PML.str_at. split; [|split; [exact Hal | lia]].
  unfold L5.lstr_long. rewrite Hlen.
  assert (Hev : Z.even cap = true).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as D. rewrite Hal in D. rewrite D. rewrite Z.add_0_r, Z.even_mul. reflexivity. }
  split; [rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even, Hev; reflexivity|].
  split; [apply (CL5.kword64_elim RSEGS E M _ _ o (cap + 1) C1); [reflexivity | fold (uv E (APC.eaddz ce 1)); rewrite uv_eaddz; fold cap; apply Z.mod_small; lia]|].
  split; [apply (CL5.kword64_elim RSEGS E M _ _ (o + 8) size C2); [unfold o, estart; cbn [a_base a_off]; lia | reflexivity]|].
  split; [apply (CL5.kword64_elim RSEGS E M _ _ (o + 16) p C3); [unfold o, estart; cbn [a_base a_off]; lia | reflexivity]|].
  split; [exact Hbs|].
  apply (CL5.kword8_zero_elim RSEGS E M _ (p + size) C4). unfold estart. cbn [a_base a_off]. fold (uv E (APC.eadd se pe)). rewrite uv_eadd. fold size p.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma kword8_zero_intro : forall E (M : mem) a A, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 -> L5.u8_at RSEGS M A 0 -> kentry_ok RSEGS E M (KWord a 1 (ELit 0)).
Proof.
  intros E M a A Ha H0 H1 Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 1)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha. exact Hu.
Qed.
Lemma kword32_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u32_at RSEGS M A z -> kentry_ok RSEGS E M (KWord a 4 v).
Proof.
  intros E M a v A z Ha H0 H4 Hv Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.
Lemma edenot_of_uv : forall E e z, uv E e = z -> edenot E e = Z_to_bv 64 z.
Proof. intros E e z H. rewrite <- H. unfold uv. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma str_cells_ok : forall E (M : mem) ob ok size' g KMIN o cap p (s : list Z),
  estart E (SA ob ok) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  bv_unsigned (ev E g) = p -> bv_unsigned (ev E (g + 1)) = cap / 2 ->
  uv E size' = Z.of_nat (length s) ->
  PML.str_at M o (PML.SLong cap p s) -> 2 * KMIN <= cap <= 2 ^ 27 -> 4096 <= p <= 2 ^ 47 ->
  forall X, In X (PSU.str_cells ob ok size' g KMIN) -> kentry_ok RSEGS E M X.
Proof.
  intros E M ob ok size' g KMIN o cap p s Ho Ho0 Ho1 Hp Hk Hsz ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hlt) Hcap Hpr X HX.
  assert (Hc2 : cap = 2 * (cap / 2)).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as D. rewrite Hc8 in D. rewrite D at 2. replace (8 * (cap / 8) + 0) with ((4 * (cap / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Ucap : uv E (PSU.emul2 (EVar (g + 1))) = cap).
  { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite Hk. rewrite <- Hc2. apply Z.mod_small. lia. }
  unfold PSU.str_cells in HX. cbn [In] in HX. destruct HX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
  - apply (CL5.kword64_intro RSEGS E M _ _ o (cap + 1) Ho Ho0 ltac:(lia)); [|exact Hw0].
    apply edenot_of_uv. rewrite uv_eaddz, Ucap. apply Z.mod_small. lia.
  - apply (CL5.kword64_intro RSEGS E M _ _ (o + 8) (Z.of_nat (length s))); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | exact (edenot_of_uv _ _ _ Hsz) | exact Hw8].
  - apply (CL5.kword64_intro RSEGS E M _ _ (o + 16) p); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | | exact Hw16].
    cbn [edenot]. rewrite <- Hp. symmetry. apply Z_to_bv_bv_unsigned.
  - apply (kword8_zero_intro E M _ (p + Z.of_nat (length s))); [| lia | lia | exact Hnul].
    unfold estart. cbn [a_base a_off]. fold (uv E (PSU.eadd size' (EVar g))). unfold PSU.eadd. rewrite uv_eadd, Hsz. unfold uv. cbn [edenot]. rewrite Hp.
    rewrite Z.mod_small by lia. lia.
  - cbn [kentry_ok edenot]. rewrite Hk. split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia].
  - cbn [kentry_ok]. fold (uv E (PSU.esub (APC.eaddz (PSU.emul2 (EVar (g + 1))) (-1)) size')). unfold PSU.esub. rewrite uv_esub, uv_eaddz, Ucap, Hsz.
    rewrite (Z.mod_small (cap + -1)) by lia. rewrite Z.mod_small by lia. lia.
  - cbn [kentry_ok]. fold (uv E (PSU.emul2 (EVar (g + 1)))). rewrite Ucap. split; [lia | exact Hc8].
Qed.

Lemma nul_facts_ok : forall E (M : mem) hd size' g BLk p cap (n : Z),
  bv_unsigned (ev E g) = p -> uv E (PSU.emul2 (EVar (g + 1))) = cap -> uv E size' = n -> 0 <= n < cap -> p + cap <= 2 ^ 64 ->
  (forall X, In X (PSU.blk_facts hd g BLk) -> kentry_ok RSEGS E M X) ->
  forall X, In X (PSU.nul_facts hd size' g BLk) -> kentry_ok RSEGS E M X.
Proof.
  intros E M hd size' g BLk p cap n Hp Hcap Hn Hlt Hb HB X HX. unfold PSU.nul_facts in HX. apply in_map_iff in HX as ([[b o] m] & <- & Hr).
  assert (HIn : In (KDisj (SA (EVar g) 0) (PSU.emul2 (EVar (g + 1))) (SA b o) m) (PSU.blk_facts hd g BLk)).
  { unfold PSU.blk_facts. apply in_or_app. right. apply in_map_iff. exists (b, o, m). split; [reflexivity | exact Hr]. }
  pose proof (HB _ HIn) as G. cbn [kentry_ok] in G |- *.
  assert (E1 : estart E (SA (EVar g) 0) = p) by (unfold estart; cbn [a_base a_off edenot]; rewrite Hp; lia).
  assert (E2 : elenZ E (PSU.emul2 (EVar (g + 1))) = cap) by exact Hcap.
  assert (E3 : estart E (SA (PSU.eadd size' (EVar g)) 0) = p + n).
  { unfold estart. cbn [a_base a_off]. fold (uv E (PSU.eadd size' (EVar g))). unfold PSU.eadd. rewrite uv_eadd, Hn. unfold uv. cbn [edenot]. rewrite Hp.
    pose proof (u64_range (ev E g)) as R. unfold two64 in R. rewrite Z.mod_small by lia. lia. }
  assert (E4 : elenZ E (ELit 1) = 1) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  rewrite E1, E2 in G. rewrite E3, E4. lia.
Qed.

Lemma uv_agree : forall b E E' e, env_agree b E E' -> APC.expr_vars_lt b e = true -> uv E' e = uv E e.
Proof. intros b E E' e Hag Hv. unfold uv. rewrite (SR.edenot_agree_AP b E E' e Hag Hv). reflexivity. Qed.
Lemma estart_agree : forall b E E' ob ok, env_agree b E E' -> APC.expr_vars_lt b ob = true -> estart E' (SA ob ok) = estart E (SA ob ok).
Proof. intros b E E' ob ok Hag Hv. unfold estart. cbn [a_base a_off]. fold (uv E' ob) (uv E ob). rewrite (uv_agree b E E' ob Hag Hv). reflexivity. Qed.
Lemma kn_vars_in : forall b cells X, APC.kn_vars_lt b cells = true -> In X cells -> APC.kentry_vars_lt b X = true.
Proof.
  intros b cells X. induction cells as [|Y r IH]; intros H HIn; [destruct HIn|]. cbn [APC.kn_vars_lt] in H. apply andb_prop in H as [H1 H2].
  destruct HIn as [<-|HIn]; [exact H1 | exact (IH H2 HIn)].
Qed.
Lemma cell_at_has : forall cells b k w v, CAX.cell_at cells b k w = Some v -> exists b' , In (KWord (SA b' k) w v) cells /\ b' = b.
Proof.
  intros cells b k w v H. unfold CAX.cell_at in H.
  destruct (find _ cells) as [X|] eqn:Hf; [|discriminate]. apply find_some in Hf as [HIn Hb].
  destruct X as [[b' k'] w' v'| | | | | | | | |]; try discriminate. injection H as <-.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Nat.eqb_eq in H3. subst.
  exists b'. split; [exact HIn | reflexivity].
Qed.

Lemma win_arith : forall q n wseg wlen, 0 <= q < 2 ^ 64 -> 0 <= n <= 16384 -> 4096 <= wseg -> 0 <= wlen -> wseg + wlen <= 2 ^ 47 ->
  0 <= (q - wseg) mod 2 ^ 64 <= 16384 -> 0 <= ((wseg + wlen) mod 2 ^ 64 - (q + n) mod 2 ^ 64) mod 2 ^ 64 <= 16384 ->
  wseg <= q /\ q - wseg <= 16384 /\ q + n <= wseg + wlen.
Proof.
  intros q n wseg wlen Hq Hn Hw Hl Hb F2 F3.
  assert (Hq1 : wseg <= q /\ q - wseg <= 16384).
  { destruct (Z_lt_dec (q - wseg) 0) as [N|N]; [rewrite (mod_neg_wrap (q - wseg)) in F2 by lia; lia|]. rewrite Z.mod_small in F2 by lia. lia. }
  split; [lia|]. split; [lia|].
  rewrite (Z.mod_small (wseg + wlen)) in F3 by lia. rewrite (Z.mod_small (q + n)) in F3 by lia.
  destruct (Z_lt_dec (wseg + wlen - (q + n)) 0) as [N|N]; [rewrite (mod_neg_wrap (wseg + wlen - (q + n))) in F3 by lia; lia | lia].
Qed.

Lemma LYI_ : forall L, PmLayout.pm0_layout L -> 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000.
Proof. intros L LAY. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). lia. Qed.
Lemma LYE_ : forall L, PmLayout.pm0_layout L -> hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Proof. intros L LAY. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY), (PmLayout.ly_errno L LAY). lia. Qed.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := LYI_ L LAY.
Let LYE := LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Lemma FLOOR : hl_sptop L - 2 ^ 23 + CH.hd_scr d <= sp0.
Proof. destruct STK as (_ & S2 & _). unfold hl_ceil in S2. lia. Qed.

Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Definition cap_of (i : nat) (E : env) : Z := snd (hd (0, 0) (CH2.den E (nth i BLS []))).

Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Variable oaddr : Z.
Hypothesis OADDR : estart E0 (SA OB OK) = oaddr.
Hypothesis OBJ : sp0 <= oaddr /\ oaddr + 24 <= hl_sptop L /\ oaddr mod 8 = 0 /\ forall a, oaddr <= a < oaddr + 24 -> exists w, In w W /\ L5.in_rng w a.

Variables KXf BXf : list (Z * Z) -> Z.
Definition tl_of (i : nat) (E : env) : list (Z * Z) := tl (CH2.den E (nth i BLS [])).
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (cap_of i E) (KXf (tl_of i E)) (BXf (tl_of i E)).

Definition STR_SCR : Z := 8496.
Definition pushb_chk (KMIN : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let nx := (CC.cp_nx cj - APC.NCS - 2)%nat in
  match split_lit (nth 10 regs (ELit 0)), BLi with
  | (ob, ok), (pe, ce) :: BLk =>
      match CAX.cell_at cells ob (ok + 8) 8 with
      | Some se =>
          if (expr_eqb ob OB && Z.eqb ok OK && Z.leb 12 KMIN && str_pat cells ob ok pe ce se (2 * KMIN) (2 ^ 26 - 2)
              && APC.fact_ok cells (KRange (nth 11 regs (ELit 0)) 0 255)
              && CH2.blocks_eqb BLj ((EVar nx, PSU.emul2 (EVar (nx + 1))) :: BLk) && CH2.blocks_vars_lt nx BLk
              && forallb (CH2.fresh_fact_ok d 0x10000 0xf8000 cells nx BLk nx (PSU.emul2 (EVar (nx + 1)))) (PSU.blk_facts d nx BLk))%bool
          then CH2.custom_chk NF d STR_SCR 2 BLk [(ob, ok, ELit 24)] (PSU.str_news d ob ok (APC.eaddz se 1) nx KMIN BLk) None c ps cj BLi
          else None
      | None => None
      end
  | _, _ => None
  end.

Hypothesis PUSHB : PMS.str_push_back_spec L HI.

Lemma den_cons : forall E pe ce BLk, CH2.den E ((pe, ce) :: BLk) = (uv E pe, uv E ce) :: CH2.den E BLk.
Proof. intros. reflexivity. Qed.

Lemma pushb_leaf_ok : forall KMIN i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_STR_PUSH_BACK) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj ->
  SR.ps_pc ps = PML.PC_STR_PUSH_BACK ->
  pushb_chk KMIN c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) LBk spc, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> XI i E M ->
     L5C.hpres L LBk spc STR_SCR [(oaddr, 24)] M' M2 -> incl LBrest LBk -> XI j E2 M2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros KMIN i c k ps j cj ci IL Hret Hcj Hpc Hchk XIBL fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold pushb_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (nth i BLS []) as [|[pe ce] BLk] eqn:HBLi; [discriminate|].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [se|] eqn:Hcell; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B7]. apply andb_prop in Hb as [Hb B6b]. apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4].
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3. subst ob ok.
  apply CH2.blocks_eqb_eq in B6.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              STR_SCR 2%nat BLk _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.

  assert (Ho : estart E' (SA OB OK) = oaddr) by (rewrite (estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct OBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  destruct (str_view E' M' cells OB OK pe ce se (2 * KMIN) (2 ^ 26 - 2) HK B4 ltac:(lia) ltac:(rewrite Ho; lia) ltac:(rewrite Ho; lia)) as (s & Hstr & Hlen & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite Ho in Hstr. set (p := uv E' pe) in *. set (cap := uv E' ce) in *. set (size := uv E' se) in *.

  unfold CH2.cur in HH. rewrite <- Hden, HBLi, den_cons in HH. fold p cap in HH. set (rest := CH2.den E' BLk ++ LBrest) in *.
  change ((p, cap) :: CH2.den E' BLk ++ LBrest) with ((p, cap) :: rest) in HH.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 oaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  pose proof (fact_ok' E' M' cells _ HK B5) as Hc255. cbn [kentry_ok] in Hc255. set (cv := bv_unsigned (edenot E' (nth 11 (CA.ps_reglist ps) (ELit 0)))) in *.
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 cv).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    unfold cv. symmetry. apply Z_to_bv_bv_unsigned. }

  set (kx := KXf (CH2.den E' BLk)). set (bx := BXf (CH2.den E' BLk)).
  assert (HBC : PPS.bufcred L cr cap kx bx).
  { apply CRED_EQ in HC. unfold cap_of, tl_of in HC. rewrite <- Hden, HBLi, den_cons in HC. exact HC. }
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & _ & Hcr0 & Hcr1).

  rewrite Hpc. rewrite LS.
  apply (PUSHB ((p, cap) :: rest) cr oaddr cap p cv (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) s fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact Hstr|]. split; [lia|]. split; [left; reflexivity|].
    split; [unfold PML.obj_on_stack; lia|]. split; [lia|].
    intros Hg. apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [Hgrown HWc] HRP HPRES Hbv2 HH2.
  assert (Hs1 : Z.of_nat (length (s ++ [cv])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; cbn [length]; lia).
  assert (EXP : exists p' cap', PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ [cv])) /\ LB' = (p', cap') :: rest /\ LBk = rest /\ 2 * KMIN <= cap' <= 2 ^ 27 /\ PPS.bufcred L cr' cap' kx bx).
  { assert (Hrm : lb_remove p ((p, cap) :: rest) = rest) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    destruct Hgrown as [(G1 & G2 & G3 & G4) | (p' & Hex)].
    - exists p, cap. rewrite G2, G3, G4, Hrm. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact HBC].
    - cbv zeta in Hex. destruct Hex as (G0 & G1 & G2 & G3 & G4 & G5). rewrite Hs1 in *.
      destruct (PPS.grow_cap_facts cap (size + 1) ltac:(lia) Hc8 ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4).
      exists p', (PML.grow_cap cap (size + 1)). rewrite G3, G5, Hrm, G4. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  destruct EXP as (p' & cap' & Hstr2 & -> & -> & Hcap' & HBC').
  destruct (CH2.first_block_facts L HI HIok p' cap' rest cr' M2 _ HH2) as (BR & BD & BA). pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.

  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] rest Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    unfold PSU.str_news in HX. apply in_app_or in HX as [HX|HX]; [|apply in_app_or in HX as [HX|HX]].
    + rewrite LS.
      assert (Hest : estart E2 (SA OB OK) = oaddr) by (rewrite (estart_agree NF E0 E2 OB OK HagE2 OB_frozen); exact OADDR).
      assert (Hsz : uv E2 (APC.eaddz se 1) = Z.of_nat (length (s ++ [cv]))).
      { destruct (cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        rewrite uv_eaddz, (uv_agree nx E' E2 se Hag2 Vse). fold size. rewrite Hs1. apply Z.mod_small. lia. }
      assert (Hpr' : 4096 <= p' <= 2 ^ 47) by (unfold hl_ceil in *; lia).
      exact (str_cells_ok E2 M2 OB OK (APC.eaddz se 1) nx KMIN oaddr cap' p' (s ++ [cv]) Hest ltac:(lia) ltac:(lia) G0 G1 Hsz (conj Hl2 (conj Hc8' Hlt2)) Hcap' Hpr' X HX).
    + rewrite forallb_forall in B7. specialize (B7 X HX).
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' X HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
    + rewrite LS.
      assert (Hsz : uv E2 (APC.eaddz se 1) = size + 1).
      { destruct (cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        rewrite uv_eaddz, (uv_agree nx E' E2 se Hag2 Vse). fold size. apply Z.mod_small. lia. }
      apply (nul_facts_ok E2 M2 d (APC.eaddz se 1) nx BLk p' cap' (size + 1) G0 Ucap Hsz ltac:(rewrite <- Hs1; lia) ltac:(unfold hl_ceil in *; lia)); [|exact HX].
      intros Y HY. rewrite forallb_forall in B7. specialize (B7 Y HY). rewrite <- LS.
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' Y HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
  -
    rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (Hcur : CH2.cur LBrest BLS j E2 = (p', cap') :: rest).
    { unfold CH2.cur. rewrite B6, den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. unfold rest. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    split; [|apply (XIBL E E' R' M M' E2 M2 rest (sp0 + CH2.ci_csp ci) HagE' Hag HLF HXI0); [subst Wc; exact HPRES | intros b0 Hb0; unfold rest; apply in_or_app; right; exact Hb0]].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 FLOOR STR_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 rest Wc cr' CF HPRES).
    + intros b Hb. unfold rest. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + rewrite Hcur. exact HH2.
    + rewrite Hnx. exact Hag2.
    + apply CRED_EQ. unfold cap_of, tl_of. rewrite B6, den_cons. cbn [hd snd tl]. rewrite Ucap. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). exact HBC'.
Qed.

Variables WSEG WLEN : expr.
Hypothesis WSEG_frozen : APC.expr_vars_lt NF WSEG = true.
Hypothesis WLEN_frozen : APC.expr_vars_lt NF WLEN = true.
Variables wseg wlen : Z.
Hypothesis WSEGV : uv E0 WSEG = wseg.
Hypothesis WLENV : uv E0 WLEN = wlen.
Hypothesis WCHUNK : exists ch, In (ch, 16384) LBrest /\ ch <= wseg /\ wseg + wlen <= ch + 16384.
Hypothesis APPENDOK : PMS.str_append_spec L HI.
Definition appendb_chk (KMIN : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let nx := (CC.cp_nx cj - APC.NCS - 2)%nat in
  let a1e := nth 11 regs (ELit 0) in let a2e := nth 12 regs (ELit 0) in
  match split_lit (nth 10 regs (ELit 0)), BLi with
  | (ob, ok), (pe, ce) :: BLk =>
      match CAX.cell_at cells ob (ok + 8) 8 with
      | Some se =>
          if (expr_eqb ob OB && Z.eqb ok OK && Z.leb 12 KMIN && str_pat cells ob ok pe ce se (2 * KMIN) (2 ^ 26 - 1)
              && has cells (KUnk (SA WSEG 0) WLEN) && prove cells (KRange (APC.esub a1e WSEG) 0 16384)
              && prove cells (KRange (APC.esub (APC.eadd WSEG WLEN) (APC.eadd a1e a2e)) 0 16384) && prove cells (KRange (APC.eadd se a2e) 0 (2 ^ 26 - 1)) && prove cells (KRange a2e 0 16384)
              && CH2.blocks_eqb BLj ((EVar nx, PSU.emul2 (EVar (nx + 1))) :: BLk) && CH2.blocks_vars_lt nx BLk
              && forallb (fun X => (CH2.fresh_fact_ok d 0x10000 0xf8000 cells nx BLk nx (PSU.emul2 (EVar (nx + 1))) X

                                    || APC.kentry_eqb X (KDisj (SA (EVar nx) 0) (PSU.emul2 (EVar (nx + 1))) (SA WSEG 0) WLEN))%bool) (PSU.blk_facts d nx BLk))%bool
          then CH2.custom_chk NF d STR_SCR 2 BLk [(ob, ok, ELit 24)] (PSU.str_news d ob ok (PSU.eadd se a2e) nx KMIN BLk) None c ps cj BLi
          else None
      | None => None
      end
  | _, _ => None
  end.

Lemma appendb_leaf_ok : forall KMIN i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_STR_APPEND) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj ->
  SR.ps_pc ps = PML.PC_STR_APPEND ->
  appendb_chk KMIN c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) LBk spc, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> XI i E M ->
     L5C.hpres L LBk spc STR_SCR [(oaddr, 24)] M' M2 -> incl LBrest LBk -> XI j E2 M2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros KMIN i c k ps j cj ci IL Hret Hcj Hpc Hchk XIBL fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold appendb_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (nth i BLS []) as [|[pe ce] BLk] eqn:HBLi; [discriminate|].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [se|] eqn:Hcell; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B7]. apply andb_prop in Hb as [Hb B6b]. apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb W5]. apply andb_prop in Hb as [Hb W4]. apply andb_prop in Hb as [Hb W3].
  apply andb_prop in Hb as [Hb W2]. apply andb_prop in Hb as [Hb W1]. apply andb_prop in Hb as [Hb B4].
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3. subst ob ok.
  apply CH2.blocks_eqb_eq in B6.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              STR_SCR 2%nat BLk _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  assert (Va2 : APC.expr_vars_lt nx (nth 12 (CA.ps_reglist ps) (ELit 0)) = true) by (rewrite <- Hnx, <- Hreq; apply CH.nth_vars_lt; exact V1).
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.

  assert (Ho : estart E' (SA OB OK) = oaddr) by (rewrite (estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct OBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  destruct (str_view E' M' cells OB OK pe ce se (2 * KMIN) (2 ^ 26 - 1) HK B4 ltac:(lia) ltac:(rewrite Ho; lia) ltac:(rewrite Ho; lia)) as (s & Hstr & Hlen & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite Ho in Hstr. set (p := uv E' pe) in *. set (cap := uv E' ce) in *. set (size := uv E' se) in *.

  unfold CH2.cur in HH. rewrite <- Hden, HBLi, den_cons in HH. fold p cap in HH. set (rest := CH2.den E' BLk ++ LBrest) in *.
  change ((p, cap) :: CH2.den E' BLk ++ LBrest) with ((p, cap) :: rest) in HH.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 oaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  set (a1e := nth 11 (CA.ps_reglist ps) (ELit 0)) in *. set (a2e := nth 12 (CA.ps_reglist ps) (ELit 0)) in *.
  set (q := uv E' a1e). set (n := uv E' a2e).
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 q).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    unfold q, uv. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Ga2 : getr R' 12%bv = Z_to_bv 64 n).
  { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite Hreq.
    unfold n, uv. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (uv_range E' a1e) as Rq. pose proof (uv_range E' a2e) as Rn. fold q in Rq. fold n in Rn.
  destruct WCHUNK as (ch & Hch & Hch1 & Hch2).
  assert (Uws : uv E' WSEG = wseg) by (rewrite (uv_agree NF E0 E' WSEG HagE' WSEG_frozen); exact WSEGV).
  assert (Uwl : uv E' WLEN = wlen) by (rewrite (uv_agree NF E0 E' WLEN HagE' WLEN_frozen); exact WLENV).
  pose proof (has_ok E' M' cells _ HK W1) as HWU.
  assert (Hdefw : L5.defined M' wseg wlen).
  { apply (CL5.kunk_elim RSEGS E' M' _ _ wseg wlen HWU); [unfold estart; cbn [a_base a_off]; fold (uv E' WSEG); lia | exact Uwl]. }
  pose proof (prove_ok E' M' cells _ HK W2) as F2. cbn [kentry_ok] in F2. fold (uv E' (APC.esub a1e WSEG)) in F2. rewrite uv_esub in F2. fold q in F2. rewrite Uws in F2.
  pose proof (prove_ok E' M' cells _ HK W3) as F3. cbn [kentry_ok] in F3. fold (uv E' (APC.esub (APC.eadd WSEG WLEN) (APC.eadd a1e a2e))) in F3.
  rewrite uv_esub, !uv_eadd in F3. fold q n in F3. rewrite Uws, Uwl in F3.
  pose proof (prove_ok E' M' cells _ HK W4) as F4. cbn [kentry_ok] in F4. fold (uv E' (APC.eadd se a2e)) in F4. rewrite uv_eadd in F4. fold n in F4.
  pose proof (prove_ok E' M' cells _ HK W5) as F5. cbn [kentry_ok] in F5. fold (uv E' a2e) in F5. fold n in F5.

  set (kx := KXf (CH2.den E' BLk)). set (bx := BXf (CH2.den E' BLk)).
  assert (HBC : PPS.bufcred L cr cap kx bx).
  { apply CRED_EQ in HC. unfold cap_of, tl_of in HC. rewrite <- Hden, HBLi, den_cons in HC. exact HC. }
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & _ & Hcr0 & Hcr1).

  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _ & _).
  assert (Hchin : In (ch, 16384) ((p, cap) :: rest)) by (right; unfold rest; apply in_or_app; right; exact Hch).
  destruct (Hwf _ Hchin) as ((C0 & C1 & C2 & C3 & C4) & _ & _). cbn [fst snd] in C0, C1, C2, C3, C4.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO0.
  assert (Hwl0 : 0 <= wlen) by (rewrite <- Uwl; apply uv_range).
  assert (Hwr : 4096 <= wseg /\ wseg + wlen <= 2 ^ 47) by (clear - C0 C4 Hch1 Hch2 S3 S4 S5 S2 SCR_pos; unfold hl_ceil in *; lia).
  destruct (win_arith q n wseg wlen Rq ltac:(clear - F5 Rn; lia) (proj1 Hwr) Hwl0 (proj2 Hwr) F2 F3) as (Hq1a & Hq1b & Hq2).
  assert (Hsn : size + n <= 2 ^ 26 - 1) by (clear - F4 F5 Hsm Rn Hlen; rewrite Z.mod_small in F4 by lia; lia).
  clear F2 F3 F4 HWU C1.
  destruct (bytes_of_defined M' (Z.to_nat n) q ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold hl_ceil in *; lia)) as (src & Hlsrc & Hbsrc).
  { intros i0 Hi0. rewrite Z2Nat.id in Hi0 by lia. replace (q + i0) with (wseg + (q - wseg + i0)) by lia. apply Hdefw. lia. }
  assert (Hnsrc : Z.of_nat (length src) = n) by (rewrite Hlsrc; apply Z2Nat.id; lia).

  rewrite Hpc. rewrite LS.
  apply (APPENDOK ((p, cap) :: rest) cr oaddr cap p q (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) s src fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [rewrite Hnsrc; exact Ga2|]. split; [exact Hstr|]. split; [lia|]. split; [left; reflexivity|].
    split; [unfold PML.obj_on_stack; lia|]. split; [exact Hbsrc|].
    split; [intros i0 Hi0; rewrite Hnsrc in Hi0; replace (q + i0) with (wseg + (q - wseg + i0)) by lia; apply Hdefw; lia|].
    split; [destruct src as [|c0 src']; [left; reflexivity | right; exists (ch, 16384); split; [exact Hchin|]; cbn [fst snd]; split; [|rewrite Hnsrc; lia]]|].
    { intros Heq. cbn [fst] in Heq. subst ch. apply (CH2.nodup_app_disj [p] (map fst rest) p Hnd); [left; reflexivity|].
      change p with (fst (p, 16384)). apply in_map. unfold rest. apply in_or_app. right. exact Hch. }
    split; [rewrite Hnsrc; lia|].
    intros Hg. apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [Hgrown HWc] HRP HPRES Hbv2 HH2.
  assert (Hs1 : Z.of_nat (length (s ++ src)) = size + n) by (rewrite length_app, Nat2Z.inj_add; lia).
  assert (EXP : exists p' cap', PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ src)) /\ LB' = (p', cap') :: rest /\ LBk = rest /\ 2 * KMIN <= cap' <= 2 ^ 27 /\ PPS.bufcred L cr' cap' kx bx).
  { assert (Hrm : lb_remove p ((p, cap) :: rest) = rest) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    destruct Hgrown as [(G1 & G2 & G3 & G4) | (p' & Hex)].
    - exists p, cap. rewrite G2, G3, G4, Hrm. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact HBC].
    - cbv zeta in Hex. destruct Hex as (G0 & G1 & G2 & G3 & G4 & G5). rewrite Hs1 in *.
      destruct (PPS.grow_cap_facts cap (size + n) ltac:(lia) Hc8 ltac:(lia) ltac:(lia)) as (F1' & F2' & F3' & F4').
      exists p', (PML.grow_cap cap (size + n)). rewrite G3, G5, Hrm, G4. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  destruct EXP as (p' & cap' & Hstr2 & -> & -> & Hcap' & HBC').
  destruct (CH2.first_block_facts L HI HIok p' cap' rest cr' M2 _ HH2) as (BR & BD & BA). pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.

  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] rest Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (BF : forall Y, In Y (PSU.blk_facts d nx BLk) -> kentry_ok (hl_segs L) E2 M2 Y).
    { intros Y HY. rewrite forallb_forall in B7. specialize (B7 Y HY). apply orb_prop in B7 as [B7|B7].
      - exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
                 E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' Y HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
      - apply APS.kentry_eqb_eq in B7. subst Y. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite G0.
        fold (uv E2 (PSU.emul2 (EVar (nx + 1)))) (uv E2 WSEG) (uv E2 WLEN). rewrite Ucap, (uv_agree NF E0 E2 WSEG HagE2 WSEG_frozen), (uv_agree NF E0 E2 WLEN HagE2 WLEN_frozen), WSEGV, WLENV.
        assert (Hin : In (ch, 16384) rest) by (unfold rest; apply in_or_app; right; exact Hch).
        pose proof (L5C.blocks_apart_in p' cap' rest ch 16384 BA Hin) as AP. lia. }
    unfold PSU.str_news in HX. apply in_app_or in HX as [HX|HX]; [|apply in_app_or in HX as [HX|HX]].
    + rewrite LS.
      assert (Hest : estart E2 (SA OB OK) = oaddr) by (rewrite (estart_agree NF E0 E2 OB OK HagE2 OB_frozen); exact OADDR).
      assert (Hsz : uv E2 (PSU.eadd se a2e) = Z.of_nat (length (s ++ src))).
      { destruct (cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        unfold PSU.eadd. rewrite uv_eadd, (uv_agree nx E' E2 se Hag2 Vse), (uv_agree nx E' E2 a2e Hag2 Va2). fold size n. rewrite Hs1. apply Z.mod_small. lia. }
      assert (Hpr' : 4096 <= p' <= 2 ^ 47) by (unfold hl_ceil in *; lia).
      exact (str_cells_ok E2 M2 OB OK (PSU.eadd se a2e) nx KMIN oaddr cap' p' (s ++ src) Hest ltac:(lia) ltac:(lia) G0 G1 Hsz (conj Hl2 (conj Hc8' Hlt2)) Hcap' Hpr' X HX).
    + exact (BF X HX).
    + rewrite LS.
      assert (Hsz : uv E2 (PSU.eadd se a2e) = size + n).
      { destruct (cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        unfold PSU.eadd. rewrite uv_eadd, (uv_agree nx E' E2 se Hag2 Vse), (uv_agree nx E' E2 a2e Hag2 Va2). fold size n. apply Z.mod_small. lia. }
      apply (nul_facts_ok E2 M2 d (PSU.eadd se a2e) nx BLk p' cap' (size + n) G0 Ucap Hsz ltac:(rewrite <- Hs1; lia) ltac:(unfold hl_ceil in *; lia)); [|exact HX].
      intros Y HY. rewrite <- LS. exact (BF Y HY).
  -
    rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (Hcur : CH2.cur LBrest BLS j E2 = (p', cap') :: rest).
    { unfold CH2.cur. rewrite B6, den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. unfold rest. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    split; [|apply (XIBL E E' R' M M' E2 M2 rest (sp0 + CH2.ci_csp ci) HagE' Hag HLF HXI0); [subst Wc; exact HPRES | intros b0 Hb0; unfold rest; apply in_or_app; right; exact Hb0]].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 FLOOR STR_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 rest Wc cr' CF HPRES).
    + intros b Hb. unfold rest. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + rewrite Hcur. exact HH2.
    + rewrite Hnx. exact Hag2.
    + apply CRED_EQ. unfold cap_of, tl_of. rewrite B6, den_cons. cbn [hd snd tl]. rewrite Ucap. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). exact HBC'.
Qed.

Variable SCRC : Z.
Hypothesis SCRC_ge : CH.hd_scr d <= SCRC.
Hypothesis STKC : hl_ceil L + SCRC <= sp0.
Hypothesis DEFC : L5.defined M0 (sp0 - SCRC) SCRC.
Variable R0 : bvmap 5 word.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Variable ra0 : Z.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.
Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.

Definition exit_base_chk (retpc : Z) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) retpc && CL.ps_keeps ps CL5.CSAVED && Nat.leb NF (CC.cp_nx c))%bool.

Lemma exit_ret : forall retpc i c k ps pc, CL.is_ret_at RSEGS retpc -> is_leaf i c k ps (CC.TOther pc) -> exit_base_chk retpc c ps = true ->
  forall (fx' : FPState) E R M model E' R' M',
    CC.At (hl_segs L) c E R M -> HAMB i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
    (regs_preserved R0 R' -> L5C.hpres L LBrest sp0 SCRC W M0 M' -> HAMB i E M' model -> env_agree NF E0 E' ->
       srealizes RSEGS SCFG (@PML.cfg fx' R' ra0 M' model) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom (hl_segs L))) model) K.
Proof.
  clear OBJ OADDR OB_frozen CRED_EQ PUSHB WSEG_frozen WLEN_frozen WSEGV WLENV WCHUNK APPENDOK.
  intros retpc i c k ps pc Hret IL Hchk fx' E R M model E' R' M' HAt HA Hag HLF Hcont.
  unfold exit_base_chk in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [C1 C2]. apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  pose proof (CH2.leaf_amb3 L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 W_ok WRS_ok CPS TAGS HEAPCHK i c k ps pc IL
                E E' R R' M M' model HAt HA Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & _ & Hfr1 & Hdf1).
  assert (HagE' : env_agree NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact C3]]).
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R0 x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat) by (unfold CL5.CSAVED in Hx; cbn [In] in Hx; intuition lia).
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' M M' CL5.CSAVED NF x HLF C2 HagE' Hx Hx32). exact (EV0 x). }
  assert (HRP : regs_preserved R0 R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0).
  pose proof (CH2.amb_hpres L HI LYI LYE NF E0 M0 model0 LBrest sp0 d W BLS Cred STK NF32 i E M' model HA' DEF0) as HP0.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof LYI as [LI1 LI2]. pose proof LYE as [LE1 LE2].
  assert (HP : L5C.hpres L LBrest sp0 SCRC W M0 M').
  { apply L5C.hpres_intro.
    - intros a (K1 & K2 & K3 & K4). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP0). split; [exact K1|]. split; [|split; assumption].
      destruct K2 as [B|[[C1' C2']|C]]; [left; exact B | right; left; split; [exact C1' | lia] | right; right; exact C].
    - intros j Hj. apply (Hdf1 (sp0 - SCRC + j)); [lia | | apply DEFC; lia].
      split; [right; left; split; lia | unfold in_errno; lia].
    - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP0 Ha); [|exact HE | exact Hd].
      destruct HC as [B|[[C1' C2']|C]]; [left; exact B | right; left; split; [exact C1' | lia] | right; right; exact C]. }
  rewrite C1, LS. eapply CL.ret_cps; [exact Hret | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct RA0ok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  rewrite Hra'. exact (Hcont HRP HP HA' HagE').
Qed.
End Inst.
End PB.
