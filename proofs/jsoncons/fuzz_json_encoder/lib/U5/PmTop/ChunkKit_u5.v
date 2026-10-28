(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 ReadKit_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CK.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition spok (sp0 : Z) : Prop := 2 ^ 40 <= sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint rfacts (E : env) (l : list kentry) : Prop :=
  match l with
  | [] => True
  | KRange e lo hi :: r => (lo <= bv_unsigned (edenot E e) <= hi) /\ rfacts E r
  | _ :: r => rfacts E r
  end.
Lemma rfacts_sound : forall E (M : mem) l, (forall K, In K l -> kentry_ok RSEGS E M K) -> rfacts E l.
Proof.
  intros E M l. induction l as [|K r IH]; intros H; [exact I|].
  assert (Hr : rfacts E r) by (apply IH; intros K' HK'; apply H; right; exact HK').
  destruct K; cbn [rfacts]; try exact Hr. split; [|exact Hr]. exact (H _ (or_introl eq_refl)).
Qed.
(* [comment removed for export] *)
Definition is_path_fact (K : kentry) : bool := match K with KRange (EVar _) _ _ => false | KRange _ _ _ => true | _ => false end.
Lemma leaf_rfacts : forall c ps E' R' M M', CC.leaf_facts RSEGS c ps E' R' M M' -> rfacts E' (List.filter is_path_fact (SR.ps_cells ps)).
Proof.
  intros c ps E' R' M M' HLF. apply (rfacts_sound E' M'). intros K HK. apply filter_In in HK as [HK _]. exact (CC.lf_cells _ _ _ _ _ _ _ HLF K HK).
Qed.
(* [comment removed for export] *)
Lemma lf_cell : forall c ps E' R' M M' K, CC.leaf_facts RSEGS c ps E' R' M M' -> existsb (APC.kentry_eqb K) (SR.ps_cells ps) = true -> kentry_ok RSEGS E' M' K.
Proof.
  intros c ps E' R' M M' K HLF H. apply existsb_exists in H as (K' & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K'. exact (CC.lf_cells _ _ _ _ _ _ _ HLF K Hin).
Qed.
(* [comment removed for export] *)
Definition is_range (K : kentry) : bool := match K with KRange _ _ _ => true | _ => false end.
Lemma leaf_ranges : forall c ps E' R' M M', CC.leaf_facts RSEGS c ps E' R' M M' -> rfacts E' (List.filter is_range (SR.ps_cells ps)).
Proof.
  intros c ps E' R' M M' HLF. apply (rfacts_sound E' M'). intros K HK. apply filter_In in HK as [HK _]. exact (CC.lf_cells _ _ _ _ _ _ _ HLF K HK).
Qed.
(* [comment removed for export] *)
Lemma u_lin_mod : forall E e, exists q, bv_unsigned (edenot E e) = lden E (lin_of e) + q * 2 ^ 64.
Proof.
  intros E e. destruct (lin_of_sound E e) as [q Hq]. unfold uE in Hq. exists (- q). change (2 ^ 64) with two64 in *. unfold two64 in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hvB (sp0 : Z) (R : bvmap 5 word) (gl : list Z) (bl : nat -> list byte) : env := Env (TK.hvV sp0 R (RK.ghl gl)) bl.
Lemma hvB_sp : forall sp0 R gl bl, 0 <= sp0 < 2 ^ 64 -> bv_unsigned (ev (hvB sp0 R gl bl) 2) = sp0.
Proof. intros. cbn. apply u64_of_Z. assumption. Qed.
Lemma hvB_reg : forall sp0 R gl bl (r : reg), ev (hvB sp0 R gl bl) (32 + ridx r) = getr R r.
Proof. intros. exact (TK.hvE_reg sp0 R (RK.ghl gl) r). Qed.
Lemma hvB_reg_u : forall sp0 R gl bl (r : reg) z, getr R r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ev (hvB sp0 R gl bl) (32 + ridx r)) = z.
Proof. intros sp0 R gl bl r z H Hz. rewrite hvB_reg, H. apply u64_of_Z. exact Hz. Qed.
Lemma hvB_gh_u : forall sp0 R gl bl k z, nth_error gl k = Some z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ev (hvB sp0 R gl bl) (64 + k)) = z.
Proof. intros sp0 R gl bl k z H Hz. exact (RK.ghl_u sp0 R gl k z H Hz). Qed.
Lemma hvB_gh_w : forall sp0 R gl bl k z, nth_error gl k = Some z -> ev (hvB sp0 R gl bl) (64 + k) = Z_to_bv 64 z.
Proof. intros sp0 R gl bl k z H. change (ev (TK.hvE sp0 R (RK.ghl gl)) (64 + k) = Z_to_bv 64 z). rewrite TK.hvE_ghost. unfold RK.ghl. rewrite (nth_error_nth _ _ _ H). reflexivity. Qed.
Lemma regs_ok_hvB : forall sr off pins sp0 R gl bl,
  RK.hv_shape sr off pins = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  regs_ok (hvB sp0 R gl bl) sr R.
Proof.
  intros sr off pins sp0 R gl bl Hsh Hsp Hspo H2 Hpins. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold RK.hv_shape in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold RK.hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
  - apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
    destruct (Z.eqb_spec off 0) as [->|Hne].
    + cbn [edenot ev hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
    + cbn [edenot ev hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
  - destruct (find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
      rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
    + cbn [edenot]. symmetry. apply hvB_reg.
Qed.
Lemma keeps_hvB_sound : forall c ps sp0 R gl bl E' R' M M' qs (r : reg),
  CC.leaf_facts RSEGS c ps E' R' M M' -> TK.keeps_hv ps qs = true -> env_agree 64 (hvB sp0 R gl bl) E' -> In (ridx r) qs -> getr R' r = getr R r.
Proof.
  intros c ps sp0 R gl bl E' R' M M' qs r HLF H Hag Hin. unfold TK.keeps_hv in H. rewrite forallb_forall in H.
  rewrite <- (ridx_roundtrip r) at 1. rewrite (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF (H _ Hin)). cbn [edenot].
  rewrite <- (proj1 Hag) by (pose proof (ridx_range r); lia). apply hvB_reg.
Qed.
(* [comment removed for export] *)
Lemma bytes_of_defined : forall (M : mem) (n : nat) p, 0 <= p -> p + Z.of_nat n <= 2 ^ 63 -> L5.defined M p (Z.of_nat n) ->
  exists bs : list Z, length bs = n /\ L5.bytes_at RSEGS M p bs.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hn D.
  - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hb).
    { intros i Hi. replace (p + 1 + i) with (p + (1 + i)) by lia. apply D. lia. }
    pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:EM; [|contradiction].
    exists (bv_unsigned b :: bs). split; [cbn; lia|]. intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. rewrite EM. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hb. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wbytes_samem : forall (M : mem) dst (bs : list byte), 0 <= dst < 2 ^ 64 -> dst + Z.of_nat (length bs) <= 2 ^ 64 ->
  TK.samem (fun a => ~ (dst <= a < dst + Z.of_nat (length bs))) M (wbytes M (Z_to_bv 64 dst) bs).
Proof.
  intros M dst bs Hd Hn a Ha Hout. apply wbytes_out; rewrite ?u64_of_Z by lia; lia.
Qed.
Lemma wbytes_grows : forall (M : mem) (dst : word) (bs : list byte), mem_grows M (wbytes M dst bs).
Proof. intros M dst bs. apply StoreOk.wbytes_grows. Qed.
(* [comment removed for export] *)
Lemma rdn_of_defined : forall (M : mem) (n : nat) a, 0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> L5.defined M a (Z.of_nat n) ->
  exists bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros M n a Ha Hn D. apply rdn_defined; [rewrite u64_of_Z by lia; lia|].
  intros j Hj. rewrite u64_of_Z by lia. unfold rd1. specialize (D (Z.of_nat j) ltac:(lia)). destruct (M (Z_to_bv 64 (a + Z.of_nat j))); [discriminate | contradiction].
Qed.
(* [comment removed for export] *)
Lemma rdn_of_bytes_at : forall (M : mem) (s : list Z) a, 0 <= a < 2 ^ 64 -> a + Z.of_nat (length s) <= 2 ^ 64 -> L5.bytes_at RSEGS M a s ->
  exists bs, rdn RSEGS M (Z_to_bv 64 a) (length s) = Some bs /\ length bs = length s.
Proof.
  intros M s a Ha Hn B. apply rdn_defined; [rewrite u64_of_Z by lia; lia|].
  intros j Hj. rewrite u64_of_Z by lia. specialize (B j Hj). unfold L5.u8_at in B. cbn [rdn] in B. unfold rd1.
  destruct (match M (Z_to_bv 64 (a + Z.of_nat j)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat j)) end); [discriminate | discriminate B].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bytes_sub : forall (M : mem) (s : list Z) D a (k : nat), 0 <= D -> D <= a -> a + Z.of_nat k <= D + Z.of_nat (length s) -> D + Z.of_nat (length s) <= 2 ^ 63 ->
  L5.bytes_at RSEGS M D s -> exists bs, rdn RSEGS M (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  intros M s D a k HD Ha Hk Hn B. apply rdn_defined; [rewrite u64_of_Z by lia; lia|].
  intros j Hj. rewrite u64_of_Z by lia. specialize (B (Z.to_nat (a - D + Z.of_nat j)) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  replace (D + (a - D + Z.of_nat j)) with (a + Z.of_nat j) in B by lia. unfold L5.u8_at in B. cbn [rdn] in B. unfold rd1.
  destruct (match M (Z_to_bv 64 (a + Z.of_nat j)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat j)) end); [discriminate | discriminate B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma samem_frame_but : forall (K : Z -> Prop) (F : list L5.range) (M M' : mem), TK.samem K M M' -> (forall a, L5.outside F a -> K a) -> L5.frame_but F M M'.
Proof.
  intros K F M M' AG H x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (bv_unsigned_in_range _ x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply AG; [exact Hr | apply H; exact Hx].
Qed.
Lemma samem_weaken2 : forall (K1 K2 K : Z -> Prop) (M M' M'' : mem), TK.samem K1 M M' -> TK.samem K2 M' M'' -> (forall a, K a -> K1 a /\ K2 a) -> TK.samem K M M''.
Proof. intros K1 K2 K M M' M'' A1 A2 H a Ha Hk. destruct (H a Hk) as [H1 H2]. rewrite (A2 a Ha H2). exact (A1 a Ha H1). Qed.
Definition CSR : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.       (* [comment removed for export] *)
Lemma rp_of_keeps : forall R R' : bvmap 5 word, getr R' 2%bv = getr R 2%bv -> TK.keepsR CSR R R' -> regs_preserved R R'.
Proof.
  intros R R' H2 HK q Hq. unfold callee_saved_idx in Hq. cbn [In] in Hq.
  destruct Hq as [Hq|Hq].
  - assert (q = 2%bv) as -> by (apply bv_eq; rewrite <- Hq; reflexivity). exact H2.
  - apply HK. unfold ridx, CSR. repeat (destruct Hq as [Hq|Hq]; [rewrite <- Hq; cbn; tauto|]). destruct Hq.
Qed.
Lemma keepsR_sub : forall qs qs' R R', TK.keepsR qs R R' -> (forall q, In q qs' -> In q qs) -> TK.keepsR qs' R R'.
Proof. intros qs qs' R R' H Hs r Hr. apply H. apply Hs. exact Hr. Qed.
Lemma keepsR_kept : forall qs (R R' : bvmap 5 word), APSX.kept_ok R R' -> forallb (fun q => (negb (Nat.eqb q 0) && negb (existsb (Nat.eqb q) APC.caller_saved))%bool) qs = true -> TK.keepsR qs R R'.
Proof.
  intros qs R R' HK Hqs r Hr. rewrite forallb_forall in Hqs. specialize (Hqs _ Hr). apply andb_prop in Hqs as [Q0 Q1].
  apply HK.
  - intros X. subst r. cbn in Q0. discriminate Q0.
  - intros Hin. apply negb_true_iff in Q1. assert (T : existsb (Nat.eqb (ridx r)) APC.caller_saved = true) by (apply existsb_exists; exists (ridx r); split; [exact Hin | apply Nat.eqb_refl]).
    rewrite T in Q1. discriminate Q1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma al16 : forall sp k, sp mod 16 = 0 -> k mod 16 = 0 -> (sp - k) mod 16 = 0.
Proof. intros sp k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; apply Z.mod_divide; try lia; assumption. Qed.
Lemma sub_stk : forall sptop (M M' : mem) sp scr spc scr', L5C.stk sptop M sp scr -> mem_grows M M' -> spc mod 16 = 0 -> sp - scr <= spc - scr' -> spc <= sp -> 0 <= scr' ->
  L5C.stk sptop M' spc scr'.
Proof.
  intros sptop M M' sp scr spc scr' (S1 & S2 & S3 & S4 & S5) MG Hal H1 H2 H3. split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [exact S4|].
  apply (L5.defined_grows _ _ _ _ MG). eapply L5.defined_sub; [exact S5 | lia | lia].
Qed.
Lemma mk_entry : forall L R (M : mem) spc rc scr, getr R 1%bv = Z_to_bv 64 rc -> L5.ra_ok rc -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  L5C.stk (hl_sptop L) M spc scr -> PML.entry L R M spc rc scr.
Proof. intros L R M spc rc scr H1 Hra H2 H4 Hs. split; [exact H1|]. split; [exact Hra|]. split; [exact H2|]. split; [exact H4 | exact Hs]. Qed.
Lemma statics_cov_lo : forall K : Z -> Prop, (forall a, 0x10000 <= a < 0xfe000 -> K a) -> TK2.statics_cov K.
Proof.
  intros K H. split; [|split].
  - intros a (iv & Hiv & Hr). apply H. unfold PML.ll_foot_xsrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn in Hr; lia|]). destruct Hiv.
  - intros a Ha. apply H. unfold PML.IMG_RO_HI in Ha. lia.
  - intros a Ha. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma writable_static : forall (M : mem) A (N : nat), StreamSim.wseg_ok RSEGS (Z_to_bv 64 A) N = true -> 0 <= A < 2 ^ 64 -> A + Z.of_nat N <= 2 ^ 64 -> L5.writable RSEGS M A (Z.of_nat N).
Proof.
  intros M A N H HA HN d k Hd Hk. destruct k as [|k]; [reflexivity|].
  apply (store_ok_sub RSEGS M (Z_to_bv 64 A) (Z_to_bv 64 (A + d)) N (S k)); [rewrite u64_of_Z by lia; lia | apply store_ok_wseg; exact H | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia].
Qed.
Lemma kwr_of_writable : forall E (M : mem) a n A N, estart E a = A -> elenZ E n = N -> 0 <= A < 2 ^ 64 -> A + N <= 2 ^ 64 -> L5.writable RSEGS M A N -> kentry_ok RSEGS E M (KWr a n).
Proof.
  intros E M a n A N Ha Hn H0 H1 Hw. cbn [kentry_ok]. rewrite Ha, Hn.
  split; [unfold flat; rewrite Ha; pose proof (u64_range (edenot E n)) as Hr; unfold elenZ in Hn; rewrite Hn in Hr; lia|]. intros d m Hd Hm. apply Hw; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hpres_of_samem : forall (L : heap_layout) (LBk : list (Z * Z)) sp scr (W : list L5.range) (K : Z -> Prop) (M M' : mem),
  TK.samem K M M' -> mem_grows M M' -> L5C.stk (hl_sptop L) M sp scr -> hl_img_hi L = 0xfe000 -> TK2.blocks_ok L LBk ->
  (forall a, L5.outside W a -> ~ (sp - scr <= a < sp) -> K a) -> L5C.hpres L LBk sp scr W M M'.
Proof.
  intros L LBk sp scr W K M M' AG MG (S1 & S2 & S3 & S4 & S5) IHI BOK HK. unfold hl_ceil in *. apply L5C.hpres_intro.
  - intros a (Ha & HC & _ & HO). apply AG; [exact Ha|]. apply HK; [exact HO|].
    destruct HC as [(b & Hb & Hr)|[X|X]]; [| lia | rewrite IHI in X; lia].
    destruct (BOK b Hb) as (_ & _ & _ & _ & B5). unfold hl_ceil in B5. lia.
  - exact (L5.defined_grows _ _ _ _ MG S5).
  - intros a _ _ _ Hd. apply MG. exact Hd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ret.
Context {SCFG_P : ScfgP}.
Lemma ret_leaf : forall (fx : FPState) R pc M model K rav,
  CL.is_ret_at RSEGS pc -> m_halted model = None -> m_vm_lazy model = [] -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav ->
  srealizes RSEGS SCFG (@PML.cfg fx R rav M model) K -> srealizes RSEGS SCFG (@PML.cfg fx R pc M model) K.
Proof.
  intros fx R pc M model K rav Hret Hh Hl H1 [Hr1 Hr2] HK. unfold PML.cfg. apply (CL.ret_cps RSEGS fx R _ M model K Hret Hh Hl).
  - rewrite H1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hr2.
  - rewrite H1. exact HK.
Qed.
End Ret.
End CK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ck_in := vm_compute; repeat first [left; reflexivity | right].
(* [comment removed for export] *)
Ltac ck_open FPM cp plans off gl bl pn sp0 R M fx model K Hh Hl Hfp H2 Hpins :=
  let E := fresh "E" in set (E := CK.hvB sp0 R gl bl);
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply CK.hvB_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (CK.regs_ok_hvB _ off pn); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins] | | ].
Ltac ck_no_pins := let q := fresh in let z := fresh in intros q z [].
(* [comment removed for export] *)
Ltac ck_pins := let q := fresh in let z := fresh in let X := fresh in intros q z X; cbn [In] in X;
  repeat (destruct X as [X|X]; [injection X as <- <-; assumption|]); destruct X.
(* [comment removed for export] *)
Ltac ck_reg E r Hr := let U := fresh "Ur" in
  lazymatch type of Hr with getr _ _ = Z_to_bv 64 ?z =>
    let v := eval vm_compute in (32 + ridx (r : reg))%nat in
    assert (U : bv_unsigned (ev E v) = z) by (change v with (32 + ridx (r : reg))%nat; subst E; apply (CK.hvB_reg_u _ _ _ _ r z Hr); lia) end.
Ltac ck_gh E k z := let U := fresh "Ug" in
  let v := eval vm_compute in (64 + k)%nat in
  assert (U : bv_unsigned (ev E v) = z) by (change v with (64 + k)%nat; subst E; eapply CK.hvB_gh_u; [reflexivity | lia]).
(* [comment removed for export] *)
Ltac ck_leaf Hag E' :=
  assert (Hag64 : env_agree 64 _ E') by (eapply CC.env_agree_le; [exact Hag | vm_compute; lia]);
  repeat match goal with U : bv_unsigned (ev ?E ?v) = ?z |- _ =>
           lazymatch E with E' => fail | _ => let U' := fresh "V" in assert (U' : bv_unsigned (ev E' v) = z) by (rewrite <- (proj1 Hag v) by (vm_compute; lia); exact U); clear U end end.
Ltac ck_leaf_k k Hnth := destruct k as [|k]; [injection Hnth as <- | ].
Ltac ck_leaf_end k Hnth := destruct k; discriminate Hnth.
(* [comment removed for export] *)
Ltac ck_paths HLF PF := pose proof (CK.leaf_rfacts _ _ _ _ _ _ HLF) as PF; vm_compute List.filter in PF; cbn [CK.rfacts] in PF.
Ltac ck_ranges HLF PF := pose proof (CK.leaf_ranges _ _ _ _ _ _ HLF) as PF; vm_compute List.filter in PF; cbn [CK.rfacts] in PF.
(* [comment removed for export] *)
Ltac ck_rlin H :=
  lazymatch type of H with _ <= bv_unsigned (edenot ?E ?e) <= _ =>
    let q := fresh "q" in let Hq := fresh "Hq" in let Hu := fresh "Hu" in
    destruct (CK.u_lin_mod E e) as [q Hq]; pose proof (u64_range (edenot E e)) as Hu; unfold two64 in Hu; rewrite Hq in H, Hu; clear Hq;
    unfold lden in H, Hu;
    repeat (match type of H with context [lin_of ?e'] => let l := fresh "l" in set (l := lin_of e') in H, Hu; vm_compute in l; subst l end);
    cbn [fst snd tden] in H, Hu; unfold uE in H, Hu; cbn [edenot] in H, Hu;
    repeat match goal with U : bv_unsigned (ev _ _) = _ |- _ => rewrite U in H, Hu end end.
(* [comment removed for export] *)
Ltac ck_probes HLF PF := pose proof (RK.leaf_probes _ _ _ _ _ _ HLF) as PF; vm_compute RK.probes in PF; cbn [RK.pfacts edenot] in PF.
Ltac ck_w2z H := repeat match type of H with context [ev ?E ?v] => match goal with U : bv_unsigned (ev E v) = ?z |- _ => rewrite (RK.w_of_u _ _ U) in H end end.
(* [comment removed for export] *)
Ltac ck_keeps HLF Hag64 qs := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; exact (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ qs r HLF eq_refl Hag64 Hr).
Ltac ck_keep HLF Hag64 x r :=            (* [comment removed for export] *)
  tk_reg HLF x; let v := eval vm_compute in (32 + ridx (r : reg))%nat in (rewrite <- (proj1 Hag64 v) by lia); exact (CK.hvB_reg _ _ _ _ r).
(* [comment removed for export] *)
Ltac ck_cell64 HLF b off v := eapply (CL5.kword64_elim CK.RSEGS); [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA b off) 8 v) HLF); vm_compute; reflexivity | ev_start | ].
Ltac ck_cell32 HLF b off v := eapply TK.kword32_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA b off) 4 v) HLF); vm_compute; reflexivity | ev_start | ].
Ltac ck_cell8 HLF b off v := eapply RK.kword8_elim; [apply (CK.lf_cell _ _ _ _ _ _ (KWord (SA b off) 1 v) HLF); vm_compute; reflexivity | ev_start | ].
Ltac ck_atom := cbn [edenot]; assumption.        (* [comment removed for export] *)
Ltac ck_vlin := apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?u64_of_Z by lia; lia | lia].
Ltac ck_vgh Hag64 v := cbn [edenot]; rewrite <- (proj1 Hag64 v) by lia.
(* [comment removed for export] *)
Ltac ck_saved HLF Hag64 off v r := ck_cell64 HLF (EVar 2) off (EVar v); ck_vgh Hag64 v; first [reflexivity | f_equal; exact (CK.hvB_reg _ _ _ _ r)].
(* [comment removed for export] *)
Ltac ck_kw64 A0 z0 H := eapply CL5.kword64_intro with (A := A0) (z := z0); [ev_start | lia | lia | first [reflexivity | cbn [edenot]; apply RK.w_of_u; rw_atoms; reflexivity | apply TK.edenot_lin; [lin_eval; rw_atoms; rewrite ?u64_of_Z by lia; lia | lia]] | exact H].
Ltac ck_kw32 A0 z0 H := eapply RK.kword32_intro with (A := A0) (z := z0); [ev_start | lia | lia | first [reflexivity | cbn [edenot]; apply RK.w_of_u; rw_atoms; reflexivity] | exact H].
Ltac ck_kw8 A0 z0 H := eapply TK.kword8_intro with (A := A0) (z := z0); [ev_start | lia | lia | first [reflexivity | cbn [edenot]; apply RK.w_of_u; rw_atoms; reflexivity] | lia | exact H].
(* [comment removed for export] *)
Ltac ck_frame HLF := apply (TK.frame_samem _ _ _ _ _ _ _ HLF); let a := fresh "a" in let Ha := fresh "Ha" in let Hk := fresh "Hk" in intros a Ha Hk; cbn [CC.cp_F]; tk_outside.
