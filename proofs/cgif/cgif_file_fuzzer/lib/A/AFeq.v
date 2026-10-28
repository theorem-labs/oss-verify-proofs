(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma Zbv_add_unsigned : forall x k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof.
intros x k. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma unwind_of_chain_length : forall pc0 ch, (1 <= length (unwind_of_chain pc0 ch) <= 30)%nat.
Proof. intros pc0 ch. unfold unwind_of_chain, kUnwindMax. rewrite firstn_length. cbn [length]. lia. Qed.
Lemma val_mem_addr : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.
Lemma le_byte_zero : forall w k, YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma land_m8_64 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 8) = a - a mod 8.
Proof.
intros a Ha. change (2 ^ 64 - 8) with (Z.land (- 2 ^ 3) (Z.ones 64)).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound a 8 ltac:(lia)). apply Z.mod_small. lia.
Qed.
Lemma div8_bounds : forall x, 0 <= x -> 8 * (x / 8) <= x < 8 * (x / 8) + 8.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.
Lemma land_7_mod : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma mod0_factor : forall x k m, 0 < k -> x mod (m * k) = 0 -> x mod k = 0.
Proof. intros x k m Hk H. rewrite <- (Z.mod_mod_divide x (m * k) k) by (exists m; reflexivity). rewrite H. apply Z.mod_0_l. lia. Qed.
Lemma land_ones_mod : forall a k, 0 <= a -> 0 <= k -> Z.land a (Z.ones k) = a mod 2 ^ k.
Proof. intros a k Ha Hk. rewrite Z.land_ones by lia. reflexivity. Qed.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma chunk_val_at : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
a = base_val E (YP09.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.
End h.
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
| |- context [Z.shiftl ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with c
| |- context [Z.shiftr ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with c
| |- context [Z.lor ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with c
| |- context [Z.lxor ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with c
end.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Ltac show_goal := match goal with |- ?g => idtac g end.
Definition flit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition flit4 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 4) 0 0 [YP09.mkChunk a (CVal 4 (SLit v))].
Definition flit1 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 1) 0 0 [YP09.mkChunk a (CVal 1 (SLit v))].
Definition flits8 (a : Z) (vs : list Z) : YP09.region :=
YP09.mkRegion None a (a + 8 * Z.of_nat (length vs)) 0 0
(map (fun iv => YP09.mkChunk (a + 8 * Z.of_nat (fst iv)) (CVal 8 (SLit (snd iv)))) (combine (seq 0 (length vs)) vs)).
Definition fatom8 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition aT : nat := 32.   Definition aC : nat := 33.   Definition aSB : nat := 34.  Definition aTOP : nat := 35.
Definition aLEN : nat := 36.
Definition aIM : nat := 37.
Definition aHW : nat := 38.
Definition aN : nat := 39.
Definition aSHB : nat := 40.
Definition aSP : nat := 41.
Definition aN8 : nat := 42.
Definition aCNT8 : nat := 43.
Definition aB : nat := 44.
Definition aBB : nat := 45.
Definition aBC : nat := 46.
Definition aSLOT : nat := 47.
Definition aQS : nat := 48.
Definition aQF : nat := 49.
Definition aQB : nat := 50.
Definition aJ1 : nat := 51.  Definition aJ2 : nat := 52.  Definition aJ3 : nat := 53.
Definition aHAVf : nat := 54.
Definition IFRAME : Z := 2128.
Definition FF : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(10%nat, mkAF (4096 + 16) (CEIL_MAX - 16) 4)   ;
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)          ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)            ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)            ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aIM, mkAF 0xa7200 (0xa7200 + 8 * 0x7fff) 3);
(aHW, mkAF 0 65535 0);
(aN, mkAF 1 (2 ^ 28) 0);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12);
(aSP, mkAF (SHADOW_OFF + 514) (SHADOW_OFF + CEIL_MAX / 8) 1)   ;
(aN8, mkAF 8 (2 ^ 28) 3);
(aCNT8, mkAF 1 (2 ^ 25) 0);
(aB, mkAF kHighMemBeg (CEIL_MAX - 8192) 13)    ;
(aBB, mkAF 0 (2 ^ 48) 0);
(aBC, mkAF 0 (kBatchSlots - 1) 0);
(aSLOT, mkAF kHighMemBeg (CEIL_MAX - 8) 3);
(aQS, mkAF 1 (2 ^ 48) 0);
(aQF, mkAF 0 (2 ^ 64 - 1) 0);
(aQB, mkAF 0 (2 ^ 48) 0);
(aJ1, mkAF 0 (2 ^ 64 - 1) 0); (aJ2, mkAF 0 (2 ^ 64 - 1) 0); (aJ3, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition A_ialloc : Z := 0x5de68.
Definition IAL_STK : Z := 48.
Definition tfib_ialloc_spec : Prop :=
forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ii : bool),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - IAL_STK -> sp < 2 ^ 64 -> (forall a, sp - IAL_STK <= a < sp -> apresent H mem a) ->
val_mem tfibsegs m TFIB_IAL_FLAG 1 (if ii then 1 else 0) -> val_mem tfibsegs m (TFIB_IAL_FLAG + 1) 1 0 ->
val_mem tfibsegs m 0x9df78 8 0x135aa0 -> val_mem tfibsegs m 0x135aa0 8 4096 ->
(if ii then val_mem tfibsegs m TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16)
else val_mem tfibsegs m TFIB_IAL_W 8 0 /\ val_mem tfibsegs m (TFIB_IAL_W + 8) 8 0) ->
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_ialloc) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 TFIB_IAL_LO /\
(forall x : word, ~ (sp - IAL_STK <= bv_unsigned x < sp) -> ~ (TFIB_IAL_LO <= bv_unsigned x < TFIB_IAL_HI) ->
~ (TFIB_IAL_FLAG <= bv_unsigned x < TFIB_IAL_FLAG + 4) -> mem' x = mem x) /\
(forall a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent H mem a -> apresent H mem' a) /\
let m' := mrestrict H mem' in
val_mem tfibsegs m' TFIB_IAL_FLAG 1 1 /\ val_mem tfibsegs m' (TFIB_IAL_FLAG + 1) 1 0 /\
val_mem tfibsegs m' TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m' (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0))).
End o.
Lemma Forall_nth_f {A} (P : A -> Prop) (l : list A) (i : nat) (x : A) : Forall P l -> nth_error l i = Some x -> P x.
Proof. intros HF He. exact (proj1 (Forall_forall P l) HF x (nth_error_In l i He)). Qed.
Lemma pairwise_ij_f {A} (R : A -> A -> Prop) : forall (l : list A) (i j : nat) (x y : A),
pairwise R l -> nth_error l i = Some x -> nth_error l (i + S j)%nat = Some y -> R x y.
Proof.
induction l as [|a l IH]; intros i j x y HP Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; cbn in Hi, Hj.
- injection Hi as <-. exact (Forall_nth_f _ l j y HF Hj).
- exact (IH i j x y HP Hi Hj).
Qed.
Lemma zdisjoint_sym_f : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.
Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Section s. Context {fx : YK11.FPState}.
Lemma st_ok_add_atom : forall segs E ss ms n f,
st_ok segs E ss ms -> afact_ok E n f -> st_ok segs E (add_atom ss n f) ms.
Proof.
intros segs E ss ms n f (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HG) Hf.
unfold st_ok, add_atom; cbn.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
exact (facts_ok_add_atom E _ n f HG Hf).
Qed.
Definition afact_eqb (f g : afact) : bool := ((af_lo f =? af_lo g) && (af_hi f =? af_hi g) && (af_al2 f =? af_al2 g))%bool.
Definition natfact_eqb (x y : nat * afact) : bool := (Nat.eqb (fst x) (fst y) && afact_eqb (snd x) (snd y))%bool.
Definition acond_eqb (c d : acond) : bool := (branch_cond_beq (ac_c c) (ac_c d) && sv_eqb (ac_a c) (ac_a d) && sv_eqb (ac_b c) (ac_b d))%bool.
Definition svpair_eqb (x y : sv * sv) : bool := (sv_eqb (fst x) (fst y) && sv_eqb (snd x) (snd y))%bool.
Definition inclb {A : Type} (eqb : A -> A -> bool) (l' l : list A) : bool := forallb (fun x => existsb (eqb x) l) l'.
Definition facts_leb (F' F : facts) : bool :=
(inclb natfact_eqb (f_atoms F') (f_atoms F) && inclb acond_eqb (f_conds F') (f_conds F) && inclb svpair_eqb (f_alias F') (f_alias F))%bool.
Definition set_facts (ss : sstate) (F : facts) : sstate := mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) F.
Lemma afact_eqb_eq : forall f g, afact_eqb f g = true -> f = g.
Proof. intros [a b c] [a' b' c'] H. unfold afact_eqb in H. cbn in H. rewrite !Bool.andb_true_iff, !Z.eqb_eq in H. destruct H as [[-> ->] ->]. reflexivity. Qed.
Lemma natfact_eqb_eq : forall x y, natfact_eqb x y = true -> x = y.
Proof. intros [n f] [m g] H. unfold natfact_eqb in H. cbn in H. rewrite Bool.andb_true_iff in H. destruct H as [H1 H2]. apply Nat.eqb_eq in H1. apply afact_eqb_eq in H2. subst. reflexivity. Qed.
Lemma acond_eqb_eq : forall c d, acond_eqb c d = true -> c = d.
Proof. intros [c a b] [c' a' b'] H. unfold acond_eqb in H. cbn in H. rewrite !Bool.andb_true_iff in H. destruct H as [[H1 H2] H3].
apply branch_cond_beq_eq in H1. apply sv_eqb_eq in H2. apply sv_eqb_eq in H3. subst. reflexivity. Qed.
Lemma svpair_eqb_eq : forall x y, svpair_eqb x y = true -> x = y.
Proof. intros [a b] [a' b'] H. unfold svpair_eqb in H. cbn in H. rewrite Bool.andb_true_iff in H. destruct H as [H1 H2]. apply sv_eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity. Qed.
Lemma inclb_incl : forall {A : Type} (eqb : A -> A -> bool) l' l, (forall x y, eqb x y = true -> x = y) -> inclb eqb l' l = true -> forall x, In x l' -> In x l.
Proof. intros A eqb l' l Heq H x Hx. unfold inclb in H. pose proof (proj1 (forallb_forall _ _) H x Hx) as E. cbn beta in E.
apply existsb_exists in E as (y & Hy & Exy). rewrite (Heq _ _ Exy). exact Hy. Qed.
Lemma atoms_ok_In : forall E l, atoms_ok E l <-> (forall nf, In nf l -> afact_ok E (fst nf) (snd nf)).
Proof. intros E l. induction l as [|[n f] l IH]; cbn; [split; [intros _ nf []|intros; exact I]|].
split; [intros [H1 H2] nf [<-|Hin]; [exact H1|exact (proj1 IH H2 nf Hin)] | intros H; split; [exact (H (n, f) (or_introl eq_refl)) | apply (proj2 IH); intros nf Hin; exact (H nf (or_intror Hin))]]. Qed.
Lemma conds_ok_In : forall E l, conds_ok E l <-> (forall c, In c l -> acond_ok E c).
Proof. intros E l. induction l as [|c l IH]; cbn; [split; [intros _ c []|intros; exact I]|].
split; [intros [H1 H2] d [<-|Hin]; [exact H1|exact (proj1 IH H2 d Hin)] | intros H; split; [exact (H c (or_introl eq_refl)) | apply (proj2 IH); intros d Hin; exact (H d (or_intror Hin))]]. Qed.
Lemma alias_ok_In : forall E l, alias_ok E l <-> (forall ab, In ab l -> sv_denot E (fst ab) = sv_denot E (snd ab)).
Proof. intros E l. induction l as [|[a b] l IH]; cbn; [split; [intros _ ab []|intros; exact I]|].
split; [intros [H1 H2] ab [<-|Hin]; [exact H1|exact (proj1 IH H2 ab Hin)] | intros H; split; [exact (H (a, b) (or_introl eq_refl)) | apply (proj2 IH); intros ab Hin; exact (H ab (or_intror Hin))]]. Qed.
Lemma facts_ok_leb : forall E F' F, facts_leb F' F = true -> facts_ok E F -> facts_ok E F'.
Proof.
intros E F' F H (HA & HC & HL). unfold facts_leb in H. rewrite !Bool.andb_true_iff in H. destruct H as [[H1 H2] H3].
split; [|split].
- apply (proj2 (atoms_ok_In E _)). intros nf Hin. apply (proj1 (atoms_ok_In E _) HA). exact (inclb_incl _ _ _ natfact_eqb_eq H1 nf Hin).
- apply (proj2 (conds_ok_In E _)). intros c Hin. apply (proj1 (conds_ok_In E _) HC). exact (inclb_incl _ _ _ acond_eqb_eq H2 c Hin).
- apply (proj2 (alias_ok_In E _)). intros ab Hin. apply (proj1 (alias_ok_In E _) HL). exact (inclb_incl _ _ _ svpair_eqb_eq H3 ab Hin).
Qed.
Lemma st_ok_facts_leb : forall segs E ss ms F', st_ok segs E ss ms -> facts_leb F' (ss_facts ss) = true -> st_ok segs E (set_facts ss F') ms.
Proof.
intros segs E ss ms F' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HG) Hle. unfold st_ok, set_facts; cbn.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
exact (facts_ok_leb E F' _ Hle HG).
Qed.
Lemma st_ok_forget_reg : forall (E : env) ss ms (r : bv 5) (k : nat),
st_ok tfibsegs E ss ms -> r <> 0%bv -> ss_atoms_lt k ss = true ->
st_ok tfibsegs (havoc E k [getr (ms_regs ms) r]) (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff k 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r k HS Hr Hk.
apply st_ok_pin_reg; [ | exact Hr | ].
- eapply (st_ok_agree tfibsegs k); [exact HS | apply env_agree_havoc | exact Hk].
- pose proof (ew_havoc_new E k [getr (ms_regs ms) r] 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as Hn. rewrite Nat.add_0_r in Hn. cbn [nth] in Hn.
cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
End s.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, SHADOW_OFF, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Definition T1term : sv := SAlu ALU_XOR (SOff 38%nat 0) (SAlu ALU_AND (SAlu ALU_XOR (SOff 38%nat 0) (SLit 3)) (SLit 255)).
Lemma T1_val : forall (rho : nat -> Z) hb1, 0 <= hb1 < 256 -> rho 38%nat = 2 + 256 * hb1 -> zev rho T1term = 3 + 256 * hb1.
Proof.
intros rho hb1 Hb Hr. rewrite (zev_only 38 rho T1term eq_refl). rewrite Hr.
assert (C : forallb (fun i => zev (fun _ => 2 + 256 * Z.of_nat i) T1term =? 3 + 256 * Z.of_nat i) (seq 0 256) = true) by (vm_compute; reflexivity).
pose proof (forallb_seq_In _ 256 (Z.to_nat hb1) C ltac:(lia)) as Hx. cbn beta in Hx. rewrite Z2Nat.id in Hx by lia.
apply Z.eqb_eq in Hx. exact Hx.
Qed.
