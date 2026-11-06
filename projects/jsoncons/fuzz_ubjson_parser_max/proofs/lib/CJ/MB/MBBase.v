(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRes.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_MB_MBBase () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB.MBBase.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1fst"; "1pair"; "1prod"; "2eq"; "3N"; "3Z"; "4pot"; "5ac_of"; "5cnt_of"; "5potf"; "5sc3"; "5scal"; "5shift_of"; "6account_bounce"; "6add_slots"; "6aptr"]; ["6area"; "6brkstate"; "6c_avail_meta_area_count"; "6c_avail_meta_count"; "6c_meta_alloc_shift"; "6decay_bounces"; "6del_group"; "6del_slots"; "6dequeue"; "6drop_region"; "6ghdr"; "6hdr_havoc"; "6lhead"; "6mctx"; "6meta"; "6mstate"]; ["6new_region"; "6optr"; "6put_group"; "6put_meta"; "6record_seq"; "6region"; "6rkind"; "6s_ctx"; "6set_active"; "6set_active_map"; "6set_areas"; "6set_avail_meta"; "6set_avail_meta_area_count"; "6set_avail_meta_areas"; "6set_avail_meta_count"; "6set_bounce"]; ["6set_bounces_map"; "6set_brk"; "6set_free_meta_head"; "6set_group_active_idx"; "6set_groups"; "6set_head"; "6set_init_done"; "6set_meta_alloc_shift"; "6set_meta_area_head"; "6set_meta_area_tail"; "6set_metas"; "6set_mmap_counter"; "6set_next_rid"; "6set_regions"; "6set_secret"; "6set_seq"]; ["6set_shadow"; "6set_slots"; "6set_tick"; "6set_unmap_seq_map"; "6set_usage"; "6set_usage_map"; "6shadow"; "6step_seq"; "6strip"; "6upd_ctx"; "6upd_meta"; "6upd_region"; "0ai"; "0b"; "0c"; "0f"]; ["0g"; "0h"; "0i"; "0k"; "0l"; "0m"; "0mo"; "0p"; "0r"; "0rid"; "0s"; "0sc"; "0st"; "0st'"; "7N_countable"; "7Z_countable"]; ["7prod_countable"; "8prod_eq_dec"; "9gmap"; ":eq_dec"; ";eq_dec"; "0v"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition undef {R} (t : M R) : Prop :=
match t with SVis (EUndef _) _ => True | _ => False end.
Lemma undef_vis {R} w (k : Z -> M R) : undef (SVis (EUndef w) k).
Proof. exact I. Qed.
Lemma undef_bad_answer {R} (b : M R) : undef (bad_answer b).
Proof. exact I. Qed.
Lemma gtree_undef {R} E ne bb (t : M R) Q : undef t -> gtree E ne bb t Q.
Proof. destruct t as [r|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.
Lemma gtree_ret {R} E ne bb (r : R) (Q : R -> Prop) : Q r -> gtree E ne bb (SRet r) Q.
Proof. intros H. exact H. Qed.
Lemma gtree_ret' {R} E ne bb (r : R) (Q : R -> Prop) : Q r -> gtree E ne bb (ret r) Q.
Proof. intros H. exact H. Qed.
Lemma gtree_le {R} E (Q : R -> Prop) t ne ne' bb bb' :
(ne <= ne')%nat -> bb <= bb' -> gtree E ne bb t Q -> gtree E ne' bb' t Q.
Proof. intros Hn Hb H. exact (gtree_mono E E Q Q (fun e He => He) (fun r Hr => Hr) t ne ne' bb bb' Hn Hb H). Qed.
Lemma gtree_Q {R} E (Q Q' : R -> Prop) t ne bb :
(forall r, Q r -> Q' r) -> gtree E ne bb t Q -> gtree E ne bb t Q'.
Proof. intros HQ H. exact (gtree_mono E E Q Q' (fun e He => He) HQ t ne ne bb bb (le_n ne) (Z.le_refl bb) H). Qed.
Lemma gtree_vis {R} E ne bb e (k : Z -> M R) Q :
E e -> ecost e <= bb ->
(forall z, good e z -> gtree E ne (bb - ecost e) (k z) Q) ->
gtree E (S ne) bb (SVis e k) Q.
Proof. intros HE HC HK. destruct e; cbn [gtree]; auto. Qed.
Lemma gtree_bind {R S} E (t : M R) (f : R -> M S) Q1 Q ne bb :
gtree E ne bb t Q1 ->
(forall r ne' bb', Q1 r -> gtree E ne' bb' (f r) Q) ->
gtree E ne bb (sbind t f) Q.
Proof.
revert ne bb. induction t as [r|e k IH]; intros ne bb H Hf; cbn [sbind].
- apply Hf. exact H.
- destruct e; cbn [gtree] in H |- *; try exact I;
(destruct ne as [|ne']; [exact H|]); destruct H as (H1 & H2 & H3);
(split; [exact H1|]); (split; [exact H2|]); intros z Hz; (apply IH; [apply H3; exact Hz| exact Hf]).
Qed.
Lemma gtree_guard {R} E ne bb tag c (k bail : M R) Q :
(c = true -> gtree E ne bb k Q) -> gtree E ne bb (guard tag c k bail) Q.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| exact I]. Qed.
Fixpoint leaves {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
match t with
| SRet r => P r
| SVis (EUndef _) _ => True
| SVis _ k => forall z, leaves P (k z)
end.
Lemma leaves_undef {R} P (t : M R) : undef t -> leaves P t.
Proof. destruct t as [r|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.
Lemma leaves_ret {R} (P : R -> Prop) r : P r -> leaves P (SRet r).
Proof. intros H; exact H. Qed.
Lemma leaves_vis {R} P e (k : Z -> M R) : (forall z, leaves P (k z)) -> leaves P (SVis e k).
Proof. intros H. destruct e; cbn; auto. Qed.
Lemma leaves_guard {R} P tag c (k bail : M R) :
(c = true -> leaves P k) -> leaves P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| exact I]. Qed.
Lemma leaves_bind {R S} (t : M R) (f : R -> M S) P1 P :
leaves P1 t -> (forall r, P1 r -> leaves P (f r)) -> leaves P (sbind t f).
Proof.
induction t as [r|e k IH]; intros H Hf; cbn [sbind].
- apply Hf. exact H.
- destruct e; cbn [leaves] in H |- *; try exact I; intros z; apply IH; auto.
Qed.
Lemma leaves_mono {R} (P P' : R -> Prop) t : (forall r, P r -> P' r) -> leaves P t -> leaves P' t.
Proof.
intros HP. induction t as [r|e k IH]; cbn; [auto|]. destruct e; auto; intros H z; apply IH; apply H.
Qed.
Lemma cpath_leaves {R} (P : R -> Prop) L (t : M R) L' r :
cpath L t L' r -> leaves P t -> P r.
Proof.
induction 1 as [L0 r0|L0 e k z L1 r0 Hok Hp IH]; cbn; intros H; [exact H|].
destruct e; try (apply IH; apply H). cbn in Hok. discriminate.
Qed.
Definition sc3 (c : mctx) : Z * Z * Z :=
(c_avail_meta_count c, c_avail_meta_area_count c, c_meta_alloc_shift c).
Definition scal (st : mstate) : Z * Z * Z := sc3 (s_ctx st).
Definition potf (x : Z * Z * Z) : Z :=
let '(cnt, ac, sh) := x in NSLOTS * 2 ^ sh - (cnt + NSLOTS * ac).
Lemma pot_scal : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "<'O'3'5&6r1%211&9&;%114%311%93851pUJ;1").
Proof. intros st. reflexivity. Qed.
Lemma pot_of_scal : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D'O'3'2'5%2211%3212&;r1%211r2%411%:3631&6%114r3%311%?3=31p061pULB1pUJC1").
Proof. intros st st'. intros H. rewrite !pot_scal, H. reflexivity. Qed.
Definition shift_of (x : Z * Z * Z) : Z := snd x.
Definition cnt_of (x : Z * Z * Z) : Z := fst (fst x).
Definition ac_of (x : Z * Z * Z) : Z := snd (fst x).
Lemma shift_scal : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase ">'O'3'5&D&Q7r1%211%411&<&;%115%311%;3:51pUJ=1"). Proof. intros st. reflexivity. Qed.
Lemma cnt_scal : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase ">'O'3'5&C&Q7r1%211%411&8&;%115%311%;3:51pUJ=1"). Proof. intros st. reflexivity. Qed.
Lemma ac_scal : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase ">'O'3'5&B&Q7r1%211%411&7&;%115%311%;3:51pUJ=1"). Proof. intros st. reflexivity. Qed.
Lemma scal_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F'Mp011'O'3'2'5%2211%3212&;&R9r2r1%3221%511&:&Q7%115%711%411%@3<61pUJB1pU0D1"). Proof. intros f st. reflexivity. Qed.
Lemma scal_set_regions : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F'S2'4&S3&RN'Q5%544321'O'3'2'5%2211%3212&;&QMr2r1%3221%511%613%<3821pUJ>1pV<@1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F'S2'4&S3&RN'R6%544321'O'3'2'5%2211%3212&;&R0r2r1%3221%511%613%<3821pUJ>1pV<@1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A'4'O'3'2'5%2211%3212&;&QLr2r1%3221%511%613%<3821pUJ>1pV<@1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_metas : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "M'S2&?&S1'4&S3'5&S4%544321&S0&RN&RO%36872651'N%=4<621'O'3'2%12<<%221=&;&QJr2r1%3221%511%613%;3821pUJ=1pV<?1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_areas : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "M'S2&?&S1'4&S3'5&S4%544321&S0&RN&RO%36872651'@%=4<621'O'3'2%12<<%221=&;&Q:r2r1%3221%511%613%;3821pUJ=1pV<?1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_groups : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "M'S2&?&S1'4&S3'5&S4%544321&S0&RN&RO%36872651'J%=4<621'O'3'2%12<<%221=&;&QDr2r1%3221%511%613%;3821pUJ=1pV<?1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_slots : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "M'S2&?&S1'4&S3'5&S4%544321&S0&RN&RO%36872651'2%12<8%>4=731'O'3%52<<%621=&;&R1r2r1%3221%511%613%:3821pUJ<1pV<>1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_set_tick : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A'4'O'3'2'5%2211%3212&;&R2r2r1%3221%511%613%<3821pUJ>1pV<@1"). Proof. intros v st. reflexivity. Qed.
Lemma scal_put_meta : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D&?'N'O'3'2'5%2211%3212&;&Q3r3r2r1%43321%611%713%=3921pUJ?1pUBA1pU<C1"). Proof. intros m r st. reflexivity. Qed.
Lemma scal_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "E&?'Np011'O'3'2'5%2211%3212&;&R:r3r2r1%43321%611%713%=3921pUJ?1pU0A1pU<D1"). Proof. intros m f st. reflexivity. Qed.
Lemma scal_put_group : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F&?&Q1'5'O'3'2%1244%2215&;&Q2r4r3r2r1%544321%711%813%=3:21pUJ?1pTJA1pU>C1pU2E1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma scal_set_group_active_idx : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "C&?'5'O'3'2%1244%2215&;&QCr3r2r1%43321%611%713%<3921pUJ>1pTJ@1pU2B1").
Proof. intros g ai st. unfold set_group_active_idx. destruct (get_group st g); reflexivity. Qed.
Lemma scal_del_group : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&?'O'3'2'5%2211%3212&;&Fr2r1%3221%511%613%<3821pUJ>1pU2@1"). Proof. intros g st. reflexivity. Qed.
Lemma scal_add_slots : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "G&?'5'O'3'2%1244%2215&;&>r5r4r3r2r1%6554321%811%913%>3;21pUJ@1pTNB1pUFC1pU@E1pU<F1"). Proof. intros m p s c st. reflexivity. Qed.
Lemma scal_del_slots : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "E&?'5'O'3'2%1244%2215&;&Gr4r3r2r1%544321%711%813%=3:21pUJ?1pTNA1pUFB1pU@D1"). Proof. intros p s c st. reflexivity. Qed.
Lemma scal_drop_region : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A'4'O'3'2'5%2211%3212&;&Ir2r1%3221%511%613%<3821pUJ>1pUD@1"). Proof. intros rid st. reflexivity. Qed.
Lemma scal_upd_region : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "E'4'Q5p011'O'3'2'5%2211%3212&;&R;r3r2r1%43321%611%713%=3921pUJ?1pU0A1pUDD1").
Proof. intros rid f st. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.
Lemma scal_new_region : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "H'Q6'5'O'3'2%1244%2215&;&0'4&Q0r4r3r2r1%544321%83>71%:11%;14%@3=21pUJB1pU:D1pTLE1pU8G1"). Proof. intros k b l st. reflexivity. Qed.
Lemma scal_set_active : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "C'5&Q1'O'3'2%1255%2216&;&Q8r3r2r1%43321%611%713%<3921pUJ>1pV<@1pUHB1"). Proof. intros sc v st. reflexivity. Qed.
Lemma scal_set_usage : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "B'5'O'3'2%1244%2215&;&R4r3r2r1%43321%611%713%<3921pUJ>1pV<@1pUHA1"). Proof. intros sc v st. reflexivity. Qed.
Lemma scal_set_bounce : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "B'5'O'3'2%1244%2215&;&Q?r3r2r1%43321%611%713%<3921pUJ>1pV<@1pU6A1"). Proof. intros i v st. reflexivity. Qed.
Lemma scal_step_seq : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase ">'O'3'2'5%2211%3212&;&R7r1%211%411%513%;3721pUJ=1").
Proof. intros st. unfold step_seq. destruct (_ =? _); reflexivity. Qed.
Lemma scal_record_seq : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'O'3'2%1244%2215&;&Q4r2r1%3221%511%613%;3821pUJ=1pUH?1").
Proof. intros sc st. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma scal_account_bounce : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'O'3'2%1244%2215&;&=r2r1%3221%511%613%;3821pUJ=1pUH?1").
Proof. intros sc st.
unfold account_bounce. destruct (sc_in_seq_range sc); [| reflexivity].
cbv zeta. destruct (_ && _); [| reflexivity]. destruct (_ <? _); reflexivity.
Qed.
Lemma scal_decay_bounces : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'O'3'2%1244%2215&;&Er2r1%3221%511%613%;3821pUJ=1pUH?1").
Proof. intros sc st. unfold decay_bounces. destruct (_ && _); reflexivity. Qed.
Lemma scal_set_head : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D'L&Q1'O'3'2'5%2211%3212&;&QEr3r2r1%43321%611%713%=3921pUJ?1pV<A1pU4C1").
Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma scal_dequeue : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D'L&?'O'3'2'5%2211%3212&;&Hr3r2r1%43321%611%713%=3921pUJ?1pU<A1pU4C1").
Proof. intros h m st.
unfold dequeue. cbv zeta. rewrite scal_upd_meta.
destruct (negb _); [| apply scal_set_head].
set (st1 := match m_prev _ with Some pv => _ | None => st end).
set (st2 := match m_next _ with Some nx => _ | None => st1 end).
assert (H1 : scal st1 = scal st) by (subst st1; destruct (m_prev _); reflexivity).
assert (H2 : scal st2 = scal st) by (subst st2; destruct (m_next _); [rewrite scal_upd_meta|]; exact H1).
destruct (optr_eqb _ _); [rewrite scal_set_head|]; exact H2.
Qed.
Lemma scal_strip : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase ">'O'3'2'5%2211%3212&;&R8r1%211%411%513%;3721pUJ=1"). Proof. intros st. reflexivity. Qed.
Lemma scal_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&?'O'3'2'5%2211%3212&;&Kr2r1%3221%511%613%<3821pUJ>1pTL@1"). Proof. intros b st. reflexivity. Qed.
Lemma sc3_set_secret : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'M'3'2%1244%2215&:&QNr2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'M'3'2%1244%2215&:&QFr2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'M'3'2%1244%2215&:&QKr2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&Q1'M'3'2'5%2211%3212&:&QBr2r1%3221%511%613%<3821pTN>1pV<@1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&Q1'M'3'2'5%2211%3212&:&Q;r2r1%3221%511%613%<3821pTN>1pV<@1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&Q1'M'3'2'5%2211%3212&:&QHr2r1%3221%511%613%<3821pTN>1pV<@1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&Q1'M'3'2'5%2211%3212&:&QIr2r1%3221%511%613%<3821pTN>1pV<@1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A&Q1'M'3'2'5%2211%3212&:&Q=r2r1%3221%511%613%<3821pTN>1pV<@1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "E'S2'5&S4&RO&?%544321'M'3'2%1288%2219&:&Q9r2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D'S2'5&S4&RO%443213'M'3'2%1277%2218&:&R5r2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D'S2'5&S4&RO%443213'M'3'2%1277%2218&:&R3r2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "D'S2'5&S4&RO%443213'M'3'2%1277%2218&:&Q@r2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_seq : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "@'5'M'3'2%1244%2215&:&QOr2r1%3221%511%613%;3821pTN=1pV<?1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_brk : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "A'A'M'3'2'5%2211%3212&:&QAr2r1%3221%511%613%<3821pTN>1pV<@1"). Proof. intros v c. reflexivity. Qed.
Lemma sc3_s_ctx : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "?'O'3'2'5%2211%3212&:&Q7r1%211%411&;%114%<3831pUJ>1"). Proof. intros st. reflexivity. Qed.
Lemma sc3_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F'5'M'3'2%1244%2215&:&Q>r2r1%3221%511(1&B%115%34??71&D%118%64>B31%A3>81pTNC1pV<E1").
Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F'5'M'3'2%1244%2215&:&Q<r2r1%3221%511(1&C%115%34??17&D%118%64>B31%A3>81pTNC1pV<E1").
Proof. intros v c. reflexivity. Qed.
Lemma sc3_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_MB_MBBase "F'5'M'3'2%1244%2215&:&QGr2r1%3221%511(1&C%115&B%117%54AA31%64>B1:%A3>81pTNC1pV<E1").
Proof. intros v c. reflexivity. Qed.
End CEIL_WRAP_1.
#[export] Hint Rewrite scal_upd_ctx scal_set_regions scal_set_shadow scal_set_next_rid scal_set_metas
scal_set_areas scal_set_groups scal_set_slots scal_set_tick scal_put_meta scal_upd_meta scal_put_group
scal_set_group_active_idx scal_del_group scal_add_slots scal_del_slots scal_drop_region scal_upd_region
scal_new_region scal_set_active scal_set_usage scal_set_bounce scal_step_seq scal_record_seq
scal_account_bounce scal_decay_bounces scal_set_head scal_dequeue scal_strip scal_hdr_havoc
sc3_set_secret sc3_set_init_done sc3_set_mmap_counter sc3_set_free_meta_head sc3_set_avail_meta
sc3_set_meta_area_head sc3_set_meta_area_tail sc3_set_avail_meta_areas sc3_set_active_map
sc3_set_usage_map sc3_set_unmap_seq_map sc3_set_bounces_map sc3_set_seq sc3_set_brk sc3_s_ctx
sc3_set_avail_meta_count sc3_set_avail_meta_area_count sc3_set_meta_alloc_shift : scal.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Definition retK {R X} (P : mstate -> X -> Prop) (k : mstate -> X -> M R) (t : M R) : Prop :=
(exists st' x, t = k st' x /\ P st' x) \/ undef t.
Definition retK1 {R} (P : mstate -> Prop) (k : mstate -> M R) (t : M R) : Prop :=
(exists st', t = k st' /\ P st') \/ undef t.
Lemma retK_here {R X} (P : mstate -> X -> Prop) (k : mstate -> X -> M R) st x :
P st x -> retK P k (k st x).
Proof. intros H. left. exists st, x. auto. Qed.
Lemma retK1_here {R} (P : mstate -> Prop) (k : mstate -> M R) st :
P st -> retK1 P k (k st).
Proof. intros H. left. exists st. auto. Qed.
Lemma retK_undef {R X} (P : mstate -> X -> Prop) (k : mstate -> X -> M R) t : undef t -> retK P k t.
Proof. intros H. right. exact H. Qed.
Lemma retK1_undef {R} (P : mstate -> Prop) (k : mstate -> M R) t : undef t -> retK1 P k t.
Proof. intros H. right. exact H. Qed.
Lemma retK_mono {R X} (P P' : mstate -> X -> Prop) (k : mstate -> X -> M R) t :
(forall st x, P st x -> P' st x) -> retK P k t -> retK P' k t.
Proof. intros HP [(st' & x & -> & H)|H]; [left; exists st', x; auto| right; exact H]. Qed.
Lemma gtree_retK {R X} (P : mstate -> X -> Prop) (k : mstate -> X -> M R) t E ne bb Q :
retK P k t -> (forall st' x, P st' x -> gtree E ne bb (k st' x) Q) -> gtree E ne bb t Q.
Proof. intros [(st' & x & -> & H)|H] HK; [apply HK; exact H| apply gtree_undef; exact H]. Qed.
Lemma gtree_retK1 {R} (P : mstate -> Prop) (k : mstate -> M R) t E ne bb Q :
retK1 P k t -> (forall st', P st' -> gtree E ne bb (k st') Q) -> gtree E ne bb t Q.
Proof. intros [(st' & -> & H)|H] HK; [apply HK; exact H| apply gtree_undef; exact H]. Qed.
Lemma leaves_retK {R X} (P : mstate -> X -> Prop) (k : mstate -> X -> M R) t PL :
retK P k t -> (forall st' x, P st' x -> leaves PL (k st' x)) -> leaves PL t.
Proof. intros [(st' & x & -> & H)|H] HK; [apply HK; exact H| apply leaves_undef; exact H]. Qed.
Lemma leaves_retK1 {R} (P : mstate -> Prop) (k : mstate -> M R) t PL :
retK1 P k t -> (forall st', P st' -> leaves PL (k st')) -> leaves PL t.
Proof. intros [(st' & -> & H)|H] HK; [apply HK; exact H| apply leaves_undef; exact H]. Qed.
Lemma guard_shape {R} tag c (k bail : M R) : guard tag c k bail = k \/ undef (guard tag c k bail).
Proof. unfold guard. destruct c; [left; reflexivity| right; exact I]. Qed.
End CEIL_WRAP_2.
Ltac shape_guard :=
match goal with
| |- retK _ _ (guard ?t ?c ?kk ?b) => destruct (guard_shape t c kk b) as [-> | ?U]; [| right; exact U]
| |- retK1 _ _ (guard ?t ?c ?kk ?b) => destruct (guard_shape t c kk b) as [-> | ?U]; [| right; exact U]
end.
Ltac shape_case :=
lazymatch goal with
| |- retK _ _ (match ?c with _ => _ end) => destruct c
| |- retK1 _ _ (match ?c with _ => _ end) => destruct c
end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Definition SAME (st : mstate) : mstate -> Prop := fun st' => scal st' = scal st.
Definition SAME2 {X} (st : mstate) : mstate -> X -> Prop := fun st' _ => scal st' = scal st.
Lemma queue_shape {R} h m st (k : mstate -> M R) bail : retK1 (SAME st) k (queue h m st k bail).
Proof.
unfold queue. cbv zeta. shape_guard. shape_guard.
destruct (get_head st h) as [head|].
- apply retK1_here. unfold SAME. destruct (m_prev _); autorewrite with scal; reflexivity.
- apply retK1_here. unfold SAME. autorewrite with scal; reflexivity.
Qed.
Lemma free_meta_shape {R} m st (k : mstate -> M R) bail : retK1 (SAME st) k (free_meta m st k bail).
Proof.
unfold free_meta. destruct (queue_shape LFree m (put_meta m meta0 st) k bail) as [(st' & -> & H)|U].
- apply retK1_here. exact H.
- right; exact U.
Qed.
Lemma activate_group_shape {R} m st (k : mstate -> Z -> M R) bail :
retK (SAME2 st) k (activate_group m st k bail).
Proof. unfold activate_group. cbv zeta. shape_guard. apply retK_here. reflexivity. Qed.
Lemma dec_slots_shape {R} st p (k : aptr -> Z -> M R) bail :
(exists m idx, dec_slots st p k bail = k m idx) \/ undef (dec_slots st p k bail).
Proof. unfold dec_slots. destruct (s_slots st !! p) as [[m idx]|]; [left; eauto| right; exact I]. Qed.
Lemma ta_fin_shape {R} st m mask (k : mstate -> Z -> M R) st0 :
scal st = scal st0 -> retK (SAME2 st0) k (ta_fin st m mask k).
Proof. intros H. unfold ta_fin. apply retK_here. unfold SAME2. autorewrite with scal. exact H. Qed.
Lemma try_avail_shape {R} sc st (k : mstate -> Z -> M R) bail : retK (SAME2 st) k (try_avail sc st k bail).
Proof.
unfold try_avail.
destruct (active st sc) as [m|]; [| apply retK_here; reflexivity]. cbv zeta.
destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply ta_fin_shape; reflexivity|].
set (step1 := if m_freed (get_meta_rec st m) =? 0 then _ else _).
assert (S1 : match step1 with Some (st1, _) => scal st1 = scal st | None => True end).
{ subst step1. destruct (m_freed _ =? 0).
- destruct (active (dequeue (LActive sc) m st) sc); [| exact I]. apply scal_dequeue.
- destruct (m_next _); [| exact I]. apply scal_set_active. }
clearbody step1. destruct step1 as [[st1 m1]|].
2:{ shape_case; [apply retK_here; unfold SAME2; apply scal_dequeue| right; exact I]. }
set (p2 := if (_ =? mask_upto _) && negb _ then _ else (st1, m1, m_freed (get_meta_rec st1 m1))).
assert (S2 : let '(st2, _, _) := p2 in scal st2 = scal st).
{ subst p2. destruct (_ && _); [| exact S1]. destruct (m_next _); [| exact S1]. rewrite scal_set_active. exact S1. }
clearbody p2. destruct p2 as [[st2 m2] mask].
set (p3 := if Z.land mask _ =? 0 then _ else (st2, m2)).
assert (S3 : let '(st3, _) := p3 in scal st3 = scal st).
{ subst p3. destruct (_ =? 0); [| exact S2]. destruct (negb _).
- destruct (m_next _); [rewrite scal_set_active|]; exact S2.
- cbv zeta. destruct (m_mem _); [rewrite scal_set_group_active_idx|]; exact S2. }
clearbody p3. destruct p3 as [st3 m3].
match goal with |- retK _ _ (activate_group ?a ?s ?kk ?b) =>
destruct (activate_group_shape a s kk b) as [(st4 & mk & -> & H4)|U]; [| right; exact U] end.
cbn beta. shape_guard.
apply ta_fin_shape. rewrite scal_decay_bounces. unfold SAME2 in H4. rewrite H4. exact S3.
Qed.
Lemma ag_tail_shape {R} st sc m p cnt ai (k : mstate -> optr -> M R) :
exists st4, ag_tail lay_none st sc m p cnt ai k = k st4 (Some m) /\ scal st4 = scal st.
Proof. unfold ag_tail. cbv zeta. eexists. split; [reflexivity|]. autorewrite with scal. reflexivity. Qed.
End CEIL_WRAP_3.
Ltac sproj :=
cbn [s_ctx s_regions s_shadow s_next_rid s_metas s_areas s_groups s_slots s_tick s_secret s_reserved
upd_ctx set_regions set_shadow set_next_rid Malloc.set_metas set_areas Malloc.set_groups set_slots set_tick
c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta c_avail_meta_count
c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas
c_active c_usage c_unmap_seq c_bounces c_seq c_brk
set_secret set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
set_avail_meta_area_count set_meta_alloc_shift set_meta_area_head set_meta_area_tail
set_avail_meta_areas set_active_map set_usage_map set_unmap_seq_map set_bounces_map set_seq set_brk
ctx scal sc3 fst snd new_region put_meta upd_meta upd_region drop_region del_group put_group
set_active set_usage set_bounce shift_of cnt_of ac_of potf].
Ltac sproj_in H :=
cbn [s_ctx s_regions s_shadow s_next_rid s_metas s_areas s_groups s_slots s_tick s_secret s_reserved
upd_ctx set_regions set_shadow set_next_rid Malloc.set_metas set_areas Malloc.set_groups set_slots set_tick
c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta c_avail_meta_count
c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas
c_active c_usage c_unmap_seq c_bounces c_seq c_brk
set_secret set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
set_avail_meta_area_count set_meta_alloc_shift set_meta_area_head set_meta_area_tail
set_avail_meta_areas set_active_map set_usage_map set_unmap_seq_map set_bounces_map set_seq set_brk
ctx scal sc3 fst snd new_region put_meta upd_meta upd_region drop_region del_group put_group
set_active set_usage set_bounce shift_of cnt_of ac_of potf] in H.
Ltac cproj := cbn [shift_of cnt_of ac_of fst snd potf].
Ltac cproj_in H := cbn [shift_of cnt_of ac_of fst snd potf] in H.
Ltac gcase :=
lazymatch goal with
| |- gtree _ _ _ (match ?c with _ => _ end) _ => first [is_var c; destruct c | destruct c eqn:?]
| |- leaves _ (match ?c with _ => _ end) => first [is_var c; destruct c | destruct c eqn:?]
end.
Section CEIL_WRAP_4.
Context {RUNp : RunP}.
Lemma am_take_shape {R} st (k : mstate -> optr -> M R) bail :
retK (fun st' x => scal st' = (c_avail_meta_count (s_ctx st) - 1, c_avail_meta_area_count (s_ctx st), c_meta_alloc_shift (s_ctx st))
/\ x <> None) k (am_take st k bail).
Proof.
unfold am_take, ctx. destruct (c_avail_meta (s_ctx st)) as [m|]; [| right; exact I].
apply retK_here. split; [| discriminate]. sproj. reflexivity.
Qed.
Lemma am_carve_shape {R} st p (k : mstate -> optr -> M R) bail :
retK (fun st' x => scal st' = (NSLOTS - 1, c_avail_meta_area_count (s_ctx st) - 1, c_meta_alloc_shift (s_ctx st))
/\ x <> None) k (am_carve st p k bail).
Proof.
unfold am_carve. cbv zeta. unfold ctx.
destruct (c_meta_area_tail _); (eapply retK_mono; [| apply am_take_shape]); cbv beta; intros st' x [H1 H2];
(split; [| exact H2]); rewrite H1; sproj; reflexivity.
Qed.
Lemma PGSZ_val : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma NSLOTS_val : NSLOTS = 101. Proof. reflexivity. Qed.
Lemma UNIT_val : UNIT = 16. Proof. reflexivity. Qed.
Lemma IB_val : IB = 4. Proof. reflexivity. Qed.
Lemma GMAX_val : GMAX = 1052672. Proof. reflexivity. Qed.
Lemma AMC_val : AMC = 65. Proof. reflexivity. Qed.
Lemma round_up_pg_spec' x : x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
unfold round_up_pg. rewrite PGSZ_val. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
change (2 ^ 12) with 4096.
pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)).
pose proof (Z_div_mod_eq_full (-x) 4096).
split; [lia|].
replace (x + (-x) mod 4096) with ((- ((-x) / 4096)) * 4096) by lia.
apply Z_mod_mult.
Qed.
Lemma round_up_pg_le_aligned x y : x <= y -> y mod 4096 = 0 -> round_up_pg x <= y.
Proof.
intros Hxy Hy. destruct (round_up_pg_spec' x) as [H1 H2].
pose proof (Z_div_mod_eq_full (round_up_pg x) 4096). pose proof (Z_div_mod_eq_full y 4096).
assert (round_up_pg x / 4096 <= y / 4096) by lia. lia.
Qed.
Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof.
intros H. apply round_up_pg_le_aligned; [| apply round_up_pg_spec'].
pose proof (round_up_pg_spec' y). lia.
Qed.
Lemma round_up_pg_id x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. pose proof (round_up_pg_spec' x). pose proof (round_up_pg_le_aligned x x ltac:(lia) H). lia. Qed.
Lemma round_up_pg_idem x : round_up_pg (round_up_pg x) = round_up_pg x.
Proof. apply round_up_pg_id. apply round_up_pg_spec'. Qed.
Lemma mmap_len_eq x : mmap_len x = round_up_pg x.
Proof.
unfold mmap_len, State.page_round_up_Z. change State.page_size with 4096.
destruct (round_up_pg_spec' x) as [H1 H2].
pose proof (Z_div_mod_eq_full (round_up_pg x) 4096).
pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)).
nia.
Qed.
Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof. rewrite mmap_len_eq. apply round_up_pg_idem. Qed.
Lemma shiftl_2 s : 0 <= s -> Z.shiftl 2 s = 2 * 2 ^ s.
Proof. intros H. rewrite Z.shiftl_mul_pow2 by exact H. reflexivity. Qed.
Lemma pow2_pos s : 0 <= s -> 1 <= 2 ^ s.
Proof. intros H. pose proof (Z.pow_pos_nonneg 2 s). lia. Qed.
Lemma is_fixed_MAPFX : is_fixed (MAP_PRIVATE + MAP_ANON + MAP_FIXED) = true.
Proof. reflexivity. Qed.
Lemma is_fixed_MAPF : is_fixed (MAP_PRIVATE + MAP_ANON) = false.
Proof. reflexivity. Qed.
Lemma div_le_of_mul a x y : 0 < a -> a * x <= y -> x <= y / a.
Proof. intros Ha H. apply Z.div_le_lower_bound; lia. Qed.
Section SE.
Local Abbreviation SEC_T_size_class_range := (forall sc, 0 <= size_class sc <= 8191) (only parsing).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_size_class_range) 0%nat 0%nat).
Lemma size_class_range : ltac:(sec_stmt2 constr:(SEC_T_size_class_range) 1%nat 0%nat).
Proof.
unfold size_class. generalize (Z.to_nat sc) as n. intros n.
do 48 (destruct n as [|n]; [cbn; lia|]). cbn. destruct n; cbn; lia.
Qed.
End SE.
Lemma size_class_small sc : sc < 9 -> 0 <= size_class sc <= 9.
Proof.
intros H. unfold size_class.
assert (Hn : (Z.to_nat sc <= 8)%nat) by lia. revert Hn.
generalize (Z.to_nat sc) as n. intros n Hn.
do 9 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.
Lemma small_cnt_range sc i : 0 <= small_cnt sc i <= 31.
Proof.
unfold small_cnt. generalize (Z.to_nat sc) as a. generalize (Z.to_nat i) as b. intros b a.
do 9 (destruct a as [|a]; [do 3 (destruct b as [|b]; [cbn; lia|]); destruct b; cbn; lia|]).
destruct a, b; cbn; lia.
Qed.
Lemma small_cnt_pick_range sc u : 0 <= small_cnt_pick sc u <= 31.
Proof. unfold small_cnt_pick. destruct (negb _); [apply small_cnt_range|]. destruct (negb _); apply small_cnt_range. Qed.
Lemma med_cnt_range i : 0 <= med_cnt i <= 32.
Proof.
unfold med_cnt. generalize (Z.to_nat i) as n. intros n.
do 4 (destruct n as [|n]; [cbn; lia|]). cbn. destruct n; cbn; lia.
Qed.
Lemma halve_even_range f : forall c u, 0 <= c -> 0 <= halve_even f c u <= c.
Proof.
induction f as [|f IH]; intros c u Hc; cbn [halve_even]; [lia|].
destruct (_ && _); [| lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
specialize (IH (c / 2) u). assert (0 <= c / 2 <= c) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia.
Qed.
Lemma halve_big_spec f : forall c size, 0 <= c -> 0 <= size ->
0 <= halve_big f c size <= c /\ (c < 2 ^ (Z.of_nat f) -> size * halve_big f c size < 65536 * UNIT).
Proof.
induction f as [|f IH]; intros c size Hc Hs; cbn [halve_big].
- change (2 ^ Z.of_nat 0) with 1. split; [lia|]. intros. replace c with 0 by lia. rewrite Z.mul_0_r. reflexivity.
- destruct (Z.leb_spec (65536 * UNIT) (size * c)) as [L|L].
+ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
assert (0 <= c / 2 <= c) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
destruct (IH (c / 2) size ltac:(lia) Hs) as [A B]. split; [lia|].
intros Hc2. apply B. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc2 by lia.
pose proof (Z_div_mod_eq_full c 2). pose proof (Z.mod_pos_bound c 2 ltac:(lia)). lia.
+ split; [lia|]. intros _. exact L.
Qed.
Lemma mul_le_bound a b A B : 0 <= a <= A -> 0 <= b <= B -> 0 <= a * b <= A * B.
Proof. intros. nia. Qed.
Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.
Lemma ecost_brk0 : ecost (EBrk 0) = 0. Proof. reflexivity. Qed.
Lemma ecost_brk_le a : ecost (EBrk a) <= 2 * PGSZ.
Proof. cbn [ecost]. destruct (a =? 0); rewrite PGSZ_val; lia. Qed.
Lemma ecost_mmap_fixed a l p : ecost (EMmap a l p (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) = 0.
Proof. reflexivity. Qed.
Lemma ecost_mmap_anon a l p : ecost (EMmap a l p (MAP_PRIVATE + MAP_ANON)) = mmap_len l.
Proof. reflexivity. Qed.
Lemma ecost_mprotect a l p : ecost (EMprotect a l p) = 0. Proof. reflexivity. Qed.
Lemma ecost_munmap a l : ecost (EMunmap a l) = 0. Proof. reflexivity. Qed.
Lemma mprotect_answer_ok_0 : mprotect_answer_ok 0 = true. Proof. reflexivity. Qed.
Lemma munmap_answer_ok_0 : munmap_answer_ok 0 = true. Proof. reflexivity. Qed.
Lemma good_mmap_anon a l p z : good (EMmap a l p (MAP_PRIVATE + MAP_ANON)) z -> is_err z = false.
Proof. cbn. intros [H|H]; [discriminate H| exact H]. Qed.
End CEIL_WRAP_4.
