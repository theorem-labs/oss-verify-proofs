(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0f YL02 YL0a YL0b YL00 YL0c YL09 YL0k YL0o YL0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition STDFDS : list (word * FdEntry) :=
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Lemma bv_eqb_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof.
intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne].
- apply bv_eqb_eq. reflexivity.
- destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E.
apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
rewrite !Z.mod_small in E by lia. contradiction.
Qed.
Lemma fd_insert3_std : forall e0 e, fd_insert ((Z_to_bv 64 3, e0) :: STDFDS) (Z_to_bv 64 3) e = (Z_to_bv 64 3, e) :: STDFDS.
Proof. intros. unfold fd_insert, STDFDS. cbn [List.filter fst negb]. rewrite !bv_eqb_lit by lia. cbn. reflexivity. Qed.
Lemma fd_remove3_std : forall e0, fd_remove ((Z_to_bv 64 3, e0) :: STDFDS) (Z_to_bv 64 3) = STDFDS.
Proof. intros. unfold fd_remove, STDFDS. cbn [List.filter fst negb]. rewrite !bv_eqb_lit by lia. cbn. reflexivity. Qed.
Lemma fd_insert_std3 : forall e, fd_insert STDFDS (Z_to_bv 64 3) e = (Z_to_bv 64 3, e) :: STDFDS.
Proof. intros. unfold fd_insert, STDFDS. cbn [List.filter fst negb]. rewrite !bv_eqb_lit by lia. cbn. reflexivity. Qed.
Definition grow_k (f : nat) (L cap : Z) (buf : sptr) (p : option sptr) : M rd_result :=
match p with
| None => ret RdOOM
| Some nb => bind (free (Some buf)) (fun _ => read_phase f L (2 * cap) nb)
end.
Lemma read_phase_loaded_eq : forall f L cap buf,
(L <? cap) = true -> read_phase (S f) L cap buf = ret (RdLoaded buf cap).
Proof. intros f L cap buf H. cbn [read_phase]. rewrite H. reflexivity. Qed.
Lemma read_phase_refused_eq : forall f L cap buf,
(L <? cap) = false -> (MAX_INPUT <=? cap) = true -> read_phase (S f) L cap buf = ret RdRefused.
Proof. intros f L cap buf H1 H2. cbn [read_phase]. rewrite H1, H2. reflexivity. Qed.
Lemma read_phase_grow_eq : forall f L cap buf,
(L <? cap) = false -> (MAX_INPUT <=? cap) = false ->
read_phase (S f) L cap buf = bind (malloc (2 * cap)) (grow_k f L cap buf).
Proof. intros f L cap buf H1 H2. cbn [read_phase]. rewrite H1, H2. reflexivity. Qed.
Lemma bind_ext1 {A B} : forall (m m' : M A) (f : A -> M B) (s : astate), m = m' -> bind m f s = bind m' f s.
Proof. intros m m' f s ->. reflexivity. Qed.
Lemma bind_ret_l {A B} : forall (x : A) (f : A -> M B) (s : astate), bind (ret x) f s = f x s.
Proof. intros. reflexivity. Qed.
Lemma blocks_after_grow : forall (b1 b2 l1 l2 : list (sptr * Z)) (buf nb : sptr) (cap : Z) (ub2 ub3 : list (sptr * Z)),
ub2 = b1 ++ (nb, 2 * cap) :: b2 -> [(buf, cap)] = b1 ++ b2 ->
ub2 = l1 ++ (buf, cap) :: l2 -> ub3 = l1 ++ l2 -> 0 < cap ->
ub3 = [(nb, 2 * cap)].
Proof.
intros b1 b2 l1 l2 buf nb cap ub2 ub3 E1 E2 E3 E4 Hcap. subst ub2 ub3.
remember (2 * cap) as c2 eqn:Hc2.
destruct b1 as [|x b1'].
- cbn in E2. subst b2. cbn in E3.
destruct l1 as [|y [|z l1'']]; cbn in E3.
+ exfalso. injection E3 as _ H _. lia.
+ injection E3 as <- <-. reflexivity.
+ exfalso. injection E3 as _ _ H. destruct l1''; discriminate.
- cbn in E2. injection E2 as <- Hn. symmetry in Hn. apply app_eq_nil in Hn as [-> ->]. cbn in E3.
destruct l1 as [|y [|z l1'']]; cbn in E3.
+ injection E3 as <-. reflexivity.
+ exfalso. injection E3 as _ _ H _. lia.
+ exfalso. injection E3 as _ _ H. destruct l1''; discriminate.
Qed.
Lemma blocks_same_ptr : forall B MR (LAWS : MR_laws B MR) L A m md p q n n',
MR L A m md -> In (p, n) (user_blocks A) -> In (q, n') (user_blocks A) -> 0 < n -> 0 < n' ->
ptr_addr L p = ptr_addr L q -> n = n'.
Proof.
intros B MR LAWS L A m md p q n n' HMR Hp Hq Hn Hn' Heq.
destruct (Z.eq_dec n n') as [|Hne]; [assumption|]. exfalso.
pose proof (mr_blocks_disjoint B MR LAWS L A m md HMR) as HD. unfold blocks in HD.
revert HD Hp Hq. induction (user_blocks A) as [|b bl IH]; intros HD Hp Hq; [destruct Hp|].
cbn [map pairwise] in HD. destruct HD as [Hhd Htl].
destruct Hp as [->|Hp]; destruct Hq as [Hq'|Hq].
- apply Hne. congruence.
- specialize (Hhd (ptr_addr L q, n') ltac:(apply in_map_iff; exists (q, n'); auto)). unfold ranges_disjoint in Hhd. cbn [fst snd] in Hhd. lia.
- subst b. specialize (Hhd (ptr_addr L p, n) ltac:(apply in_map_iff; exists (p, n); auto)). unfold ranges_disjoint in Hhd. cbn [fst snd] in Hhd. lia.
- apply IH; assumption.
Qed.
Lemma sep_check_outside : forall B MR (LAWS : MR_laws B MR) (AX : AllocExtra B MR) E m G L A md p sz rs,
facts_ok E G -> stack_anchored E G   -> MR L A m md -> In (p, sz) (user_blocks A) -> ms_segs B <> [] ->
sep_check B G rs = true ->
forall r x, In r rs -> base_val E (r_base r) + r_lo r <= x < base_val E (r_base r) + r_hi r ->
~ (ptr_addr L p <= x < ptr_addr L p + sz).
Proof.
intros B MR LAWS AX E m G L A md p sz rs HG HSA HMR Hin Hne Hsep r x Hr Hx Hpx.
pose proof (forallb_In _ _ r Hsep Hr) as H. cbn beta in H.
pose proof (mr_blocks B MR LAWS L A m md p sz (x - ptr_addr L p) HMR Hin ltac:(lia)) as (_ & Hplo & Hphi & _).
destruct (r_base r) as [k|] eqn:Hb; cbn [base_val] in Hx.
- cbn [blk_size] in H. destruct (anch_lo G k) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in H.
pose proof (stack_anchored_sound E G k K HSA HK). pose proof YM05.alloc_ceiling_val. lia.
- apply andb_prop in H as [Hnz H]. apply Z.ltb_lt in Hnz.
apply YL09.existsb_In in H as (sg & Hsg & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply (ax_blocks_img AX L A m md p sz (x - ptr_addr L p) HMR Hin ltac:(lia)).
replace (ptr_addr L p + (x - ptr_addr L p)) with x by lia.
apply (in_img_of_reserved B sg); [exact Hsg | lia | exact Hne].
Qed.
Lemma LH_mem_sep : sep_check src0_msyms RD_facts LH_mem = true /\ sep_check src0_msyms (ss_facts S_RE) (ss_mem S_RE) = true /\
sep_check src0_msyms (ss_facts S_CP) (ss_mem S_CP) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma read_stage_img : forall i, 0 <= i < 65536 -> in_img src0_msyms (RS_LO + i).
Proof.
intros i Hi. unfold in_img. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|].
match goal with |- exists s, In s ?l /\ _ => let v := eval vm_compute in l in change l with v end.
eexists. split; [do 3 right; left; reflexivity|].
match goal with |- ?lo <= ?x < ?hi => let vl := eval vm_compute in lo in let vh := eval vm_compute in hi in change (vl <= x < vh) end.
unfold RS_LO, src0_D_read_stage. lia.
Qed.
Section j.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variables (sp tid : word) (a0 path : list byte) (inp : ProcInput) (data : list byte) (rnd : EntryDraw).
Hypothesis Hlk : fs_lookup (in_fs inp) path = Some data.
Let L : Z := Z.of_nat (length data).
Let E9 : env := edset (E_main sp [a0; path] (in_envp inp) tid rnd) 2 data.
Hypothesis HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G.
Variable PRES : dleaf * astate -> Prop.
Definition E_lp (J : list word) (buf g len cap : Z) : env :=
ewset (ewset (ewset (ewset (havoc E9 29 J) 14 (Z_to_bv 64 buf)) 26 (Z_to_bv 64 g)) 27 (Z_to_bv 64 len)) 28 (Z_to_bv 64 cap).
Lemma ew_lp : forall J buf g len cap n,
ew (E_lp J buf g len cap) n =
if (n =? 28)%nat then Z_to_bv 64 cap else if (n =? 27)%nat then Z_to_bv 64 len
else if (n =? 26)%nat then Z_to_bv 64 g else if (n =? 14)%nat then Z_to_bv 64 buf
else if (n <? 29)%nat then ew E9 n else nth (n - 29) J (ew E9 n).
Proof. intros. unfold E_lp, ewset, havoc. cbn [ew]. reflexivity. Qed.
Lemma ed_lp : forall J buf g len cap, ed (E_lp J buf g len cap) = ed E9.
Proof. intros. reflexivity. Qed.
Lemma ed_lp2 : forall J buf g len cap, ed (E_lp J buf g len cap) 2 = data.
Proof. intros. rewrite ed_lp. unfold E9, edset. cbn. reflexivity. Qed.
Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.
Definition md_loop (md : Model) (off : Z) : Prop :=
fd_lookup (m_fds md) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 off)) /\
fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) md /\ fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md /\ m_fs md = in_fs inp /\
m_fds md = (Z_to_bv 64 3, FdFile path (Z_to_bv 64 off)) :: STDFDS.
Definition md_post (md : Model) : Prop :=
fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) md /\ fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md /\ m_fs md = in_fs inp /\
m_fds md = STDFDS.
Lemma md_loop_vm : forall md off vm, md_loop md off -> md_loop (with_vmmaps vm md) off.
Proof. intros md off vm (H1 & [H2 H2'] & [H3 H3'] & H4 & H5). unfold md_loop, fdchan. autorewrite with model. repeat split; assumption. Qed.
Lemma md_loop_ex : forall md md' off, md_loop md off -> (exists vm, md' = with_vmmaps vm md) -> md_loop md' off.
Proof. intros md md' off H [vm ->]. apply md_loop_vm. exact H. Qed.
Lemma md_loop_read : forall md off off' e,
md_loop md off -> e = FdFile path (Z_to_bv 64 off') ->
md_loop (with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) e) md) off'.
Proof.
intros md off off' e (H1 & [H2 H2'] & [H3 H3'] & H4 & H5) ->. unfold md_loop, fdchan. autorewrite with model.
rewrite fd_lookup_insert_eq. rewrite !fd_lookup_insert_neq by (intros H; apply (f_equal bv_unsigned) in H; discriminate).
repeat split; try assumption. rewrite H5. apply fd_insert3_std.
Qed.
Lemma md_loop_close : forall md off,
md_loop md off -> md_post (with_fds (fd_remove (m_fds md) (Z_to_bv 64 3)) md).
Proof.
intros md off (H1 & [H2 H2'] & [H3 H3'] & H4 & H5). unfold md_post, fdchan. autorewrite with model.
rewrite !fd_lookup_remove_neq by (intros H; apply (f_equal bv_unsigned) in H; discriminate).
repeat split; try assumption. rewrite H5. apply fd_remove3_std.
Qed.
Lemma win_not_static : forallb (fun r => (fst r + snd r <=? RS_LO) || (RS_LO + 65536 <=? fst r)) (static_ranges src0_msyms) = true
/\ ((ms_ctx src0_msyms + CTX_SIZE <=? RS_LO) || (RS_LO + 65536 <=? ms_ctx src0_msyms)) = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma win_not_owned : forall Lc A m md x, aa_MR API Lc A m md -> RS_LO <= x < RS_LO + 65536 -> ~ owned src0_msyms Lc A x.
Proof.
intros Lc A m md x HMR Hx [Ho|Ho].
- pose proof (read_stage_img (x - RS_LO) ltac:(lia)) as Himg. replace (RS_LO + (x - RS_LO)) with x in Himg by lia.
pose proof (ax_img AX Lc A m md x HMR Himg Ho) as Hc.
pose proof (proj2 win_not_static) as W. apply orb_prop in W as [W|W]; apply Z.leb_le in W; lia.
- destruct (static_owned_ranges src0_msyms x Ho) as (r & Hr & Hxr).
pose proof (forallb_In _ _ r (proj1 win_not_static) Hr) as W. cbn beta in W. apply orb_prop in W as [W|W]; apply Z.leb_le in W; lia.
Qed.
Lemma MR_win : forall Lc A (m m' : word -> option byte) md a (bs : list byte),
aa_MR API Lc A m md -> RS_LO <= a -> a + Z.of_nat (length bs) <= RS_LO + 65536 ->
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x -> m' x = m x) ->
m' = wbytes m (Z_to_bv 64 a) bs ->
aa_MR API Lc A m' md.
Proof.
intros Lc A m m' md a bs HMR Ha1 Ha2 Hfr ->.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & Hmat).
assert (Hrs : 0 <= RS_LO) by (unfold RS_LO, src0_D_read_stage; lia). pose proof YM05.alloc_ceiling_val as Hcv.
eapply (mr_frame _ _ (aa_laws API)); [exact HMR | | | | reflexivity | exact Hh | exact Hlz | exact Hmat].
- intros x Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ x HMR Ho) as Hxl.
unfold mbyte. rewrite Hfr; [reflexivity|]. rewrite u64_of_Z by lia.
destruct (Z_lt_dec x a) as [|Hge]; [lia|]. destruct (Z_lt_dec x (a + Z.of_nat (length bs))) as [Hlt|]; [|lia].
exfalso. exact (win_not_owned Lc A m md x HMR ltac:(lia) Ho).
- intros x Ho [b Hb]. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ x HMR Ho) as Hxl. exists b. rewrite Hfr; [exact Hb|]. rewrite u64_of_Z by lia.
destruct (Z_lt_dec x a) as [|Hge]; [lia|]. destruct (Z_lt_dec x (a + Z.of_nat (length bs))) as [Hlt|]; [|lia].
exfalso. exact (win_not_owned Lc A m md x HMR ltac:(lia) Ho).
- intros p n i Hp Hi. destruct (mr_blocks _ _ (aa_laws API) Lc A m md p n i HMR Hp Hi) as ([b Hb] & Hplo & Hphi & _).
exists b. rewrite Hfr; [exact Hb|]. rewrite u64_of_Z by lia.
destruct (Z_lt_dec (ptr_addr Lc p + i) a) as [|Hge]; [lia|]. destruct (Z_lt_dec (ptr_addr Lc p + i) (a + Z.of_nat (length bs))) as [Hlt|]; [|lia].
exfalso. apply (ax_blocks_img AX Lc A m md p n i HMR Hp Hi). replace (ptr_addr Lc p + i) with (RS_LO + (ptr_addr Lc p + i - RS_LO)) by lia.
apply read_stage_img. lia.
Qed.
Lemma blk_data_win : forall Lc A (m m' : word -> option byte) md p sz a (bs : list byte) c bs0,
aa_MR API Lc A m md -> In (p, sz) (user_blocks A) -> ptr_addr Lc p <= c -> c + Z.of_nat (length bs0) <= ptr_addr Lc p + sz ->
RS_LO <= a -> a + Z.of_nat (length bs) <= RS_LO + 65536 ->
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x -> m' x = m x) ->
blk_data src0_msyms m c bs0 -> blk_data src0_msyms m' c bs0.
Proof.
intros Lc A m m' md p sz a bs c bs0 HMR Hp Hc1 Hc2 Ha1 Ha2 Hfr HD i Hi. rewrite <- (HD i Hi).
destruct (mr_blocks _ _ (aa_laws API) Lc A m md p sz (c + i - ptr_addr Lc p) HMR Hp ltac:(lia)) as (_ & Hplo & Hphi & _).
pose proof YM05.alloc_ceiling_val as Hcv.
unfold mbyte. rewrite Hfr; [reflexivity|]. rewrite u64_of_Z by lia.
destruct (Z_lt_dec (c + i) a) as [|Hge]; [lia|]. destruct (Z_lt_dec (c + i) (a + Z.of_nat (length bs))) as [Hlt|]; [|lia].
exfalso. apply (ax_blocks_img AX Lc A m md p sz (c + i - ptr_addr Lc p) HMR Hp ltac:(lia)).
replace (ptr_addr Lc p + (c + i - ptr_addr Lc p)) with (RS_LO + (c + i - RS_LO)) by lia. apply read_stage_img. lia.
Qed.
Definition ext29 (E Ec : env) : Prop := (forall n, (n < 29)%nat -> ew Ec n = ew E n) /\ ed Ec = ed E.
Lemma ext29_refl : forall E, ext29 E E.
Proof. intros E. split; [intros; reflexivity | reflexivity]. Qed.
Lemma ext29_agree : forall E E1 E2 k, (29 <= k)%nat -> ext29 E E1 -> env_agree k E1 E2 -> ext29 E E2.
Proof. intros E E1 E2 k Hk [H1 H1'] [H2 H2']. split; [| congruence]. intros n Hn. rewrite H2 by lia. apply H1. exact Hn. Qed.
Lemma ext29_ewset : forall E Ec k v, (29 <= k)%nat -> ext29 E Ec -> ext29 E (ewset Ec k v).
Proof. intros E Ec k v Hk H. eapply ext29_agree; [exact Hk | exact H | apply env_agree_ewset]. Qed.
Lemma ext29_havoc : forall E Ec k ws, (29 <= k)%nat -> ext29 E Ec -> ext29 E (havoc Ec k ws).
Proof. intros E Ec k ws Hk H. eapply ext29_agree; [exact Hk | exact H | apply env_agree_havoc]. Qed.
Lemma ext29_post : forall E Ec k regs g, (29 <= k)%nat -> ext29 E Ec -> ext29 E (post_env Ec k regs g).
Proof. intros E Ec k regs g Hk H. eapply ext29_agree; [exact Hk | exact H | apply post_env_agree]. Qed.
Lemma anch_lp : forall J buf g len cap Ec G,
ext29 (E_lp J buf g len cap) Ec -> anchored_atoms G = anchored_atoms RD_facts -> stack_anchored Ec G.
Proof.
intros J buf g len cap Ec G [HX _] HG.
apply (stack_anchored_ext (E_main sp [a0; path] (in_envp inp) tid rnd) Ec RD_facts G (HSA0 RD_facts eq_refl) HG).
intros [n K] Hin. cbn [fst].
match type of Hin with In _ ?l => let v := eval vm_compute in l in change l with v in Hin end.
assert (Hn : (n < 10)%nat /\ n <> 14%nat).
{ cbn in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; split; [lia | discriminate] |]). destruct Hin. }
rewrite HX by lia. rewrite ew_lp.
destruct (Nat.eqb_spec n 28); [lia|]. destruct (Nat.eqb_spec n 27); [lia|]. destruct (Nat.eqb_spec n 26); [lia|].
destruct (Nat.eqb_spec n 14); [lia|]. destruct (Nat.ltb_spec n 29); [|lia]. reflexivity.
Qed.
Ltac drv_anch ::= first [ assumption | eapply anch_lp; [ eassumption | vm_compute; reflexivity ] ].
Section o.
Variables (J : list word) (buf g len cap : Z) (Ec : env).
Hypothesis HX : ext29 (E_lp J buf g len cap) Ec.
Hypothesis Hbuf : 0 <= buf < 2 ^ 62.
Hypothesis Hlen : 0 <= len <= cap.
Hypothesis Hcap : 0 < cap <= 2 ^ 26.
Lemma Ec14 : bv_unsigned (ew Ec 14) = buf.
Proof. rewrite (proj1 HX) by lia. rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. apply u64_of_Z. lia. Qed.
Lemma Ec27 : bv_unsigned (ew Ec 27) = len.
Proof. rewrite (proj1 HX) by lia. rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. apply u64_of_Z. lia. Qed.
Lemma Ec28 : bv_unsigned (ew Ec 28) = cap.
Proof. rewrite (proj1 HX) by lia. rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. apply u64_of_Z. lia. Qed.
Lemma Ec_ed2 : ed Ec 2 = data.
Proof. rewrite (proj2 HX). apply ed_lp2. Qed.
Lemma U_want : U Ec sv_want = cap - len.
Proof.
unfold sv_want, A_LEN, A_CAP. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, U_SLit, Ec27, Ec28, !Z.add_0_r.
rewrite (zcanon_id len), (zcanon_id cap) by (unfold M64; lia).
change (zcanon (-1)) with (M64 - 1).
replace (zcanon (len * (M64 - 1))) with (zcanon (- len)).
2:{ unfold zcanon. replace (len * (M64 - 1)) with (- len + len * M64) by lia. symmetry. apply Z_mod_plus_full. }
unfold zcanon, M64. rewrite Zplus_mod_idemp_l. replace (- len + cap) with (cap - len) by lia. apply Z.mod_small. lia.
Qed.
Lemma U_dst : U Ec (SAlu ALU_ADD (SOff A_BUF 0) (SOff A_LEN 0)) = buf + len.
Proof.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff. change A_BUF with 14%nat. change A_LEN with 27%nat. rewrite Ec14, Ec27, !Z.add_0_r.
rewrite (zcanon_id len), (zcanon_id buf) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.
Variable n : Z.
Hypothesis Hn : 0 <= n /\ len + n <= cap.
Hypothesis E47 : bv_unsigned (ew Ec 47) = n.
Lemma U_len1 : U Ec sv_len1 = len + n.
Proof.
unfold sv_len1. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff. change A_LEN with 27%nat. change A_N with 47%nat.
rewrite Ec27, E47, !Z.add_0_r. rewrite (zcanon_id len), (zcanon_id n) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_big : U Ec sv_big = Z.shiftr (len + n) 26.
Proof.
unfold sv_big. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (U Ec sv_len1) with (U Ec sv_len1). rewrite U_len1.
change (Z.land (zcanon 26) 63) with 26. rewrite ?(zcanon_id (len + n)) by (unfold M64; lia).
apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia. unfold M64. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; lia.
Qed.
Lemma U_dbl : U Ec (SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1))) = 2 * (len + n).
Proof.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit. change A_LEN with 27%nat. change A_N with 47%nat.
rewrite Ec27, E47, !Z.add_0_r. rewrite (zcanon_id len), (zcanon_id n) by (unfold M64; lia). change (Z.land (zcanon 1) 63) with 1.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (len * 2)), (zcanon_id (n * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End o.
Lemma agree_to_lp : forall (P : nat -> bool) J buf g len cap Ec J' buf' g' len' cap',
ext29 (E_lp J buf g len cap) Ec ->
(forall n, P n = true -> (n < 29)%nat /\ (n = 14%nat -> buf' = buf) /\ (n = 26%nat -> g' = g) /\ (n = 27%nat -> len' = len) /\ (n = 28%nat -> cap' = cap)) ->
env_agree_pd P PT Ec (E_lp J' buf' g' len' cap').
Proof.
intros P J buf g len cap Ec J' buf' g' len' cap' [HX HD] HP. split; [| intros d _; rewrite ed_lp, HD, ed_lp; reflexivity].
intros n Hn. destruct (HP n Hn) as (H29 & H14 & H26 & H27 & H28). rewrite HX by exact H29. rewrite !ew_lp.
destruct (Nat.eqb_spec n 28); [rewrite H28 by assumption; reflexivity|].
destruct (Nat.eqb_spec n 27); [rewrite H27 by assumption; reflexivity|].
destruct (Nat.eqb_spec n 26); [rewrite H26 by assumption; reflexivity|].
destruct (Nat.eqb_spec n 14); [rewrite H14 by assumption; reflexivity|].
destruct (Nat.ltb_spec n 29); [reflexivity | lia].
Qed.
Lemma lp_junk : forall rl buf g len cap regs k r,
length rl = 17%nat ->
nth_error rl (k - 29) = Some r -> (29 <= k)%nat ->
ew (E_lp (map (getr regs) rl) buf g len cap) k = getr regs r.
Proof.
intros rl buf g len cap regs k r Hlen Hr Hk. rewrite ew_lp.
assert (Hk46 : (k - 29 < length rl)%nat) by (apply nth_error_Some; congruence). rewrite Hlen in Hk46.
destruct (Nat.eqb_spec k 28); [lia|]. destruct (Nat.eqb_spec k 27); [lia|]. destruct (Nat.eqb_spec k 26); [lia|].
destruct (Nat.eqb_spec k 14); [lia|]. destruct (Nat.ltb_spec k 29); [lia|].
apply nth_error_nth. rewrite nth_error_map, Hr. reflexivity.
Qed.
Definition TREE (fuel : nat) (cap : Z) (bufp : sptr) (A : astate) : itree astate (dleaf * astate) :=
bind (read_phase fuel L cap bufp) (driver_tail data) A.
Definition POST (K : dleaf * astate -> TSet) : Prop :=
forall cap' bufp' A' Lc' J' g' len0 w ms' md',
L < cap' -> 65536 <= cap' <= MAX_INPUT -> 0 <= len0 <= L ->
user_blocks A' = [(bufp', cap')] -> WF A' -> bounded A' -> st_init_done A' = true ->
st_ok src0segs (ewset (E_lp J' (ptr_addr Lc' bufp') g' len0 cap') 46 (Z_to_bv 64 w)) S_HDR ms' -> 1 <= w <= 65536 ->
len0 = L ->
aa_MR API Lc' A' (ms_mem ms') md' -> md_post md' ->
blk_data src0_msyms (ms_mem ms') (ptr_addr Lc' bufp') data ->
jinv K (driver_tail data (RdLoaded bufp' cap') A') -> gtree mgrant (driver_tail data (RdLoaded bufp' cap') A') ->
leaves PRES (driver_tail data (RdLoaded bufp' cap') A') ->
realizes src0segs (mkCfg ms' md') (tset (driver_tail data (RdLoaded bufp' cap') A') K).
Lemma cap_range : forall fuel cap, cap = 2 ^ (27 - Z.of_nat fuel) -> (1 <= fuel <= 11)%nat -> 65536 <= cap <= 2 ^ 26 /\ cap mod 65536 = 0.
Proof.
intros fuel cap -> Hf. split.
- split; [change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia | apply Z.pow_le_mono_r; lia].
- change 65536 with (2 ^ 16). replace (27 - Z.of_nat fuel) with (16 + (11 - Z.of_nat fuel)) by lia.
rewrite Z.pow_add_r by lia. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma bv_off_add : forall off (bs : list byte),
0 <= off -> off + Z.of_nat (length bs) < 2 ^ 64 ->
(Z_to_bv 64 off + len_word bs)%bv = Z_to_bv 64 (off + Z.of_nat (length bs)).
Proof.
intros off bs H1 H2. apply bv_eq. unfold len_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by lia. reflexivity.
Qed.
Ltac carry E S HS HF HMR HD Hin len Hfl :=
lazymatch type of HD with blk_data _ _ ?a ?bs0 =>
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
let HD' := fresh "HD'" in
let HG0 := fresh "HG0" in let HSA1 := fresh "HSA1" in
assert (HG0 : facts_ok E (ss_facts S)) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X);
assert (HSA1 : stack_anchored E (ss_facts S)) by drv_anch;
pose proof (fun h1 h2 => blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX _ _ m0 m1 _ E (ss_facts S) src0_keep rs0 _ _ a bs0
HMR HG0 HSA1 ltac:(vm_compute; reflexivity) HF Hin h1 h2 HD) as HD';
specialize (HD' ltac:(lia) ltac:(rewrite (Hfl len); lia)); clear HD HG0 HSA1; rename HD' into HD
end end;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
Theorem loop_rd : forall N fuel cap bufp len A Lc J g ms md (K : dleaf * astate -> TSet),
(Z.to_nat (2 ^ 28 - len - cap) < N)%nat ->
cap = 2 ^ (27 - Z.of_nat fuel) -> (1 <= fuel <= 11)%nat ->
0 <= len < cap -> len <= L ->
user_blocks A = [(bufp, cap)] -> WF A -> bounded A -> st_init_done A = true ->
st_ok src0segs (E_lp J (ptr_addr Lc bufp) g len cap) S_RD ms ->
aa_MR API Lc A (ms_mem ms) md -> md_loop md len ->
blk_data src0_msyms (ms_mem ms) (ptr_addr Lc bufp) (firstn (Z.to_nat len) data) ->
jinv K (TREE fuel cap bufp A) -> gtree mgrant (TREE fuel cap bufp A) -> leaves PRES (TREE fuel cap bufp A) ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
POST K ->
realizes src0segs (mkCfg ms md) (tset (TREE fuel cap bufp A) K).
Proof.
induction N as [|N IHN]; [lia|].
intros fuel cap bufp len A Lc J g ms md K HN Hcap Hfuel Hlen HlenL Hub HW HB Hid HS HMR Hmd HD HJt HGt HLt HK HPOST.
destruct (cap_range fuel cap Hcap Hfuel) as [Hcr Hcm].
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp, cap) (user_blocks A)) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc A (ms_mem ms) md bufp cap 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
assert (Hb' : exists b, b = ptr_addr Lc bufp) by (eexists; reflexivity). destruct Hb' as [buf Hbuf]. rewrite <- Hbuf in *.
set (E := E_lp J buf g len cap) in HS.
assert (HX : ext29 (E_lp J buf g len cap) E) by apply ext29_refl.
assert (Hfl : forall k, 0 <= k <= L -> Z.of_nat (length (firstn (Z.to_nat k) data)) = k).
{ intros k Hk. rewrite firstn_length_le; unfold L in Hk; lia. }
assert (Hbufr : 0 <= buf < 2 ^ 62) by lia. assert (Hlenr : 0 <= len <= cap) by lia. assert (Hcapr : 0 < cap <= 2 ^ 26) by lia.
pose proof (U_want J buf g len cap E HX Hbufr Hlenr Hcapr) as HUw.
assert (Hch2 : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md) by exact (proj1 (proj2 (proj2 Hmd))).
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E S_W msx) in HS end.
carry E S_W HS HF HMR HD Hin len Hfl.
assert (REABS : forall w ms1 (S : sstate),
st_ok src0segs E S ms1 -> reabs_check P_W S RW_regs RW_facts = true -> ss_mem S = LH_mem -> ss_pc S = RWPC ->
sv_denot E (sr_get (ss_regs S) (R 12)) = Z_to_bv 64 w -> 1 <= w <= 65536 ->
st_ok src0segs (ewset E 46 (Z_to_bv 64 w)) S_RW ms1).
{ intros w ms1 S HS1 Hck HmS HpcS H12 Hw.
unfold S_RW. rewrite <- HpcS.
apply (st_ok_reabs src0segs P_W E (ewset E 46 (Z_to_bv 64 w)) S ms1 RW_regs LH_mem RW_facts HS1).
- split; [| intros; reflexivity]. intros k Hk. unfold P_W in Hk. apply ew_ewset_other. intros ->. rewrite Nat.eqb_refl in Hk. discriminate.
- exact Hck.
- apply obl_W. rewrite ew_ewset_same. rewrite (st_ok_reg src0segs _ _ _ (R 12) HS1), H12. reflexivity.
- rewrite fobl_W. constructor; [| constructor]. unfold afact_ok, fact_want. cbn [fst snd af_lo af_hi af_al2].
rewrite ew_ewset_same, u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
- destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & HM & _). rewrite HmS in HM.
eapply (mem_ok_agree_pd src0segs P_W PT E); [| | exact HM].
+ split; [| intros; reflexivity]. intros k Hk. unfold P_W in Hk. apply ew_ewset_other. intros ->. rewrite Nat.eqb_refl in Hk. discriminate.
+ vm_compute. reflexivity. }
assert (CONT : forall w ms1, 1 <= w <= 65536 -> w <= cap - len ->
st_ok src0segs (ewset E 46 (Z_to_bv 64 w)) S_RW ms1 ->
aa_MR API Lc A (ms_mem ms1) md ->
blk_data src0_msyms (ms_mem ms1) buf (firstn (Z.to_nat len) data) ->
realizes src0segs (mkCfg ms1 md) (tset (TREE fuel cap bufp A) K)).
2:{ destruct S_W_facts as (HpcW & H12a & H12b & HpcA & HpcB & HmA & HmB).
destruct (Z_lt_dec (cap - len) 65536) as [Hsmall | Hbig].
- sym_assume_with src0tbl_ok HS true.
{ rewrite branch_ltu_U, U_SLit.
match goal with |- (U E ?a <? _) = true => change (U E a) with (U E sv_want) end. rewrite HUw. apply Z.ltb_lt. change (zcanon 65536) with 65536. lia. }
drv_run_to_with src0tbl_ok HS RWPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E S_Wa msx) in HS end.
carry E S_Wa HS HF HMR HD Hin len Hfl.
lazymatch type of HS with st_ok _ _ _ ?msx =>
apply (CONT (cap - len) msx ltac:(lia) ltac:(lia)); [| exact HMR | exact HD] end.
apply (REABS (cap - len) _ S_Wa HS reabs_Wa HmA HpcA); [| lia].
change (sr_get (ss_regs S_Wa) (R 12)) with sv_want. rewrite (denot_lit_U E sv_want), HUw. reflexivity.
- sym_assume_with src0tbl_ok HS false.
{ rewrite branch_ltu_U, U_SLit.
match goal with |- (U E ?a <? _) = false => change (U E a) with (U E sv_want) end. rewrite HUw. apply Z.ltb_ge. change (zcanon 65536) with 65536. lia. }
drv_run_to_with src0tbl_ok HS RWPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E S_Wb msx) in HS end.
carry E S_Wb HS HF HMR HD Hin len Hfl.
lazymatch type of HS with st_ok _ _ _ ?msx =>
apply (CONT 65536 msx ltac:(lia) ltac:(lia)); [| exact HMR | exact HD] end.
apply (REABS 65536 _ S_Wb HS reabs_Wb HmB HpcB); [| lia].
change (sr_get (ss_regs S_Wb) (R 12)) with (SLit 65536). reflexivity. }
clear HS HMR HD ms.
intros w ms Hw Hwc HS HMR HD.
set (E1 := ewset E 46 (Z_to_bv 64 w)) in HS.
assert (HX1 : ext29 (E_lp J buf g len cap) E1) by (unfold E1; apply ext29_ewset; [lia | exact HX]).
assert (E46 : bv_unsigned (ew E1 46) = w) by (unfold E1; rewrite ew_ewset_same; apply u64_of_Z; lia).
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall src0segs E1 S_RE msx) in HS end.
carry E1 S_RE HS HF HMR HD Hin len Hfl.
destruct S_RE_facts as (Hpc1 & H17 & H10 & H11 & H12 & Hrv1).
eapply (rz_read_win src0segs E1 S_RE _ md (Z_to_bv 64 3) path (Z_to_bv 64 len) data _ RS_LO w _ Hh Hlz HS Hrv1).
- rewrite H17. reflexivity.
- rewrite H10. reflexivity.
- reflexivity.
- exact (proj1 Hmd).
- rewrite (proj1 (proj2 (proj2 (proj2 Hmd)))). exact Hlk.
- rewrite H11. vm_compute. reflexivity.
- rewrite H12. change (bv_unsigned (sv_denot E1 (SOff A_WANT 0))) with (U E1 (SOff 46 0)). rewrite U_SOff, E46, Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
- reflexivity.
- exact S_RE_dest.
- exact read_stage_seg.
- unfold RS_LO, src0_D_read_stage. lia.
- unfold RS_LO, src0_D_read_stage. lia.
- cbn [ms_mem pend_at] in HMR, HD |- *.
intros regs Hregs HG Hmem Hbytes Hfr Hnle.
lazymatch type of Hfr with context [wbytes ?m0 _ _] => remember m0 as mem eqn:Hmem_def in *; clear Hmem_def end.
set (bs := file_read data (Z_to_bv 64 len) (sv_denot E1 (sr_get (ss_regs S_RE) 12%bv))) in *.
assert (Hnlen : Z.of_nat (length bs) = Z.min w (L - len)).
{ subst bs. rewrite file_read_length. rewrite (denot_lit_U E1 (sr_get (ss_regs S_RE) 12%bv)), H12.
change (U E1 (SOff A_WANT 0)) with (U E1 (SOff 46 0)). rewrite U_SOff, E46, Z.add_0_r, zcanon_id by (unfold M64; lia).
rewrite !u64_of_Z by lia. unfold L. lia. }
assert (Hbs : bs = firstn (Z.to_nat w) (skipn (Z.to_nat len) data)).
{ subst bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite (denot_lit_U E1 (sr_get (ss_regs S_RE) 12%bv)), H12.
change (U E1 (SOff A_WANT 0)) with (U E1 (SOff 46 0)). rewrite U_SOff, E46, Z.add_0_r, zcanon_id by (unfold M64; lia).
rewrite !u64_of_Z by lia. reflexivity. }
pose proof (MR_win Lc A mem _ md RS_LO bs HMR ltac:(lia) ltac:(lia) Hfr eq_refl) as HMR1.
pose proof (blk_data_win Lc A mem _ md bufp cap RS_LO bs buf (firstn (Z.to_nat len) data) HMR Hin ltac:(lia) ltac:(rewrite (Hfl len); lia)
ltac:(lia) ltac:(lia) Hfr HD) as HD1.
clear HMR HD.
remember (Z.of_nat (length bs)) as n eqn:Hndef.
destruct (Z.eq_dec n 0) as [Hn0 | Hnpos].
+
assert (HLlen : len = L) by lia.
assert (Ebs : bs = []) by (destruct bs; [reflexivity | cbn in Hndef; lia]). rewrite Ebs in *. cbn [wbytes] in *.
assert (HS1 : st_ok src0segs E1 (resume S_RE (SLit 0) (ss_mem S_RE) (ss_facts S_RE))
(mkst (regupd regs 10%bv (len_word (@nil byte))) (v_addi (Z_to_bv 64 (ss_pc S_RE)) 4) mem (seg_rom src0segs))).
{ apply (st_ok_resume_sv src0segs E1 S_RE regs mem (SLit 0)); [exact Hregs | exact Hmem | exact HG | reflexivity]. }
clear Hregs HG Hmem HS. rename HS1 into HS.
match goal with |- realizes _ (mkCfg _ ?M) _ =>
assert (Hmd1 : md_loop M len) by (apply (md_loop_read md len len); [exact Hmd | f_equal; rewrite bv_off_add by (cbn; lia); cbn; rewrite Z.add_0_r; reflexivity]);
assert (Hh1 : m_halted M = None) by (autorewrite with model; exact Hh);
assert (Hlz1 : m_vm_lazy M = []) by (autorewrite with model; exact Hlz) end.
apply (MR_with_fds src0_msyms (aa_MR API) (aa_laws API)) with (f := fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 len + len_word (@nil byte))%bv)) in HMR1.
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall src0segs E1 S_CL msx) in HS end.
carry E1 S_CL HS HF HMR1 HD1 Hin len Hfl.
destruct S_CL_facts as (Hpc3 & H17c & H10c & Hrv3).
sym_ecall_open HS. cbn [ms_mem pend_at] in HMR1, HD1.
eapply (rz_close src0segs regs0 _ mem0 (seg_rom src0segs) _ (Z_to_bv 64 3));
[exact Hh1 | exact Hlz1
| rewrite (Hregs 17%bv), H17c; reflexivity | rewrite (Hregs 10%bv), H10c; reflexivity | reflexivity
| exact (proj1 Hmd1) |].
resume_sv src0segs (SLit 0). { reflexivity. }
change (resume _ _ _ _) with S_HDR in HS.
destruct fuel as [|f]; [lia|].
unfold TREE in HJt, HGt, HLt |- *. rewrite (bind_ext1 _ (ret (RdLoaded bufp cap)) (driver_tail data) A) in HJt, HGt, HLt |- * by (apply read_phase_loaded_eq; apply Z.ltb_lt; lia).
rewrite bind_ret_l in HJt, HGt, HLt |- *.
unfold E1 in HS. subst buf.
eapply (HPOST cap bufp A Lc J g len w _ _ ltac:(lia) ltac:(unfold MAX_INPUT; lia) ltac:(lia) Hub HW HB Hid HS Hw HLlen).
* exact (MR_with_fds src0_msyms (aa_MR API) (aa_laws API) _ _ _ _ _ HMR1).
* apply (md_loop_close _ len). exact Hmd1.
* rewrite HLlen in HD1. rewrite firstn_all2 in HD1 by (unfold L; lia). exact HD1.
* exact HJt.
* exact HGt.
* exact HLt.
+
assert (Hnp : 1 <= n <= w) by lia.
assert (HnL : len + n <= L /\ len + n <= cap) by lia.
assert (HS1 : st_ok src0segs (ewset E1 47 (len_word bs))
(resume S_RE (SOff 47 0) (ss_mem S_RE) (mkFacts ((47%nat, fact_n) :: f_atoms (ss_facts S_RE)) (f_conds (ss_facts S_RE)) (f_alias (ss_facts S_RE))))
(mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc S_RE)) 4) (wbytes mem (Z_to_bv 64 RS_LO) bs) (seg_rom src0segs))).
{ apply (st_ok_resume_atom src0segs 47 fact_n E1 S_RE regs _ (len_word bs) Hregs).
- exact Hmem.
- exact HG.
- exact (proj1 (proj2 (proj2 S_RDc_pd))).
- unfold fact_n, len_word; cbn [af_lo af_hi]. rewrite u64_of_Z by lia. lia.
- cbn. lia.
- unfold len_word. cbn [af_al2 fact_n]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
clear Hregs HG Hmem HS. rename HS1 into HS.
set (E2 := ewset E1 47 (len_word bs)) in HS.
assert (HX2 : ext29 (E_lp J buf g len cap) E2) by (unfold E2; apply ext29_ewset; [lia | exact HX1]).
assert (HmemW : mem_ok src0segs E2 (wbytes mem (Z_to_bv 64 RS_LO) bs) (ss_mem S_RE)) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _); exact HM).
assert (E47 : bv_unsigned (ew E2 47) = n) by (unfold E2; rewrite ew_ewset_same; unfold len_word; rewrite u64_of_Z by lia; lia).
match goal with |- realizes _ (mkCfg _ ?M) _ =>
assert (Hmd1 : md_loop M (len + n)) by (apply (md_loop_read md len (len + n)); [exact Hmd | f_equal; rewrite Hndef; apply bv_off_add; lia]);
assert (Hh1 : m_halted M = None) by (autorewrite with model; exact Hh);
assert (Hlz1 : m_vm_lazy M = []) by (autorewrite with model; exact Hlz);
apply (MR_with_fds src0_msyms (aa_MR API) (aa_laws API)) with (f := m_fds M) in HMR1; cbn [m_fds with_fds] in HMR1 || idtac end.
match goal with |- realizes _ (mkCfg _ ?M) _ => change (aa_MR API Lc A (wbytes mem (Z_to_bv 64 RS_LO) bs) M) in HMR1 || idtac end.
drv_run_to_with src0tbl_ok HS src0_A_memcpy HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E2 S_CP msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
assert (Hwin : forall i, 0 <= i < n -> mbyte src0segs m1 (RS_LO + i) = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite <- (Hbytes i ltac:(lia));
apply (mbyte_win_after_frame src0segs E2 m0 m1 rs0 RS_LO 65536 HmemW S_RE_dest HF); unfold RS_LO, src0_D_read_stage in *; lia | ] end.
carry E2 S_CP HS HF HMR1 HD1 Hin len Hfl.
destruct S_CP_facts as (HpcC & HraC & H10C & H11C & H12C & HrvC & HmC).
lazymatch type of HS with st_ok _ _ _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11; pose proof (st_ok_reg src0segs _ _ _ 12%bv HS) as Hr12;
rewrite H10C in Hr10; rewrite H11C in Hr11; rewrite H12C in Hr12;
eapply (src0_memcpy_from_abs API AX E2 S_CP msx _ Lc A bufp cap (buf + len) RS_LO n bs A_BUF K_CP RA_CP _ HS ltac:(drv_anch) ltac:(vm_compute; reflexivity) HMR1 Hin);
[ change A_BUF with 14%nat; rewrite (Ec14 J buf g len cap E2 HX2 Hbufr); exact Hbuf
| rewrite Hr10, (denot_lit_U E2), (U_dst J buf g len cap E2 HX2 Hbufr Hlenr Hcapr); reflexivity
| lia | lia
| rewrite Hr11; reflexivity
| unfold RS_LO, src0_D_read_stage; lia
| unfold RS_LO, src0_D_read_stage; lia
| intros i Hi; apply read_stage_img; lia
| exact Hwin
| lia
| rewrite Hr12, (denot_lit_U E2); change (U E2 (SOff A_N 0)) with (U E2 (SOff 47 0)); rewrite U_SOff, E47, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity
| lia
| clear Hr10 Hr11 Hr12 ] end.
intros mq3 HS3 HMR3 Hout3 Hbd3.
assert (HD3 : blk_data src0_msyms (ms_mem mq3) buf (firstn (Z.to_nat (len + n)) data)).
{ intros i Hi. change (ms_segs src0_msyms) with src0segs. rewrite firstn_length_le in Hi by (unfold L in *; lia).
destruct (Z_lt_dec i len) as [Hlt | Hge].
- rewrite (nth_error_firstn (Z.to_nat (len + n)) data). destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) (Z.to_nat (len + n))); [|lia].
transitivity (nth_error (firstn (Z.to_nat len) data) (Z.to_nat i)).
+ rewrite <- (HD1 i) by (rewrite firstn_length_le; unfold L in *; lia). unfold mbyte. rewrite Hout3 by lia. reflexivity.
+ rewrite (nth_error_firstn (Z.to_nat len) data). destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) (Z.to_nat len)); [reflexivity | lia].
- replace (buf + i) with (buf + len + (i - len)) by lia. rewrite (Hbd3 (i - len)) by lia.
rewrite Hbs. rewrite (nth_error_firstn (Z.to_nat w)), nth_error_skipn, (nth_error_firstn _ data).
replace (Z.to_nat len + Z.to_nat (i - len))%nat with (Z.to_nat i) by lia.
destruct (PeanoNat.Nat.ltb_spec (Z.to_nat (i - len)) (Z.to_nat w)); destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) (Z.to_nat (len + n))); try reflexivity; try lia. }
clear HS HMR1 Hout3 Hbd3 HD1 Hwin.
lazymatch type of HS3 with st_ok _ ?Ec _ ?msx => set (E3 := Ec) in HS3; change (st_ok src0segs E3 S_CPp msx) in HS3 end.
assert (HX3 : ext29 (E_lp J buf g len cap) E3) by (unfold E3; apply ext29_havoc; [unfold K_CP; lia | exact HX2]).
assert (E47' : bv_unsigned (ew E3 47) = n) by (unfold E3; rewrite ew_havoc_old by (unfold K_CP; lia); exact E47).
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR3) as (Hh3 & Hlz3 & _).
rename mq3 into ms3. rename HS3 into HS. rename HMR3 into HMR. rename HD3 into HD.
match type of HMR with aa_MR _ _ _ _ ?M => rename Hmd1 into Hmd'; assert (Hmd1 : md_loop M (len + n)) by exact Hmd'; clear Hmd' end.
assert (Hch2' : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) _) by exact (proj1 (proj2 (proj2 Hmd1))).
pose proof (U_len1 J buf g len cap E3 HX3 Hbufr Hlenr Hcapr n ltac:(lia) E47') as HUl1.
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_T msx) in HS end.
carry E3 S_T HS HF HMR HD Hin (len + n) Hfl.
destruct (Z.eq_dec (len + n) cap) as [Heq | Hne].
*
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_eq_U. match goal with |- (U E3 ?a =? U E3 ?b) = true => change (U E3 a) with (U E3 sv_len1); change (U E3 b) with (U E3 (SOff 28 0)) end.
rewrite HUl1, U_SOff, (Ec28 J buf g len cap E3 HX3 Hbufr Hcapr), Z.add_0_r, zcanon_id by (unfold M64; lia). rewrite Heq. apply Z.eqb_refl. }
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_G msx) in HS end.
carry E3 S_G HS HF HMR HD Hin (len + n) Hfl.
pose proof (U_big J buf g len cap E3 HX3 Hbufr Hlenr Hcapr n ltac:(lia) E47') as HUbig.
destruct fuel as [|f]; [lia|].
destruct (Z.eq_dec cap (2 ^ 26)) as [Hmax | Hnmax].
--
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_ne_U, U_SLit. match goal with |- negb (U E3 ?a =? _) = true => change (U E3 a) with (U E3 sv_big) end.
rewrite HUbig, Heq, Hmax. reflexivity. }
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_RF msx) in HS end.
unfold TREE. rewrite (bind_ext1 _ (ret RdRefused) (driver_tail data) A) by (apply read_phase_refused_eq; [apply Z.ltb_ge; lia | apply Z.leb_le; unfold MAX_INPUT; lia]).
rewrite bind_ret_l. change (tset (driver_tail data RdRefused A) K) with (K (DL_refused, A)).
apply (rz_conseq _ _ (diag msg_refused (in_fs inp)) _); [| apply t_eq_sym; apply HK].
unfold diag, wr, ex. rewrite <- (proj1 (proj2 (proj2 (proj2 Hmd1)))).
lazymatch type of HS with st_ok _ _ _ ?msx =>
exact (realizes_diag_exit_by_run E3 S_RF msx _ (Z_to_bv 64 2) K_MG msg_refused 2 2 HS Hh3 Hlz3 ltac:(lia) refused_check Hch2') end.
--
assert (Hf1 : (1 <= f)%nat).
{ destruct f; [| lia]. exfalso. apply Hnmax. rewrite Hcap. reflexivity. }
assert (Hcap2 : 2 * cap = 2 ^ (27 - Z.of_nat f)).
{ rewrite Hcap. replace (27 - Z.of_nat f) with (Z.succ (27 - Z.of_nat (S f))) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
assert (H2cap : 2 * cap <= 2 ^ 26) by (rewrite Hcap2; apply Z.pow_le_mono_r; lia).
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_ne_U, U_SLit. match goal with |- negb (U E3 ?a =? _) = false => change (U E3 a) with (U E3 sv_big) end.
rewrite HUbig, Heq, Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
drv_run_to_with src0tbl_ok HS src0_A_malloc HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_MG msx) in HS end.
carry E3 S_MG HS HF HMR HD Hin (len + n) Hfl.
unfold TREE in HJt, HGt, HLt |- *.
rewrite (bind_ext1 _ _ (driver_tail data) A (read_phase_grow_eq f L cap bufp ltac:(apply Z.ltb_ge; lia) ltac:(apply Z.leb_gt; unfold MAX_INPUT; lia))) in HJt, HGt, HLt |- *.
apply jinv_bind_assoc in HJt. apply gtree_bind_assoc in HGt. apply leaves_bind_assoc in HLt.
apply (rz_conseq _ _ (tset (bind (malloc (2 * cap)) (fun p => bind (grow_k f L cap bufp p) (driver_tail data)) A) K)); [| apply t_eq_sym; apply tset_bind_assoc].
rewrite tset_mbind'.
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10.
rewrite (proj1 S_MG_facts) in Hr10.
rewrite (denot_lit_U E3), (U_dbl J buf g len cap E3 HX3 Hbufr Hlenr Hcapr n ltac:(lia) E47') in Hr10.
lazymatch type of HS with st_ok _ _ _ ?msx =>
eapply (malloc_site src0_msyms API AX E3 S_MG msx _ Lc A (2 * cap) MAIN_SP src0_keep [] K_MG L_MG RS_MG RA_MG _ HS ltac:(drv_anch) site_MG statics_MG HMR HW HB);
[ intros Hf'; rewrite Hid in Hf'; discriminate
| rewrite Hr10, Heq; reflexivity
| lia
| intros kb sz [ ]
| exact (jinv_mbind_head _ _ _ _ HJt)
| exact (gtree_mbind_head _ _ _ _ HGt)
| ] end.
intros res A2 L2 mq2 md2 g2 tr HS2 HSA2 HMR2 HW2 HB2 [vm2 Hmd2] Hpath Hstab Hhi Hbk Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _).
assert (Hid2 : st_init_done A2 = true) by (exact (malloc_keeps_init_done _ _ _ _ _ Hid (cpath_yields _ _ _ Hpath))).
assert (Hmdl2 : md_loop md2 (len + n)) by (subst md2; apply md_loop_vm; exact Hmd1).
assert (Hch2'' : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md2) by exact (proj1 (proj2 (proj2 Hmdl2))).
destruct (Hstab _ _ Hin) as [Hin2 Hpb2]. rewrite <- Hbuf in Hpb2.
assert (HD2 : blk_data src0_msyms (ms_mem mq2) buf (firstn (Z.to_nat (len + n)) data)).
{ eapply (blk_data_kept src0_msyms); [| exact HD]. intros i Hi. rewrite Hbuf. apply (Hbk bufp cap i Hin). rewrite (Hfl (len + n)) in Hi by lia. lia. }
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs (post_env E3 K_MG (ms_regs mq2) g2) S_MGp msx) in HS2 end.
set (E4 := post_env E3 K_MG (ms_regs mq2) g2) in HS2, HSA2.
assert (HX4 : ext29 (E_lp J buf g len cap) E4) by (unfold E4; apply ext29_post; [unfold K_MG; lia | exact HX3]).
assert (E47'' : bv_unsigned (ew E4 47) = n) by (unfold E4; rewrite (proj1 (post_env_agree E3 K_MG _ _)) by (unfold K_MG; lia); exact E47').
pose proof (jinv_mbind_after K _ _ A tr res A2 HJt Hpath) as HJ2. pose proof (gtree_mbind_after mgrant _ _ A tr res A2 HGt Hpath) as HG2. pose proof (leaves_mbind_after PRES _ _ A tr res A2 HLt Hpath) as HL2.
clear HS HMR Hhi Hr10 HJt HGt HLt. cbn beta iota. cbn beta in HJ2, HG2, HL2.
destruct res as [nb|].
++
destruct Hres as (Hq0 & Hqnz & b1 & b2 & HubA2 & HubA).
assert (Hinb : In (nb, 2 * cap) (user_blocks A2)) by (rewrite HubA2; apply in_app_iff; right; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L2 A2 (ms_mem mq2) md2 nb (2 * cap) 0 HMR2 Hinb ltac:(lia)) as (_ & Hn1 & Hn2 & _).
pose proof (mr_blocks_aligned _ _ (aa_laws API) L2 A2 (ms_mem mq2) md2 nb _ HMR2 Hinb) as Hnal.
assert (Hnbp : nb <> bufp).
{ intros ->. pose proof (blocks_same_ptr _ _ (aa_laws API) _ _ _ _ _ _ _ _ HMR2 Hinb Hin2 ltac:(lia) ltac:(lia) eq_refl). lia. }
unfold grow_k in HJ2, HG2, HL2 |- *.
apply jinv_bind_assoc in HJ2. apply gtree_bind_assoc in HG2. apply leaves_bind_assoc in HL2.
apply (rz_conseq _ _ (tset (bind (free (Some bufp)) (fun u => bind ((fun _ : unit => read_phase f L (2 * cap) nb) u) (driver_tail data)) A2) K)); [| apply t_eq_sym; apply tset_bind_assoc].
rewrite tset_mbind'.
assert (H63 : bv_unsigned (ew E4 63) = ptr_addr L2 nb).
{ unfold E4. change 63%nat with (K_MG + 4)%nat. rewrite post_env_a0, Hq0. apply u64_of_Z. lia. }
apply (st_ok_add_fact src0segs _ S_MGp mq2 A_NB blkq_fact) in HS2.
2:{ unfold afact_ok, blkq_fact. cbn [af_lo af_hi af_al2]. change A_NB with 63%nat. rewrite H63. change (2 ^ 4) with 16.
pose proof YM05.alloc_ceiling_val. lia. }
drv_run_to_with src0tbl_ok HS2 src0_A_memcpy HF.
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs E4 S_MC msx) in HS2 end.
carry E4 S_MC HS2 HF HMR2 HD2 Hin2 (len + n) Hfl.
lazymatch type of HS2 with st_ok _ _ _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS2) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS2) as Hr11; pose proof (st_ok_reg src0segs _ _ _ 12%bv HS2) as Hr12;
rewrite (proj1 S_MC_facts) in Hr10; rewrite (proj1 (proj2 S_MC_facts)) in Hr11; rewrite (proj2 (proj2 S_MC_facts)) in Hr12;
eapply (src0_memcpy_site API AX E4 S_MC msx md2 L2 A2 nb (2 * cap) (len + n) bufp cap buf A_NB K_MC RA_MC1 _ HS2 ltac:(drv_anch) ck_MC HMR2 Hinb Hin2 Hnbp);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r; change A_NB with 63%nat; rewrite <- H63, Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11, (denot_lit_U E4), U_SOff; change A_BUF with 14%nat; rewrite (Ec14 J buf g len cap E4 HX4 Hbufr), Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity
| rewrite Hpb2; lia
| rewrite Hpb2; lia
| rewrite Hr12, (denot_lit_U E4), (U_len1 J buf g len cap E4 HX4 Hbufr Hlenr Hcapr n ltac:(lia) E47''); reflexivity
| lia | lia
| clear Hr10 Hr11 Hr12 ] end.
intros mq5 HS5 HMR5 Hout5 Hbd5.
assert (HD5 : blk_data src0_msyms (ms_mem mq5) (ptr_addr L2 nb) (firstn (Z.to_nat (len + n)) data)) by (apply Hbd5; [exact HD2 | rewrite (Hfl (len + n)); lia]).
clear HS2 HMR2 Hout5 Hbd5 HD2.
lazymatch type of HS5 with st_ok _ ?Ec _ ?msx => set (E5 := Ec) in HS5; change (st_ok src0segs E5 S_MCp msx) in HS5 end.
assert (HX5 : ext29 (E_lp J buf g len cap) E5) by (unfold E5; apply ext29_havoc; [unfold K_MC; lia | exact HX4]).
assert (H63' : bv_unsigned (ew E5 63) = ptr_addr L2 nb) by (unfold E5; rewrite ew_havoc_old by (unfold K_MC; lia); exact H63).
assert (E47_5 : bv_unsigned (ew E5 47) = n) by (unfold E5; rewrite ew_havoc_old by (unfold K_MC; lia); exact E47'').
drv_run_to_with src0tbl_ok HS5 src0_A_free HF.
lazymatch type of HS5 with st_ok _ _ _ ?msx => change (st_ok src0segs E5 S_FR msx) in HS5 end.
carry E5 S_FR HS5 HF HMR5 HD5 Hinb (len + n) Hfl.
lazymatch type of HS5 with st_ok _ _ _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS5) as Hr10; rewrite S_FR_facts in Hr10;
eapply (free_site_tset src0_msyms API AX E5 S_FR msx md2 L2 A2 bufp cap MAIN_SP src0_keep [] K_FR L_FR RS_FR RA_FR _
HS5 ltac:(drv_anch) site_FR statics_FR HMR5 HW2 HB2 Hid2 Hin2);
[ rewrite Hr10, (denot_lit_U E5), U_SOff; change A_BUF with 14%nat; rewrite (Ec14 J buf g len cap E5 HX5 Hbufr), Z.add_0_r, zcanon_id by (unfold M64; lia); rewrite Hpb2; reflexivity
| intros kb sz [ ]
| exact (jinv_mbind_head _ _ _ _ HJ2)
| exact (gtree_mbind_head _ _ _ _ HG2)
| clear Hr10 ] end.
intros A3 L3 mq6 md6 g6 tr6 HS6 HSA6 HMR6 HW6 HB6 [vm6 Hmd6] Hpath6 (l1 & l2 & HubA2' & HubA3) Hstab6 Hhi6 Hbk6.
cbn beta iota. change (bind (read_phase f L (2 * cap) nb) (driver_tail data) A3) with (TREE f (2 * cap) nb A3).
pose proof (jinv_mbind_after K _ _ A2 tr6 tt A3 HJ2 Hpath6) as HJ3. pose proof (gtree_mbind_after mgrant _ _ A2 tr6 tt A3 HG2 Hpath6) as HG3. pose proof (leaves_mbind_after PRES _ _ A2 tr6 tt A3 HL2 Hpath6) as HL3.
cbn beta in HJ3, HG3, HL3. change (bind (read_phase f L (2 * cap) nb) (driver_tail data) A3) with (TREE f (2 * cap) nb A3) in HJ3, HG3, HL3.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR6) as (Hh6 & Hlz6 & _).
assert (Hub3 : user_blocks A3 = [(nb, 2 * cap)]).
{ apply (blocks_after_grow b1 b2 l1 l2 bufp nb cap (user_blocks A2)); [exact HubA2 | rewrite <- Hub; exact HubA | exact HubA2' | exact HubA3 | lia]. }
destruct (Hstab6 nb (2 * cap) Hinb Hnbp) as [Hinb3 Hpnb3].
assert (Hid3 : st_init_done A3 = true) by (exact (free_keeps_init_done _ _ _ _ _ Hid2 (cpath_yields _ _ _ Hpath6))).
assert (Hmdl6 : md_loop md6 (len + n)) by (subst md6; apply md_loop_vm; exact Hmdl2).
assert (HD6 : blk_data src0_msyms (ms_mem mq6) (ptr_addr L2 nb) (firstn (Z.to_nat (len + n)) data)).
{ eapply (blk_data_kept src0_msyms); [| exact HD5]. intros i Hi. apply (Hbk6 nb (2 * cap) i Hinb Hnbp). rewrite (Hfl (len + n)) in Hi by lia. lia. }
clear HS5 HMR5 Hhi6 Hbk6 HD5.
lazymatch type of HS6 with st_ok _ ?Ec _ ?msx => set (E6 := Ec) in HS6, HSA6; change (st_ok src0segs E6 S_RD' msx) in HS6 end.
assert (HX6 : ext29 (E_lp J buf g len cap) E6) by (unfold E6; apply ext29_post; [unfold K_FR; lia | exact HX5]).
assert (H63'' : bv_unsigned (ew E6 63) = ptr_addr L2 nb) by (unfold E6; rewrite (proj1 (post_env_agree E5 K_FR _ _)) by (unfold K_FR; lia); exact H63').
assert (E47_6 : bv_unsigned (ew E6 47) = n) by (unfold E6; rewrite (proj1 (post_env_agree E5 K_FR _ _)) by (unfold K_FR; lia); exact E47_5).
lazymatch type of HS6 with st_ok _ _ _ ?msx =>
set (J' := map (getr (ms_regs msx)) Jregs);
assert (HSc : st_ok src0segs (E_lp J' (ptr_addr L3 nb) g (len + n) (2 * cap)) S_RDc msx);
[ unfold S_RDc; rewrite <- (proj1 S_RD'_facts);
apply (st_ok_reabs src0segs P_GR E6 (E_lp J' (ptr_addr L3 nb) g (len + n) (2 * cap)) S_RD' msx RD_regs (map snd LH_cut) RD_facts HS6) | ] end.
** apply (agree_to_lp P_GR J buf g len cap E6); [exact HX6|].
intros k Hk. unfold P_GR, P_junk in Hk. repeat (apply andb_prop in Hk as [Hk ?X]). apply Nat.ltb_lt in Hk.
destruct (Nat.eqb_spec k 14); [discriminate|]. destruct (Nat.eqb_spec k 26); [discriminate|]. destruct (Nat.eqb_spec k 27); [discriminate|]. destruct (Nat.eqb_spec k 28); [discriminate|].
repeat split; intros; lia || congruence.
** exact reabs_RD'.
** apply obl_RD.
+++ intros k r Hr Hk. apply (lp_junk Jregs); [reflexivity | exact Hr | exact Hk].
+++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 9) HS6). change (sr_get (ss_regs S_RD') (R 9)) with (SOff 63 0).
cbn [sv_denot]. rewrite Z.add_0_r. rewrite Hpnb3, <- H63'', Z_to_bv_bv_unsigned. reflexivity.
+++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 19) HS6). change (sr_get (ss_regs S_RD') (R 19)) with sv_len1.
rewrite (denot_lit_U E6), (U_len1 J buf g len cap E6 HX6 Hbufr Hlenr Hcapr n ltac:(lia) E47_6). reflexivity.
+++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 21) HS6).
change (sr_get (ss_regs S_RD') (R 21)) with (SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1))).
rewrite (denot_lit_U E6), (U_dbl J buf g len cap E6 HX6 Hbufr Hlenr Hcapr n ltac:(lia) E47_6), Heq. reflexivity.
** rewrite fobl_RD. constructor; [| constructor; [| constructor; [| constructor]]]; unfold afact_ok, fact_len, fact_cap; cbn [fst snd af_lo af_hi af_al2]; rewrite ew_lp; cbn [Nat.eqb Nat.ltb Nat.leb].
+++ rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
+++ rewrite u64_of_Z by lia. change (2 ^ 16) with 65536. split; [lia|]. split; [| lia].
replace (2 * cap) with (cap + cap) by lia. rewrite Z.add_mod, Hcm by lia. reflexivity.
+++ rewrite u64_of_Z by lia. rewrite Hpnb3. change (2 ^ 4) with 16. pose proof YM05.alloc_ceiling_val. repeat split; lia.
** destruct HS6 as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (mem_ok_relayout src0segs) with (l := back (map snd LH_cut)) in HM; [| exact relayout_RD']. rewrite back_cut in HM.
eapply (mem_ok_agree_pd src0segs P_GR PT E6); [| exact (proj1 LH_mem_atoms) | exact HM].
apply (agree_to_lp P_GR J buf g len cap E6); [exact HX6|].
intros k Hk. unfold P_GR, P_junk in Hk. repeat (apply andb_prop in Hk as [Hk ?X]). apply Nat.ltb_lt in Hk.
destruct (Nat.eqb_spec k 14); [discriminate|]. destruct (Nat.eqb_spec k 26); [discriminate|]. destruct (Nat.eqb_spec k 27); [discriminate|]. destruct (Nat.eqb_spec k 28); [discriminate|].
repeat split; intros; lia || congruence.
**
pose proof LH_statics as Hadd. unfold drv_add_statics in Hadd.
destruct (abs_region_index (map snd LH_cut) (ms_got_guard src0_msyms) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd LH_cut) (ms_libc src0_msyms + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd LH_cut) (ms_guard src0_msyms) 0) as [i3|]; [|discriminate].
lazymatch type of HSc with st_ok _ _ _ ?msx =>
destruct (st_ok_statics_pd src0_msyms (aa_MR API) AX _ S_RDc msx L3 A3 md6 G_M1 i1 i2 i3 LH_mem HSc HMR6 (proj1 S_RDc_pd) Hadd) as (g' & Hg' & HS7);
change (st_ok src0segs (ewset (E_lp J' (ptr_addr L3 nb) g (len + n) (2 * cap)) 26 (Z_to_bv 64 g')) S_RD msx) in HS7;
assert (HS8 : st_ok src0segs (E_lp J' (ptr_addr L3 nb) g' (len + n) (2 * cap)) S_RD msx);
[ apply (st_ok_agree_pd src0segs PT PT _ _ S_RD msx HS7); [| exact (proj1 (proj2 S_RDc_pd))];
split; [| intros; reflexivity]; intros k _;
destruct (Nat.eqb_spec k 26) as [->|Hk26]; [rewrite ew_lp, ew_ewset_same; reflexivity|];
rewrite (ew_ewset_other _ _ _ _ Hk26), !ew_lp, (proj2 (Nat.eqb_neq _ _) Hk26); reflexivity | ] end.
clear HSc HS7 HS6.
lazymatch type of HS8 with st_ok _ _ _ ?msx =>
refine (IHN f (2 * cap) nb (len + n) A3 L3 J' g' msx md6 K ltac:(lia) Hcap2 ltac:(lia) ltac:(lia) ltac:(lia) Hub3 HW6 HB6 Hid3 HS8 HMR6 Hmdl6 _ HJ3 HG3 HL3 HK HPOST);
rewrite Hpnb3; exact HD6 end.
++
destruct Hres as [Hq0 HubA2].
unfold grow_k. rewrite bind_ret_l. change (tset (driver_tail data RdOOM A2) K) with (K (DL_oom, A2)).
apply (rz_conseq _ _ (diag msg_oom (in_fs inp)) _); [| apply t_eq_sym; apply HK].
apply (st_ok_regs src0segs _ _ mq2 (sr_set (ss_regs S_MGp) 10%bv (SLit 0))) in HS2.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. rewrite (proj2 S_MG_facts).
cbn [sv_denot]. rewrite Z.add_0_r. unfold E4. change A_NB with (K_MG + 4)%nat. rewrite post_env_a0, Hq0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs E4 S_MGn msx) in HS2 end.
unfold diag, wr, ex. rewrite <- (proj1 (proj2 (proj2 (proj2 Hmdl2)))).
lazymatch type of HS2 with st_ok _ _ _ ?msx =>
exact (realizes_diag_exit_by_run E4 S_MGn msx md2 (Z_to_bv 64 2) K_MC msg_oom 2 2 HS2 Hh2 Hlz2 ltac:(lia) oom_check Hch2'') end.
*
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_eq_U. match goal with |- (U E3 ?a =? U E3 ?b) = false => change (U E3 a) with (U E3 sv_len1); change (U E3 b) with (U E3 (SOff 28 0)) end.
rewrite HUl1, U_SOff, (Ec28 J buf g len cap E3 HX3 Hbufr Hcapr), Z.add_0_r, zcanon_id by (unfold M64; lia). apply Z.eqb_neq. exact Hne. }
drv_run_to_with src0tbl_ok HS RDPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_RDn msx) in HS end.
carry E3 S_RDn HS HF HMR HD Hin (len + n) Hfl.
lazymatch type of HS with st_ok _ _ _ ?msx =>
set (J' := map (getr (ms_regs msx)) Jregs);
assert (HS' : st_ok src0segs (E_lp J' buf g (len + n) cap) S_RD msx);
[ unfold S_RD; rewrite <- (proj1 S_RDn_facts);
apply (st_ok_reabs src0segs P_RDLH E3 (E_lp J' buf g (len + n) cap) S_RDn msx RD_regs LH_mem RD_facts HS) | ] end.
-- apply (agree_to_lp P_RDLH J buf g len cap E3); [exact HX3|].
intros k Hk. unfold P_RDLH, P_junk in Hk. apply andb_prop in Hk as [Hk1 Hk2]. apply Nat.ltb_lt in Hk1.
destruct (Nat.eqb_spec k 27); [discriminate|]. repeat split; intros; lia || congruence.
-- exact reabs_RDn.
-- apply obl_RDn.
++ intros k r Hr Hk. apply (lp_junk Jregs); [reflexivity | exact Hr | exact Hk].
++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 19) HS). change (sr_get (ss_regs S_RDn) (R 19)) with sv_len1.
rewrite (denot_lit_U E3), HUl1. reflexivity.
-- rewrite fobl_RDn. constructor; [| constructor]. unfold afact_ok, fact_len. cbn [fst snd af_lo af_hi af_al2].
rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
-- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (mem_ok_relayout src0segs) with (l := back LH_mem) in HM; [| exact relayout_RDn]. rewrite back_LH_mem in HM.
eapply (mem_ok_agree_pd src0segs P_RDLH PT E3); [| exact (proj1 (proj2 (proj2 (proj2 LH_mem_atoms)))) | exact HM].
apply (agree_to_lp P_RDLH J buf g len cap E3); [exact HX3|].
intros k Hk. unfold P_RDLH, P_junk in Hk. apply andb_prop in Hk as [Hk1 Hk2]. apply Nat.ltb_lt in Hk1.
destruct (Nat.eqb_spec k 27); [discriminate|]. repeat split; intros; lia || congruence.
-- clear HS. subst E. subst buf.
lazymatch type of HS' with st_ok _ _ _ ?msx =>
apply (IHN fuel cap bufp (len + n) A Lc J' g msx _ K ltac:(lia) Hcap Hfuel ltac:(lia) ltac:(lia) Hub HW HB Hid HS' HMR Hmd1 HD HJt HGt HLt HK HPOST) end.
Qed.
Theorem src0_read_loop : forall (brk mbase : word) (lim : Z) regs' g ms md Lc A bufp vm (K : dleaf * astate -> TSet),
st_ok src0segs (E_m1 sp tid [a0; path] (in_envp inp) rnd regs' g) ss_m1_post ms ->
getr regs' 10%bv = Z_to_bv 64 (ptr_addr Lc bufp) ->
aa_MR API Lc A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
user_blocks A = [(bufp, CAP0)] ->
md = with_vmmaps vm (MD_file path tid brk mbase sp lim inp) ->
jinv K (TREE READ_FUEL CAP0 bufp A) -> gtree mgrant (TREE READ_FUEL CAP0 bufp A) -> leaves PRES (TREE READ_FUEL CAP0 bufp A) ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
POST K ->
realizes src0segs (mkCfg ms md) (tset (TREE READ_FUEL CAP0 bufp A) K).
Proof.
intros brk mbase lim regs' g ms md Lc A bufp vm K HS Ha0 HMR HW HB Hid Hub Hmd HJ HG HL HK HPOST.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp, CAP0) (user_blocks A)) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc A (ms_mem ms) md bufp CAP0 0 HMR Hin ltac:(unfold CAP0; lia)) as (_ & Hq1 & Hq2 & _).
pose proof (mr_blocks_aligned _ _ (aa_laws API) Lc A (ms_mem ms) md bufp CAP0 HMR Hin) as Hqal.
unfold CAP0 in Hq2. assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
set (E0 := E_m1 sp tid [a0; path] (in_envp inp) rnd regs' g) in HS.
assert (E14 : ew E0 14 = Z_to_bv 64 (ptr_addr Lc bufp)).
{ unfold E0, E_m1. change 14%nat with (K_M1 + 4)%nat. rewrite post_env_a0. exact Ha0. }
assert (HSAE0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored E0 G).
{ intros G HGa. apply (stack_anchored_ext (E_main sp [a0; path] (in_envp inp) tid rnd) E0 RD_facts G (HSA0 RD_facts eq_refl) HGa).
intros [n K0] Hn. cbn [fst].
match type of Hn with In _ ?l => let v := eval vm_compute in l in change l with v in Hn end.
assert (Hn10 : (n < 10)%nat).
{ cbn in Hn. repeat (destruct Hn as [Hn|Hn]; [injection Hn as <- <-; lia |]). destruct Hn. }
unfold E0, E_m1. apply (proj1 (post_env_agree _ K_M1 _ _)). unfold K_M1. lia. }
apply (st_ok_add_fact src0segs E0 ss_m1_post ms A_BUF blk_fact) in HS.
2:{ unfold afact_ok, blk_fact. cbn [af_lo af_hi af_al2]. change A_BUF with 14%nat. rewrite E14, u64_of_Z by lia. change (2 ^ 4) with 16.
pose proof YM05.alloc_ceiling_val. lia. }
change (add_atom ss_m1_post A_BUF blk_fact) with ss_m1_ok in HS.
drv_run_to_with src0tbl_ok HS RDPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E0 X0 msx) in HS end.
assert (HSAX : stack_anchored E0 (ss_facts X0)) by (apply HSAE0; vm_compute; reflexivity).
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E0 HS HF HMR.
apply (st_ok_edset src0segs E0 2 data) in HS; [| vm_compute; reflexivity].
lazymatch type of HS with st_ok _ _ _ ?msx =>
set (J := map (getr (ms_regs msx)) Jregs);
assert (HS' : st_ok src0segs (E_lp J (ptr_addr Lc bufp) g 0 65536) S_RD msx);
[ unfold S_RD; change RDPC with (ss_pc X0);
apply (st_ok_reabs src0segs P_X0 (edset E0 2 data) (E_lp J (ptr_addr Lc bufp) g 0 65536) X0 msx RD_regs LH_mem RD_facts HS) | ] end.
- split; [| intros d _; reflexivity].
intros n Hn. unfold P_X0 in Hn. rewrite ew_lp.
apply orb_prop in Hn as [Hn|Hn]; [apply orb_prop in Hn as [Hn|Hn]|].
+ apply Nat.ltb_lt in Hn. destruct (Nat.eqb_spec n 28); [lia|]. destruct (Nat.eqb_spec n 27); [lia|]. destruct (Nat.eqb_spec n 26); [lia|].
destruct (Nat.eqb_spec n 14); [lia|]. destruct (Nat.ltb_spec n 29); [|lia].
unfold E9, E0, E_m1, post_env, edset. cbn [ew]. rewrite ew_ewset_other by (unfold K_M1; lia). rewrite !ew_havoc_old by (unfold K_M1; lia). reflexivity.
+ apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset. cbn [ew]. rewrite E14. reflexivity.
+ apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset, E0, E_m1, post_env. cbn [ew]. change 26%nat with (K_M1 + 16)%nat. rewrite ew_ewset_same. reflexivity.
- exact reabs_X0.
- apply obl_X0.
+ intros k r Hr Hk. apply (lp_junk Jregs); [reflexivity | exact Hr | exact Hk].
+ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 19) HS). reflexivity.
+ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 21) HS). reflexivity.
- rewrite fobl_X0. constructor; [| constructor; [| constructor]]; unfold afact_ok, fact_len, fact_cap; cbn [fst snd af_lo af_hi af_al2]; rewrite ew_lp; cbn [Nat.eqb Nat.ltb Nat.leb].
+ rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
+ rewrite u64_of_Z by lia. repeat split; try lia; try reflexivity.
- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (mem_ok_relayout src0segs) with (l := back LH_mem) in HM; [| exact relayout_X0]. rewrite back_LH_mem in HM.
eapply (mem_ok_agree_pd src0segs P_X0 PT (edset E0 2 data)); [| | exact HM].
+ split; [| intros d _; reflexivity].
intros n Hn. unfold P_X0 in Hn. rewrite ew_lp.
apply orb_prop in Hn as [Hn|Hn]; [apply orb_prop in Hn as [Hn|Hn]|].
* apply Nat.ltb_lt in Hn. destruct (Nat.eqb_spec n 28); [lia|]. destruct (Nat.eqb_spec n 27); [lia|]. destruct (Nat.eqb_spec n 26); [lia|].
destruct (Nat.eqb_spec n 14); [lia|]. destruct (Nat.ltb_spec n 29); [|lia].
unfold E9, E0, E_m1, post_env, edset. cbn [ew]. rewrite ew_ewset_other by (unfold K_M1; lia). rewrite !ew_havoc_old by (unfold K_M1; lia). reflexivity.
* apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset. cbn [ew]. rewrite E14. reflexivity.
* apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset, E0, E_m1, post_env. cbn [ew]. change 26%nat with (K_M1 + 16)%nat. rewrite ew_ewset_same. reflexivity.
+ vm_compute. reflexivity.
- clear HS.
lazymatch type of HS' with st_ok _ _ _ ?msx =>
apply (loop_rd (S (Z.to_nat (2 ^ 28))) READ_FUEL CAP0 bufp 0 A Lc J g msx md K ltac:(unfold CAP0; lia) eq_refl ltac:(unfold READ_FUEL; lia)
ltac:(unfold CAP0; lia) ltac:(unfold L; lia) Hub HW HB Hid HS' HMR) end.
+ subst md. unfold md_loop, MD_file, fdchan. autorewrite with model. rewrite MD0_fds, MD0_fs.
rewrite fd_lookup_insert_eq, !fd_lookup_insert_neq by (intros H'; apply (f_equal bv_unsigned) in H'; discriminate).
repeat split; first [apply fd_insert_std3 | reflexivity].
+ cbn. apply (blk_data_nil src0_msyms).
+ exact HJ.
+ exact HG.
+ exact HL.
+ exact HK.
+ exact HPOST.
Qed.
End j.
End h.
