(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPcV.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* printf_core walks: the values of the symbolic registers the walks meet, and dropping the GOT cell's region. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPc0 FMsnprintfPcA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sv_lit : forall E v c, sv_eqb v (SLit c) = true -> sv_denot E v = w64 c.
Proof. intros E v c H. apply sv_eqb_eq in H. subst v. reflexivity. Qed.
Lemma sv_atom : forall E v j c a, sv_eqb v (SOff j c) = true -> bv_unsigned (ew E j) = a -> sv_denot E v = w64 (a + c).
Proof. intros E v j c a H Ha. apply sv_eqb_eq in H. subst v. cbn [sv_denot]. rewrite Ha. reflexivity. Qed.
Lemma sv_atom0 : forall E v j a, sv_eqb v (SOff j 0) = true -> bv_unsigned (ew E j) = a -> sv_denot E v = w64 a.
Proof. intros E v j a H Ha. apply sv_eqb_eq in H. subst v. cbn [sv_denot]. rewrite Ha, Z.add_0_r. reflexivity. Qed.
Lemma w64_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> w64 x = w64 y.
Proof. intros x y H. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H. Qed.
Lemma sv_add2 : forall E v i j a b, sv_eqb v (SAlu ALU_ADD (SOff i 0) (SOff j 0)) = true ->
  bv_unsigned (ew E i) = a -> bv_unsigned (ew E j) = b -> sv_denot E v = w64 (a + b).
Proof.
intros E v i j a b H Ha Hb. apply sv_eqb_eq in H. subst v. cbn [sv_denot]. rewrite Ha, Hb, !Z.add_0_r.
rewrite zalu64_sound. apply w64_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw]. rewrite Zmod_mod. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma swrap64_small : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_swrap 64 x = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma lts_false : forall x y, 0 <= y <= x -> x < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y H1 H2. unfold bv_lts. rewrite !Z_to_bv_signed, !swrap64_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma lts_false_mod : forall x y x' y', x mod 2 ^ 64 = x' -> y mod 2 ^ 64 = y' -> 0 <= y' <= x' -> x' < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y x' y' Hx Hy H1 H2.
assert (E1 : Z_to_bv 64 x = Z_to_bv 64 x') by (apply (w64_mod x x'); rewrite <- Hx, Zmod_mod; reflexivity).
assert (E2 : Z_to_bv 64 y = Z_to_bv 64 y') by (apply (w64_mod y y'); rewrite <- Hy, Zmod_mod; reflexivity).
rewrite E1, E2. apply lts_false; lia.
Qed.
(* the first %.*s-format branch: `if (w > INT_MAX - cnt) goto overflow` before the second %s, BC_LT (0 - (k + c)) l *)
Lemma br_sub : forall E a b i j c k l, sv_eqb a (SAlu ALU_SUB (SLit 0) (SOff i c)) = true -> sv_eqb b (SOff j 0) = true ->
  bv_unsigned (ew E i) = k -> bv_unsigned (ew E j) = l -> 0 <= l <= - (k + c) -> - (k + c) < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = false.
Proof.
intros E a b i j c k l Ha Hb Hk Hl H1 H2. apply sv_eqb_eq in Ha. apply sv_eqb_eq in Hb. subst a b.
cbn [sv_denot branch_taken]. rewrite Hk, Hl, Z.add_0_r. rewrite zalu64_sound. unfold zalu64, zcanon, M64. cbn [zalu_raw].
apply (lts_false_mod _ _ (- (k + c)) l).
- rewrite Zmod_mod, Zmod_0_l, Zminus_mod_idemp_r, Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. reflexivity.
- lia.
- exact H2.
Qed.
Lemma swrap32_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma zalu32_add_small : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 31 -> zalu32 ALU_ADD a b = a + b.
Proof.
intros a b Ha Hb Hab. unfold zalu32, zu32, M32, zcanon, M64. cbn [zalu_raw].
rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.
Lemma zalu32_sub_small : forall a b, 0 <= b <= a -> a < 2 ^ 31 -> zalu32 ALU_SUB a b = a - b.
Proof.
intros a b Hb Ha. unfold zalu32, zu32, M32, zcanon, M64. cbn [zalu_raw].
rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.
(* the second %.*s-format branch: `if (z-a > INT_MAX-cnt) goto overflow` at the last literal run *)
Lemma br_subw : forall E a b i j c d k l (L : Z), sv_eqb a (SAluw ALU_SUB (SLit L) (SAluw ALU_ADD (SOff j 0) (SOff i c))) = true ->
  sv_eqb b (SLit d) = true -> bv_unsigned (ew E i) = k -> bv_unsigned (ew E j) = l -> 0 <= k -> 0 <= l -> 0 <= c -> 0 <= d ->
  l + k + c + d <= L -> L < 2 ^ 31 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = false.
Proof.
intros E a b i j c d k l L Ha Hb Hk Hl H1 H2 H3 H4 H5 H6. apply sv_eqb_eq in Ha. apply sv_eqb_eq in Hb. subst a b.
cbn [sv_denot branch_taken]. rewrite Hk, Hl, Z.add_0_r. rewrite zalu32_sound, zalu32_add_small by lia.
rewrite zalu32_sound, zalu32_sub_small by lia. apply lts_false; lia.
Qed.
(* the return value of the %.*s formats: 0 + (d + (l + (k + c))) in 32-bit adds *)
Lemma sv_retw : forall E v i j c d k l, sv_eqb v (SAlu ALU_ADD (SAluw ALU_ADD (SLit d) (SAluw ALU_ADD (SOff j 0) (SOff i c))) (SLit 0)) = true ->
  bv_unsigned (ew E i) = k -> bv_unsigned (ew E j) = l -> 0 <= k -> 0 <= l -> 0 <= c -> 0 <= d -> d + l + k + c < 2 ^ 31 ->
  sv_denot E v = w64 (d + l + k + c).
Proof.
intros E v i j c d k l Hv Hk Hl H1 H2 H3 H4 H5. apply sv_eqb_eq in Hv. subst v.
cbn [sv_denot]. rewrite Hk, Hl, Z.add_0_r. rewrite zalu32_sound, zalu32_add_small by lia.
rewrite zalu32_sound, zalu32_add_small by lia. rewrite zalu64_sound. apply w64_mod.
unfold zalu64, zcanon, M64. cbn [zalu_raw]. rewrite Zmod_mod, Zmod_0_l, Z.add_0_r, Zmod_mod. f_equal. lia.
Qed.
(* dropping the last region keeps st_ok *)
Lemma regions_wf_removelast : forall rs, regions_wf rs = true -> regions_wf (removelast rs) = true.
Proof.
induction rs as [|r rs IH]; intros H; [reflexivity|]. cbn [regions_wf] in H. apply andb_prop in H as [H1 H2].
destruct rs as [|r' rs']; [reflexivity|]. cbn [removelast]. cbn [regions_wf]. rewrite H1. cbn. apply IH. exact H2.
Qed.
Lemma Forall_removelast : forall (A : Type) (P : A -> Prop) l, Forall P l -> Forall P (removelast l).
Proof.
intros A P l. induction l as [|x l IH]; intros H; [constructor|].
destruct l as [|y l']; [constructor|]. cbn [removelast]. inversion H; subst. constructor; [assumption|]. apply IH. assumption.
Qed.
Lemma all_disjoint_removelast : forall E r rs, all_disjoint E r rs -> all_disjoint E r (removelast rs).
Proof.
intros E r rs. induction rs as [|x rs IH]; intros H; [exact I|].
destruct rs as [|y rs']; [exact I|]. cbn [removelast]. destruct H as [H1 H2]. split; [exact H1|]. apply IH. exact H2.
Qed.
Lemma pairwise_disjoint_removelast : forall E rs, pairwise_disjoint E rs -> pairwise_disjoint E (removelast rs).
Proof.
intros E rs. induction rs as [|r rs IH]; intros H; [exact I|].
destruct rs as [|y rs']; [exact I|]. cbn [removelast]. destruct H as [H1 H2].
split; [exact (all_disjoint_removelast E r _ H1)|]. apply IH. exact H2.
Qed.
Lemma st_ok_drop : forall E ss ms, st_ok tfibsegs E ss ms -> st_ok tfibsegs E (pc_drop ss) ms.
Proof.
intros E ss ms HS. destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9).
unfold st_ok, pc_drop. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [apply regions_wf_removelast; exact Hwf|].
split; [apply Forall_removelast; exact Hok | apply pairwise_disjoint_removelast; exact Hpd].
Qed.
End v.
